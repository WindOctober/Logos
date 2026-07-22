#!/usr/bin/env python3
"""Fail-closed SQLSolver DDL constraint materialization.

SQLSolver learns integrity constraints only from the schema DDL passed to its
frontend.  Benchmark pair constraints and WeTune sidecars therefore have to be
rendered into that DDL before a non-equivalence result can be interpreted under
the benchmark contract.  This module edits only normalized ``CREATE TABLE``
statements and accepts the constraint forms SQLSolver actually reasons about:
``NOT NULL``, primary/unique keys, and foreign keys.

Every referenced table and column is resolved against the emitted schema.  An
unknown, ambiguous, malformed, or conflicting declaration raises instead of
silently weakening the contract.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import re
from typing import Any, Iterable

from materializer_sql import (
    find_matching_paren,
    find_next_unquoted,
    split_sql_statements,
    split_top_level_commas,
)


class SqlsolverSchemaConstraintError(ValueError):
    """Raised when an authoritative constraint cannot be emitted exactly."""


@dataclass(frozen=True)
class ConstraintSpec:
    kind: str
    table: str
    columns: tuple[str, ...]
    referenced_table: str | None = None
    referenced_columns: tuple[str, ...] = ()
    source: str = "benchmark"

    def as_report(self) -> dict[str, Any]:
        report: dict[str, Any] = {
            "kind": self.kind,
            "table": self.table,
            "columns": list(self.columns),
            "source": self.source,
        }
        if self.referenced_table is not None:
            report["referencedTable"] = self.referenced_table
            report["referencedColumns"] = list(self.referenced_columns)
        return report


@dataclass
class _TableStatement:
    statement: str
    table_name: str
    table_token: str
    open_paren: int
    close_paren: int
    items: list[str]
    columns: dict[str, tuple[str, int]]
    column_types: dict[str, str]
    not_null_columns: set[str]
    primary_keys: set[tuple[str, ...]]
    unique_keys: set[tuple[str, ...]]
    foreign_keys: set[tuple[tuple[str, ...], str, tuple[str, ...]]]

    def render(self) -> str:
        body = ",\n  ".join(item.strip() for item in self.items)
        return (
            self.statement[: self.open_paren + 1]
            + ("\n  " + body + "\n" if body else "")
            + self.statement[self.close_paren :]
        )


_IDENTIFIER = r'(?:`(?:``|[^`])+`|"(?:""|[^"])+"|[A-Za-z_][A-Za-z0-9_$]*)'
_QUALIFIED_IDENTIFIER = rf"{_IDENTIFIER}(?:\s*\.\s*{_IDENTIFIER})*"
_CREATE_TABLE = re.compile(
    rf"^\s*CREATE\s+TABLE(?:\s+IF\s+NOT\s+EXISTS)?\s+"
    rf"(?P<table>{_QUALIFIED_IDENTIFIER})",
    re.IGNORECASE | re.DOTALL,
)
_COLUMN = re.compile(rf"^\s*(?P<column>{_IDENTIFIER})(?:\s+|$)", re.DOTALL)
_TABLE_CONSTRAINT = re.compile(
    r"^\s*(?:CONSTRAINT\s+" + _IDENTIFIER + r"\s+)?"
    r"(?P<kind>PRIMARY\s+KEY|UNIQUE(?:\s+(?:KEY|INDEX))?|FOREIGN\s+KEY)\b",
    re.IGNORECASE | re.DOTALL,
)


def materialize_pair_constraints(
    schema_sql: str,
    constraints: list[dict[str, Any]] | None,
) -> tuple[str, dict[str, Any]]:
    """Render the pair-constraint JSON vocabulary into SQLSolver DDL."""

    raw_constraints = [] if constraints is None else constraints
    if not isinstance(raw_constraints, list):
        raise SqlsolverSchemaConstraintError("pair constraints must be a list or null")

    tables = _parse_schema(schema_sql)
    specs: list[ConstraintSpec] = []
    for index, raw in enumerate(raw_constraints):
        if not isinstance(raw, dict) or len(raw) != 1:
            raise SqlsolverSchemaConstraintError(
                f"pair constraint {index} must be a singleton object"
            )
        kind, payload = next(iter(raw.items()))
        if kind == "not_null":
            table, column = _resolve_pair_value(
                _constraint_value(payload, f"pair constraint {index}"), tables
            )
            specs.append(
                ConstraintSpec("not_null", table, (column,), source="pair_metadata")
            )
        elif kind in {"primary", "unique"}:
            if not isinstance(payload, list) or not payload:
                raise SqlsolverSchemaConstraintError(
                    f"pair constraint {index} {kind} payload must be a nonempty list"
                )
            resolved = [
                _resolve_pair_value(
                    _constraint_value(value, f"pair constraint {index}"), tables
                )
                for value in payload
            ]
            table_names = {table for table, _ in resolved}
            if len(table_names) != 1:
                raise SqlsolverSchemaConstraintError(
                    f"pair constraint {index} {kind} spans multiple tables"
                )
            specs.append(
                ConstraintSpec(
                    "primary_key" if kind == "primary" else "unique",
                    resolved[0][0],
                    tuple(column for _, column in resolved),
                    source="pair_metadata",
                )
            )
        elif kind == "foreign":
            if not isinstance(payload, list) or len(payload) != 2:
                raise SqlsolverSchemaConstraintError(
                    f"pair constraint {index} foreign payload must have two endpoints"
                )
            source_table, source_column = _resolve_pair_value(
                _constraint_value(payload[0], f"pair constraint {index}"), tables
            )
            target_table, target_column = _resolve_pair_value(
                _constraint_value(payload[1], f"pair constraint {index}"), tables
            )
            specs.append(
                ConstraintSpec(
                    "foreign_key",
                    source_table,
                    (source_column,),
                    referenced_table=target_table,
                    referenced_columns=(target_column,),
                    source="pair_metadata",
                )
            )
        else:
            raise SqlsolverSchemaConstraintError(
                f"pair constraint {index} has unsupported kind {kind!r}"
            )

    materialized, report = materialize_schema_constraints(
        schema_sql,
        specs,
        authority="pair_metadata",
    )
    report["sourceConstraintCount"] = len(raw_constraints)
    report["ddlComplete"] = True
    report["residualConstraints"] = []
    return materialized, report


def materialize_schema_constraints(
    schema_sql: str,
    specs: Iterable[ConstraintSpec],
    *,
    authority: str,
) -> tuple[str, dict[str, Any]]:
    """Apply normalized constraint specs to normalized ``CREATE TABLE`` DDL."""

    tables = _parse_schema(schema_sql)
    by_name = {_key(table.table_name): table for table in tables}
    if len(by_name) != len(tables):
        raise SqlsolverSchemaConstraintError("schema contains duplicate table names")

    expanded_specs: list[ConstraintSpec] = []
    for spec in specs:
        if spec.kind == "primary_key":
            expanded_specs.extend(
                ConstraintSpec(
                    "not_null",
                    spec.table,
                    (column,),
                    source=f"{spec.source}:primary-key-implied-not-null",
                )
                for column in spec.columns
            )
        expanded_specs.append(spec)
    expanded_specs.sort(
        key=lambda spec: {
            "not_null": 0,
            "primary_key": 1,
            "unique": 1,
            "foreign_key": 2,
        }.get(spec.kind, 99)
    )

    applied: list[dict[str, Any]] = []
    already_present: list[dict[str, Any]] = []
    seen_specs: set[ConstraintSpec] = set()
    for spec in expanded_specs:
        if spec in seen_specs:
            continue
        seen_specs.add(spec)
        table = _resolve_table(by_name, spec.table)
        columns = tuple(_resolve_column(table, column) for column in spec.columns)
        normalized_columns = tuple(_key(column) for column in columns)
        if len(set(normalized_columns)) != len(normalized_columns):
            raise SqlsolverSchemaConstraintError(
                f"{spec.kind} on {table.table_name!r} repeats a column"
            )
        report = spec.as_report()

        if spec.kind == "not_null":
            if len(columns) != 1:
                raise SqlsolverSchemaConstraintError("NOT NULL requires one column")
            _, item_index = table.columns[_key(columns[0])]
            item = table.items[item_index]
            if re.search(r"\bNOT\s+NULL\b", item, re.IGNORECASE):
                already_present.append(report)
            else:
                table.items[item_index] = item.rstrip() + " NOT NULL"
                table.not_null_columns.add(_key(columns[0]))
                applied.append(report)
        elif spec.kind in {"primary_key", "unique"}:
            if not columns:
                raise SqlsolverSchemaConstraintError(
                    f"{spec.kind} requires at least one column"
                )
            existing = (
                table.primary_keys if spec.kind == "primary_key" else table.unique_keys
            )
            if spec.kind == "unique" and any(
                column not in table.not_null_columns for column in normalized_columns
            ):
                raise SqlsolverSchemaConstraintError(
                    f"nullable UNIQUE key on {table.table_name} cannot be emitted "
                    "into SQLSolver's total-key model"
                )
            if normalized_columns in existing:
                already_present.append(report)
            else:
                if spec.kind == "primary_key" and table.primary_keys:
                    raise SqlsolverSchemaConstraintError(
                        f"table {table.table_name!r} already has a different primary key"
                    )
                keyword = "PRIMARY KEY" if spec.kind == "primary_key" else "UNIQUE"
                table.items.append(
                    f"{keyword} ({', '.join(_column_token(table, column) for column in columns)})"
                )
                existing.add(normalized_columns)
                applied.append(report)
        elif spec.kind == "foreign_key":
            if (
                not columns
                or spec.referenced_table is None
                or len(columns) != len(spec.referenced_columns)
            ):
                raise SqlsolverSchemaConstraintError(
                    "foreign key endpoints must be nonempty and have equal arity"
                )
            referenced = _resolve_table(by_name, spec.referenced_table)
            referenced_columns = tuple(
                _resolve_column(referenced, column)
                for column in spec.referenced_columns
            )
            if len({_key(column) for column in referenced_columns}) != len(
                referenced_columns
            ):
                raise SqlsolverSchemaConstraintError(
                    f"foreign key target on {referenced.table_name!r} repeats a column"
                )
            signature = (
                normalized_columns,
                _key(referenced.table_name),
                tuple(_key(column) for column in referenced_columns),
            )
            referenced_key = tuple(_key(column) for column in referenced_columns)
            if (
                referenced_key not in referenced.primary_keys
                and referenced_key not in referenced.unique_keys
            ):
                raise SqlsolverSchemaConstraintError(
                    f"foreign key target {referenced.table_name}{referenced_columns!r} "
                    "is not an emitted primary/non-null unique key"
                )
            for source_column, referenced_column in zip(columns, referenced_columns):
                source_type = table.column_types[_key(source_column)]
                referenced_type = referenced.column_types[_key(referenced_column)]
                if not _constraint_types_compatible(source_type, referenced_type):
                    raise SqlsolverSchemaConstraintError(
                        f"foreign key type mismatch: {table.table_name}.{source_column} "
                        f"is {source_type}, but {referenced.table_name}.{referenced_column} "
                        f"is {referenced_type}"
                    )
            if signature in table.foreign_keys:
                already_present.append(report)
            else:
                table.items.append(
                    "FOREIGN KEY ("
                    + ", ".join(_column_token(table, column) for column in columns)
                    + ") REFERENCES "
                    + referenced.table_token
                    + " ("
                    + ", ".join(
                        _column_token(referenced, column)
                        for column in referenced_columns
                    )
                    + ")"
                )
                table.foreign_keys.add(signature)
                applied.append(report)
        else:
            raise SqlsolverSchemaConstraintError(
                f"unsupported SQLSolver constraint kind {spec.kind!r}"
            )

    _validate_existing_constraints(tables, by_name)
    rendered = ";\n\n".join(table.render().rstrip() for table in tables) + ";\n"
    return rendered, {
        "authority": authority,
        "inputSchemaSha256": _sha256(schema_sql),
        "materializedSchemaSha256": _sha256(rendered),
        "constraintCount": len(seen_specs),
        "appliedCount": len(applied),
        "alreadyPresentCount": len(already_present),
        "applied": applied,
        "alreadyPresent": already_present,
    }


def _validate_existing_constraints(
    tables: list[_TableStatement],
    by_name: dict[str, _TableStatement],
) -> None:
    """Reject unsafe constraint syntax that was already present in the DDL."""

    for table in tables:
        if len(table.primary_keys) > 1:
            raise SqlsolverSchemaConstraintError(
                f"table {table.table_name!r} contains multiple primary keys"
            )
        for key in table.primary_keys | table.unique_keys:
            if len(set(key)) != len(key):
                raise SqlsolverSchemaConstraintError(
                    f"key on table {table.table_name!r} repeats a column"
                )
            for column in key:
                if column not in table.columns:
                    raise SqlsolverSchemaConstraintError(
                        f"key on table {table.table_name!r} references missing "
                        f"column {column!r}"
                    )
        for primary in table.primary_keys:
            table.not_null_columns.update(primary)
        for unique in table.unique_keys:
            if any(column not in table.not_null_columns for column in unique):
                raise SqlsolverSchemaConstraintError(
                    f"nullable UNIQUE key on {table.table_name} cannot be emitted "
                    "into SQLSolver's total-key model"
                )

    for table in tables:
        for source_columns, target_table_name, target_columns in table.foreign_keys:
            if (
                len(source_columns) != len(target_columns)
                or not source_columns
                or len(set(source_columns)) != len(source_columns)
                or len(set(target_columns)) != len(target_columns)
            ):
                raise SqlsolverSchemaConstraintError(
                    f"foreign key on {table.table_name!r} has malformed endpoints"
                )
            target = by_name.get(target_table_name)
            if target is None:
                raise SqlsolverSchemaConstraintError(
                    f"foreign key on {table.table_name!r} references missing "
                    f"table {target_table_name!r}"
                )
            if any(column not in table.columns for column in source_columns) or any(
                column not in target.columns for column in target_columns
            ):
                raise SqlsolverSchemaConstraintError(
                    f"foreign key on {table.table_name!r} references a missing column"
                )
            if (
                target_columns not in target.primary_keys
                and target_columns not in target.unique_keys
            ):
                raise SqlsolverSchemaConstraintError(
                    f"foreign key target {target.table_name}{target_columns!r} is "
                    "not an emitted primary/non-null unique key"
                )
            for source_column, target_column in zip(source_columns, target_columns):
                if not _constraint_types_compatible(
                    table.column_types[source_column],
                    target.column_types[target_column],
                ):
                    raise SqlsolverSchemaConstraintError(
                        f"foreign key type mismatch: {table.table_name}."
                        f"{source_column} is {table.column_types[source_column]}, but "
                        f"{target.table_name}.{target_column} is "
                        f"{target.column_types[target_column]}"
                    )


def _parse_schema(schema_sql: str) -> list[_TableStatement]:
    statements = split_sql_statements(schema_sql)
    if not statements:
        raise SqlsolverSchemaConstraintError("schema has no CREATE TABLE statements")
    tables = [_parse_table_statement(statement) for statement in statements]
    return tables


def _parse_table_statement(statement: str) -> _TableStatement:
    match = _CREATE_TABLE.match(statement)
    if match is None:
        raise SqlsolverSchemaConstraintError(
            "SQLSolver constraint materialization accepts CREATE TABLE statements only"
        )
    open_paren = find_next_unquoted(statement, "(", match.end())
    close_paren = find_matching_paren(statement, open_paren)
    if open_paren < 0 or close_paren < 0:
        raise SqlsolverSchemaConstraintError("malformed CREATE TABLE statement")
    if statement[close_paren + 1 :].strip() and not re.fullmatch(
        r"(?is)(?:ENGINE|COMMENT|DEFAULT|CHARACTER|COLLATE|ROW_FORMAT).*",
        statement[close_paren + 1 :].strip(),
    ):
        raise SqlsolverSchemaConstraintError(
            "unrecognized CREATE TABLE suffix during constraint materialization"
        )

    table_token = match.group("table").strip()
    table_name = _unquote_identifier(re.split(r"\s*\.\s*", table_token)[-1])
    items = [
        item.strip()
        for item in split_top_level_commas(statement[open_paren + 1 : close_paren])
    ]
    columns: dict[str, tuple[str, int]] = {}
    column_types: dict[str, str] = {}
    not_null_columns: set[str] = set()
    primary_keys: set[tuple[str, ...]] = set()
    unique_keys: set[tuple[str, ...]] = set()
    foreign_keys: set[tuple[tuple[str, ...], str, tuple[str, ...]]] = set()

    for index, item in enumerate(items):
        constraint = _TABLE_CONSTRAINT.match(item)
        if constraint is None:
            column_match = _COLUMN.match(item)
            if column_match is None:
                raise SqlsolverSchemaConstraintError(
                    f"cannot identify column declaration in table {table_name!r}: {item!r}"
                )
            token = column_match.group("column")
            name = _unquote_identifier(token)
            if _key(name) in columns:
                raise SqlsolverSchemaConstraintError(
                    f"table {table_name!r} contains duplicate column {name!r}"
                )
            columns[_key(name)] = (token, index)
            column_types[_key(name)] = _column_type(item, column_match.end())
            if re.search(r"\bNOT\s+NULL\b", item, re.IGNORECASE):
                not_null_columns.add(_key(name))
            if re.search(
                r"\b(?:PRIMARY\s+KEY|UNIQUE|REFERENCES|CHECK)\b",
                item[column_match.end() :],
                re.IGNORECASE,
            ):
                raise SqlsolverSchemaConstraintError(
                    f"inline key/reference/check constraint is unsupported in "
                    f"table {table_name!r}: {item!r}"
                )
            continue

        kind = re.sub(r"\s+", " ", constraint.group("kind").upper())
        key_columns = tuple(
            _key(column) for column in _columns_after(item, constraint.end())
        )
        if kind == "PRIMARY KEY":
            primary_keys.add(key_columns)
        elif kind.startswith("UNIQUE"):
            unique_keys.add(key_columns)
        else:
            referenced_match = re.search(
                rf"\bREFERENCES\s+(?P<table>{_QUALIFIED_IDENTIFIER})\s*",
                item,
                re.IGNORECASE | re.DOTALL,
            )
            if referenced_match is None:
                raise SqlsolverSchemaConstraintError(
                    f"malformed foreign key in table {table_name!r}"
                )
            referenced_table = _unquote_identifier(
                re.split(r"\s*\.\s*", referenced_match.group("table"))[-1]
            )
            referenced_columns = tuple(
                _key(column) for column in _columns_after(item, referenced_match.end())
            )
            foreign_keys.add((key_columns, _key(referenced_table), referenced_columns))

    return _TableStatement(
        statement=statement,
        table_name=table_name,
        table_token=table_token,
        open_paren=open_paren,
        close_paren=close_paren,
        items=items,
        columns=columns,
        column_types=column_types,
        not_null_columns=not_null_columns,
        primary_keys=primary_keys,
        unique_keys=unique_keys,
        foreign_keys=foreign_keys,
    )


def _columns_after(item: str, start: int) -> tuple[str, ...]:
    open_paren = find_next_unquoted(item, "(", start)
    close_paren = find_matching_paren(item, open_paren)
    if open_paren < 0 or close_paren < 0:
        raise SqlsolverSchemaConstraintError("constraint has no column list")
    columns = []
    for raw in split_top_level_commas(item[open_paren + 1 : close_paren]):
        match = re.match(rf"^\s*(?P<column>{_IDENTIFIER})\s*$", raw, re.DOTALL)
        if match is None:
            raise SqlsolverSchemaConstraintError(
                f"constraint term is not a simple column: {raw!r}"
            )
        columns.append(_unquote_identifier(match.group("column")))
    if not columns:
        raise SqlsolverSchemaConstraintError("constraint has an empty column list")
    return tuple(columns)


def _column_type(item: str, start: int) -> str:
    rest = item[start:].strip()
    match = re.match(
        r"(?is)^(?P<type>"
        r"[A-Za-z]+(?:\s+(?:PRECISION|VARYING))?"
        r"(?:\s*\([^)]*\))?"
        r")(?=\s|$)",
        rest,
    )
    if match is None:
        raise SqlsolverSchemaConstraintError(
            f"cannot identify SQLSolver column type in {item!r}"
        )
    return re.sub(r"\s+", " ", match.group("type").upper()).replace(" ", "")


def _constraint_types_compatible(left: str, right: str) -> bool:
    if left == right:
        return True
    integral = {
        "TINYINT",
        "SMALLINT",
        "MEDIUMINT",
        "INT",
        "INTEGER",
        "BIGINT",
    }
    return _base_type(left) in integral and _base_type(right) in integral


def _base_type(value: str) -> str:
    return value.split("(", 1)[0]


def _resolve_pair_value(
    value: str,
    tables: list[_TableStatement],
) -> tuple[str, str]:
    matches = [
        (table.table_name, column_name)
        for table in tables
        for column_name, _ in table.columns.values()
        if _key(f"{table.table_name}__{_unquote_identifier(column_name)}")
        == _key(value)
    ]
    if len(matches) != 1:
        raise SqlsolverSchemaConstraintError(
            f"pair constraint reference {value!r} resolves to {len(matches)} schema columns"
        )
    return matches[0]


def _constraint_value(payload: Any, context: str) -> str:
    if not isinstance(payload, dict) or set(payload) != {"value"}:
        raise SqlsolverSchemaConstraintError(f"{context} must contain only value")
    value = payload["value"]
    if not isinstance(value, str) or not value:
        raise SqlsolverSchemaConstraintError(
            f"{context} value must be a nonempty string"
        )
    return value


def _resolve_table(
    tables: dict[str, _TableStatement],
    table_name: str,
) -> _TableStatement:
    table = tables.get(_key(table_name))
    if table is None:
        raise SqlsolverSchemaConstraintError(
            f"constraint references missing table {table_name!r}"
        )
    return table


def _resolve_column(table: _TableStatement, column_name: str) -> str:
    entry = table.columns.get(_key(column_name))
    if entry is None:
        raise SqlsolverSchemaConstraintError(
            f"constraint references missing column {table.table_name}.{column_name}"
        )
    return _unquote_identifier(entry[0])


def _column_token(table: _TableStatement, column_name: str) -> str:
    return table.columns[_key(column_name)][0]


def _unquote_identifier(token: str) -> str:
    token = token.strip()
    if len(token) >= 2 and token[0] == token[-1] and token[0] in {"`", '"'}:
        quote = token[0]
        return token[1:-1].replace(quote * 2, quote)
    return token


def _key(identifier: str) -> str:
    return identifier.casefold()


def _sha256(value: str) -> str:
    return hashlib.sha256(value.encode()).hexdigest()
