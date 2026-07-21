"""Fail-closed provenance bridge for a top-level relational ``SELECT *``.

SQLGlot qualification is deliberately not used here.  The source row shape is
recovered from the syntactic ``FROM`` order, then independently compared with
Calcite's direct input-reference lineage and (after parsing) QED's direct
column lineage.  This keeps a wildcard rewrite sound even when every output
has the same type and a type-only check could not detect a permutation.

The admitted source fragment is intentionally small: unquoted base tables and
direct pass-through derived SELECTs, joined with ordinary ``ON`` joins or
``CROSS JOIN``.  Unsupported syntax raises :class:`ProvenanceError`.
"""

from __future__ import annotations

import hashlib
import re
from copy import deepcopy
from collections.abc import Sequence

import sqlglot
from sqlglot import exp

__all__ = [
    "ProvenanceError",
    "expand_top_level_unqualified_star",
    "validate_calcite_rel_direct_provenance",
    "validate_qed_json_direct_provenance",
]


class ProvenanceError(ValueError):
    """The requested provenance bridge is outside the attested fragment."""


_SAFE_IDENTIFIER = re.compile(r"[A-Za-z_][A-Za-z0-9_$]*\Z")
_CALCITE_INPUT_REF = re.compile(r"\$(\d+)\Z")
_ALLOWED_SELECT_FIELDS = {"expressions", "from_", "joins", "where"}
_ALLOWED_JOIN_SIDES = {"", "LEFT", "RIGHT", "FULL"}
_ALLOWED_JOIN_KINDS = {"", "INNER", "OUTER", "CROSS"}


def _identifier_key(value: str) -> str:
    # Quoted identifiers are rejected, so PostgreSQL's unquoted folding is the
    # only identifier equivalence needed by this module.
    return value.casefold()


def _require_identifier(value: object, *, context: str) -> str:
    if not isinstance(value, str) or not _SAFE_IDENTIFIER.fullmatch(value):
        raise ProvenanceError(f"{context} is not a simple unquoted identifier")
    return value


def _is_present(value: object) -> bool:
    return value is not None and value is not False and value != []


def _schema_index(schema: object) -> dict[str, dict]:
    if not isinstance(schema, list) or not schema:
        raise ProvenanceError("authority schema must be a non-empty table list")
    tables: dict[str, dict] = {}
    for table in schema:
        if not isinstance(table, dict):
            raise ProvenanceError("authority schema contains a malformed table")
        name = _require_identifier(table.get("name"), context="schema table name")
        columns = table.get("columns")
        if not isinstance(columns, list) or not columns:
            raise ProvenanceError(f"schema table {name} has no declared columns")
        column_keys: set[str] = set()
        normalized_columns: list[dict] = []
        for column_ordinal, column in enumerate(columns):
            if not isinstance(column, dict):
                raise ProvenanceError(f"schema table {name} has a malformed column")
            column_name = _require_identifier(
                column.get("name"), context=f"column name in {name}"
            )
            type_name = column.get("type")
            if not isinstance(type_name, str) or not type_name:
                raise ProvenanceError(f"schema column {name}.{column_name} has no type")
            column_key = _identifier_key(column_name)
            if column_key in column_keys:
                raise ProvenanceError(
                    f"schema table {name} has duplicate folded column {column_name}"
                )
            column_keys.add(column_key)
            normalized_columns.append(
                {
                    "name": column_name,
                    "type": type_name,
                    "columnOrdinal": column_ordinal,
                }
            )
        table_key = _identifier_key(name)
        if table_key in tables:
            raise ProvenanceError(f"schema has duplicate folded table {name}")
        tables[table_key] = {"name": name, "columns": normalized_columns}
    return tables


def _copy_field(field: dict) -> dict:
    return deepcopy(field)


def _source_origin_key(field: dict) -> tuple[int, str, str, int]:
    origin = field.get("origin") if isinstance(field, dict) else None
    if not isinstance(origin, dict):
        raise ProvenanceError("expected source output lacks provenance")
    scan = origin.get("scanOccurrence")
    table = origin.get("table")
    column = origin.get("column")
    column_ordinal = origin.get("columnOrdinal")
    if (
        not isinstance(scan, int)
        or isinstance(scan, bool)
        or scan < 0
        or not isinstance(table, str)
        or not isinstance(column, str)
        or not isinstance(column_ordinal, int)
        or isinstance(column_ordinal, bool)
        or column_ordinal < 0
    ):
        raise ProvenanceError("expected source output has malformed provenance")
    return (
        scan,
        _identifier_key(table),
        _identifier_key(column),
        column_ordinal,
    )


def _source_type(field: dict) -> str:
    type_name = field.get("sourceType") if isinstance(field, dict) else None
    if not isinstance(type_name, str) or not type_name:
        raise ProvenanceError("expected source output lacks a source type")
    return type_name


class _SurfaceResolver:
    def __init__(self, schema: list[dict]):
        self.tables = _schema_index(schema)
        self.next_scan = 0

    @staticmethod
    def _reject_unsupported_select_fields(
        select: exp.Select,
        *,
        top_level: bool,
    ) -> None:
        allowed = set(_ALLOWED_SELECT_FIELDS)
        if top_level:
            # These clauses observe or trim rows but do not change their shape;
            # the exact star-span replacement leaves every clause byte intact.
            allowed.update({"order", "limit", "offset"})
        for field_name, value in select.args.items():
            if field_name not in allowed and _is_present(value):
                raise ProvenanceError(
                    f"SELECT field {field_name} is outside the star bridge"
                )

    @staticmethod
    def _reject_predicate_subqueries(expression: object, *, context: str) -> None:
        if isinstance(expression, exp.Expression) and expression.find(exp.Subquery):
            raise ProvenanceError(f"subquery in {context} is outside the star bridge")

    def _base_relation(self, table_expression: exp.Table) -> dict:
        allowed_fields = {"this", "alias"}
        for field_name, value in table_expression.args.items():
            if field_name not in allowed_fields and _is_present(value):
                raise ProvenanceError(
                    f"base-table field {field_name} is outside the star bridge"
                )
        table = self.tables.get(_identifier_key(table_expression.name))
        if table is None:
            raise ProvenanceError(
                f"base table {table_expression.name} is absent from authority schema"
            )
        alias = table_expression.args.get("alias")
        if isinstance(alias, exp.TableAlias) and alias.args.get("columns"):
            raise ProvenanceError("relation column-alias lists are outside the bridge")
        qualifier = _require_identifier(
            table_expression.alias_or_name, context="visible base-table qualifier"
        )
        scan = self.next_scan
        self.next_scan += 1
        fields = []
        for column in table["columns"]:
            fields.append(
                {
                    "outputLabel": column["name"],
                    "visibleQualifier": qualifier,
                    "aliasPath": [qualifier],
                    "sourceType": column["type"],
                    "origin": {
                        "scanOccurrence": scan,
                        "table": table["name"],
                        "column": column["name"],
                        "columnOrdinal": column["columnOrdinal"],
                    },
                }
            )
        return {"qualifier": qualifier, "fields": fields}

    def _derived_relation(self, subquery: exp.Subquery) -> dict:
        for field_name, value in subquery.args.items():
            if field_name not in {"this", "alias"} and _is_present(value):
                raise ProvenanceError(
                    f"derived-table field {field_name} is outside the star bridge"
                )
        alias = subquery.args.get("alias")
        if not isinstance(alias, exp.TableAlias) or not subquery.alias:
            raise ProvenanceError("derived relation must have an alias")
        if alias.args.get("columns"):
            raise ProvenanceError("derived column-alias lists are outside the bridge")
        if not isinstance(subquery.this, exp.Select):
            raise ProvenanceError("derived relation must contain one plain SELECT")
        qualifier = _require_identifier(
            subquery.alias, context="visible derived-table qualifier"
        )
        fields = self._select_outputs(subquery.this, top_level=False)
        folded_labels = [_identifier_key(field["outputLabel"]) for field in fields]
        if len(folded_labels) != len(set(folded_labels)):
            raise ProvenanceError(
                "derived relation has duplicate output labels and cannot be qualified"
            )
        for field in fields:
            field["visibleQualifier"] = qualifier
            field["aliasPath"].append(qualifier)
        return {"qualifier": qualifier, "fields": fields}

    def _relation(self, expression: exp.Expression) -> dict:
        if isinstance(expression, exp.Table):
            return self._base_relation(expression)
        if isinstance(expression, exp.Subquery):
            return self._derived_relation(expression)
        raise ProvenanceError(
            f"FROM relation {type(expression).__name__} is outside the star bridge"
        )

    def _scope(self, select: exp.Select, *, top_level: bool) -> list[dict]:
        self._reject_unsupported_select_fields(select, top_level=top_level)
        self._reject_predicate_subqueries(select.args.get("where"), context="WHERE")
        from_clause = select.args.get("from_")
        if not isinstance(from_clause, exp.From) or not isinstance(
            from_clause.this, exp.Expression
        ):
            raise ProvenanceError("SELECT must have one plain FROM source")
        relations = [self._relation(from_clause.this)]
        for join in select.args.get("joins") or []:
            if not isinstance(join, exp.Join):
                raise ProvenanceError("SELECT contains a malformed JOIN")
            if join.args.get("using"):
                raise ProvenanceError("JOIN USING changes unqualified-star row shape")
            if str(join.args.get("method") or "").upper() == "NATURAL":
                raise ProvenanceError("NATURAL JOIN changes unqualified-star row shape")
            side = str(join.args.get("side") or "").upper()
            kind = str(join.args.get("kind") or "").upper()
            if side not in _ALLOWED_JOIN_SIDES or kind not in _ALLOWED_JOIN_KINDS:
                raise ProvenanceError(f"unsupported JOIN shape: {side} {kind}".strip())
            for field_name, value in join.args.items():
                if field_name not in {"this", "on", "side", "kind"} and _is_present(
                    value
                ):
                    raise ProvenanceError(
                        f"JOIN field {field_name} is outside the star bridge"
                    )
            on = join.args.get("on")
            if kind == "CROSS":
                if _is_present(on) or side:
                    raise ProvenanceError(
                        "CROSS JOIN must not have ON or an outer side"
                    )
            elif not isinstance(on, exp.Expression):
                # This also rejects comma joins, which SQLGlot represents as a
                # shape-less Join node rather than an explicit CROSS JOIN.
                raise ProvenanceError("ordinary JOIN must have an ON predicate")
            self._reject_predicate_subqueries(on, context="JOIN ON")
            if not isinstance(join.this, exp.Expression):
                raise ProvenanceError("JOIN has no relation")
            relations.append(self._relation(join.this))
        return relations

    @staticmethod
    def _resolve_direct_column(column: exp.Column, relations: list[dict]) -> dict:
        if isinstance(column.this, exp.Star):
            raise ProvenanceError("qualified stars are outside derived projections")
        relation_qualifiers = {
            _identifier_key(relation["qualifier"]) for relation in relations
        }
        if not column.table and _identifier_key(column.name) in relation_qualifiers:
            raise ProvenanceError(
                "whole-row relation references are outside the bridge"
            )
        matches = []
        for relation in relations:
            if column.table and _identifier_key(column.table) != _identifier_key(
                relation["qualifier"]
            ):
                continue
            matches.extend(
                field
                for field in relation["fields"]
                if _identifier_key(field["outputLabel"]) == _identifier_key(column.name)
            )
        if len(matches) != 1:
            raise ProvenanceError(
                f"derived direct column does not resolve uniquely: {column.sql()}"
            )
        return _copy_field(matches[0])

    def _select_outputs(self, select: exp.Select, *, top_level: bool) -> list[dict]:
        relations = self._scope(select, top_level=top_level)
        selections = select.expressions
        if len(selections) == 1 and isinstance(selections[0], exp.Star):
            if any(_is_present(value) for value in selections[0].args.values()):
                raise ProvenanceError("modified star is outside the bridge")
            return [
                _copy_field(field)
                for relation in relations
                for field in relation["fields"]
            ]
        if top_level:
            raise ProvenanceError(
                "top-level SELECT list must be exactly one unqualified star"
            )
        outputs = []
        for selection in selections:
            value = selection
            output_label = None
            if isinstance(selection, exp.Alias):
                value = selection.this
                output_label = _require_identifier(
                    selection.alias, context="derived output alias"
                )
            if not isinstance(value, exp.Column) or isinstance(value.this, exp.Star):
                raise ProvenanceError(
                    "derived outputs must be direct columns, optionally aliased"
                )
            field = self._resolve_direct_column(value, relations)
            if output_label is not None:
                field["outputLabel"] = output_label
            outputs.append(field)
        if not outputs:
            raise ProvenanceError("derived SELECT has no outputs")
        return outputs

    def expand(self, sql: str) -> dict:
        if not isinstance(sql, str) or not sql:
            raise ProvenanceError("source SQL must be a non-empty string")
        try:
            statements = sqlglot.parse(sql, read="postgres")
        except sqlglot.errors.ParseError as error:
            raise ProvenanceError("source SQL does not parse as PostgreSQL") from error
        if len(statements) != 1 or not isinstance(statements[0], exp.Select):
            raise ProvenanceError("source root must be one plain SELECT, not a set op")
        select = statements[0]
        if any(
            identifier.args.get("quoted")
            for identifier in select.find_all(exp.Identifier)
        ):
            raise ProvenanceError("quoted identifiers are outside the star bridge")
        if len(select.expressions) != 1 or not isinstance(
            select.expressions[0], exp.Star
        ):
            raise ProvenanceError(
                "top-level SELECT list must be exactly one unqualified star"
            )
        star = select.expressions[0]
        start = star.meta.get("start")
        end = star.meta.get("end")
        if (
            not isinstance(start, int)
            or isinstance(start, bool)
            or not isinstance(end, int)
            or isinstance(end, bool)
            or start < 0
            or end < start
            or sql[start : end + 1] != "*"
        ):
            raise ProvenanceError("top-level star lacks an exact source span")
        fields = self._select_outputs(select, top_level=True)
        expressions = [
            f'{field["visibleQualifier"]}.{field["outputLabel"]}' for field in fields
        ]
        replacement = ", ".join(expressions)
        rewritten = sql[:start] + replacement + sql[end + 1 :]
        outputs = []
        for ordinal, (expression_sql, field) in enumerate(zip(expressions, fields)):
            outputs.append(
                {
                    "ordinal": ordinal,
                    "sourceExpression": expression_sql,
                    **_copy_field(field),
                }
            )
        return {
            "status": "verified-source-top-level-unqualified-star",
            "sourceSha256": hashlib.sha256(sql.encode()).hexdigest(),
            "rewrittenSha256": hashlib.sha256(rewritten.encode()).hexdigest(),
            "sourceStar": {"start": start, "end": end, "text": "*"},
            "rewrittenSql": rewritten,
            "outputs": outputs,
        }


def expand_top_level_unqualified_star(sql: str, schema: list[dict]) -> dict:
    """Expand exactly the root unqualified star using syntactic FROM order.

    All bytes outside the root star's exact SQLGlot source span are preserved.
    The returned outputs carry base scan-occurrence and column provenance.
    """

    return _SurfaceResolver(schema).expand(sql)


def _calcite_row_type(node: dict, *, context: str) -> list[dict]:
    row_type = node.get("rowType")
    if not isinstance(row_type, list):
        raise ProvenanceError(f"{context} has no Calcite rowType")
    fields = []
    for field in row_type:
        if (
            not isinstance(field, dict)
            or not isinstance(field.get("name"), str)
            or not isinstance(field.get("type"), str)
        ):
            raise ProvenanceError(f"{context} has a malformed Calcite rowType")
        fields.append({"relName": field["name"], "type": field["type"]})
    return fields


class _CalciteResolver:
    def __init__(self, schema: list[dict]):
        self.tables = _schema_index(schema)
        self.next_scan = 0
        self.project_count = 0

    @staticmethod
    def _apply_row_type(node: dict, fields: list[dict], *, context: str) -> list[dict]:
        row_type = _calcite_row_type(node, context=context)
        if len(row_type) != len(fields):
            raise ProvenanceError(f"{context} rowType arity disagrees with lineage")
        result = []
        for index, (field, row_field) in enumerate(zip(fields, row_type)):
            if field["type"] != row_field["type"]:
                raise ProvenanceError(
                    f"{context} rowType type disagrees at output {index}"
                )
            result.append({**_copy_field(field), "relName": row_field["relName"]})
        return result

    def _scan(self, node: dict) -> list[dict]:
        inputs = node.get("inputs")
        if inputs not in (None, []):
            raise ProvenanceError("Calcite TableScan unexpectedly has inputs")
        table_path = node.get("table")
        if (
            not isinstance(table_path, list)
            or len(table_path) != 1
            or not isinstance(table_path[0], str)
        ):
            raise ProvenanceError("Calcite TableScan has a non-local table path")
        table = self.tables.get(_identifier_key(table_path[0]))
        if table is None:
            raise ProvenanceError("Calcite TableScan is absent from authority schema")
        row_type = _calcite_row_type(node, context="Calcite TableScan")
        declared = [(column["name"], column["type"]) for column in table["columns"]]
        actual = [(field["relName"], field["type"]) for field in row_type]
        if actual != declared:
            raise ProvenanceError(
                "Calcite TableScan rowType disagrees with declaration order"
            )
        scan = self.next_scan
        self.next_scan += 1
        return [
            {
                "relName": column["name"],
                "type": column["type"],
                "origin": {
                    "scanOccurrence": scan,
                    "table": table["name"],
                    "column": column["name"],
                    "columnOrdinal": column["columnOrdinal"],
                },
            }
            for column in table["columns"]
        ]

    def walk(self, node: object) -> list[dict]:
        if not isinstance(node, dict):
            raise ProvenanceError("Calcite relational node is malformed")
        node_type = node.get("type")
        if node_type == "LogicalTableScan":
            return self._scan(node)
        inputs = node.get("inputs")
        if not isinstance(inputs, list):
            raise ProvenanceError(f"Calcite {node_type} has no input list")
        if node_type in {"LogicalFilter", "LogicalSort"}:
            if len(inputs) != 1:
                raise ProvenanceError(f"Calcite {node_type} must have one input")
            fields = self.walk(inputs[0])
        elif node_type == "LogicalJoin":
            if len(inputs) != 2:
                raise ProvenanceError("Calcite Join must have two inputs")
            fields = self.walk(inputs[0]) + self.walk(inputs[1])
        elif node_type == "LogicalProject":
            if len(inputs) != 1:
                raise ProvenanceError("Calcite Project must have one input")
            source = self.walk(inputs[0])
            self.project_count += 1
            projects = node.get("projects")
            project_rex = node.get("projectRex")
            indexes: list[int] = []
            if projects is not None:
                if not isinstance(projects, list):
                    raise ProvenanceError(
                        "Calcite Project expression list is malformed"
                    )
                for expression in projects:
                    if not isinstance(expression, str):
                        raise ProvenanceError("Calcite Project expression is malformed")
                    match = _CALCITE_INPUT_REF.fullmatch(expression)
                    if match is None:
                        raise ProvenanceError(
                            "Calcite Project contains a computed expression"
                        )
                    indexes.append(int(match.group(1)))
            if project_rex is not None:
                if not isinstance(project_rex, list):
                    raise ProvenanceError("Calcite Project Rex list is malformed")
                rex_indexes: list[int] = []
                for expression in project_rex:
                    if (
                        not isinstance(expression, dict)
                        or expression.get("class") != "RexInputRef"
                        or expression.get("kind") != "INPUT_REF"
                        or not isinstance(expression.get("index"), int)
                        or isinstance(expression.get("index"), bool)
                        or expression.get("index") < 0
                        or expression.get("text") != f'${expression.get("index")}'
                        or not isinstance(expression.get("type"), str)
                        or not expression.get("type")
                        or not isinstance(expression.get("fullType"), str)
                        or not expression.get("fullType")
                        or not isinstance(expression.get("nullable"), bool)
                    ):
                        raise ProvenanceError(
                            "Calcite Project contains a computed Rex expression"
                        )
                    rex_indexes.append(expression["index"])
                if projects is not None:
                    if len(projects) != len(project_rex) or any(
                        legacy != typed.get("text")
                        for legacy, typed in zip(projects, project_rex)
                    ):
                        raise ProvenanceError(
                            "Calcite Project has conflicting expression encodings"
                        )
                    if indexes != rex_indexes:
                        raise ProvenanceError(
                            "Calcite Project has conflicting expression encodings"
                        )
                else:
                    indexes = rex_indexes
            if projects is None and project_rex is None:
                raise ProvenanceError("Calcite Project has no expression list")
            fields = []
            for input_index in indexes:
                if input_index >= len(source):
                    raise ProvenanceError(
                        "Calcite Project input reference is out of bounds"
                    )
                fields.append(_copy_field(source[input_index]))
        else:
            raise ProvenanceError(
                f"Calcite relational node {node_type} is outside direct provenance"
            )
        return self._apply_row_type(node, fields, context=f"Calcite {node_type}")


def validate_calcite_rel_direct_provenance(
    rel: dict,
    schema: list[dict],
    expected_outputs: Sequence[dict],
) -> dict:
    """Validate direct Calcite output lineage against source-star provenance."""

    if not isinstance(rel, dict):
        raise ProvenanceError("Calcite root is malformed")
    if not isinstance(expected_outputs, Sequence) or isinstance(
        expected_outputs, (str, bytes)
    ):
        raise ProvenanceError("expected source outputs must be a sequence")
    resolver = _CalciteResolver(schema)
    actual = resolver.walk(rel)
    if resolver.project_count == 0:
        raise ProvenanceError("Calcite relation has no direct Project")
    expected = list(expected_outputs)
    if len(actual) != len(expected):
        raise ProvenanceError("Calcite output arity disagrees with source star")
    for index, (actual_field, expected_field) in enumerate(zip(actual, expected)):
        if _source_origin_key(actual_field) != _source_origin_key(expected_field):
            raise ProvenanceError(
                f"Calcite output provenance disagrees at ordinal {index}"
            )
        if actual_field["type"] != _source_type(expected_field):
            raise ProvenanceError(f"Calcite output type disagrees at ordinal {index}")
    return {
        "status": "verified-calcite-direct-output-provenance",
        "outputs": [
            {
                "ordinal": index,
                "calciteName": field["relName"],
                "sourceType": field["type"],
                "origin": _copy_field(field["origin"]),
            }
            for index, field in enumerate(actual)
        ],
    }


def _qed_schemas(schemas: object) -> list[dict]:
    if not isinstance(schemas, list) or not schemas:
        raise ProvenanceError("parsed QED document has no schemas")
    result = []
    for schema in schemas:
        if not isinstance(schema, dict):
            raise ProvenanceError("parsed QED schema is malformed")
        name = _require_identifier(schema.get("name"), context="QED schema name")
        fields = schema.get("fields")
        types = schema.get("types")
        if (
            not isinstance(fields, list)
            or not isinstance(types, list)
            or len(fields) != len(types)
            or not fields
        ):
            raise ProvenanceError(f"parsed QED schema {name} has malformed fields")
        normalized_fields = []
        seen: set[str] = set()
        for parser_ordinal, (field_name, type_name) in enumerate(zip(fields, types)):
            field_name = _require_identifier(field_name, context=f"QED field in {name}")
            if not isinstance(type_name, str) or not type_name:
                raise ProvenanceError(f"QED field {name}.{field_name} has no type")
            field_key = _identifier_key(field_name)
            if field_key in seen:
                raise ProvenanceError(f"QED schema {name} has duplicate field names")
            seen.add(field_key)
            normalized_fields.append(
                {
                    "name": field_name,
                    "type": type_name,
                    "parserColumnOrdinal": parser_ordinal,
                }
            )
        result.append({"name": name, "fields": normalized_fields})
    return result


class _QedResolver:
    def __init__(self, schemas: list[dict]):
        self.schemas = _qed_schemas(schemas)
        self.next_scan = 0
        self.project_count = 0

    def walk(self, node: object) -> list[dict]:
        if not isinstance(node, dict) or len(node) != 1:
            raise ProvenanceError("parsed QED relation must have one constructor")
        if "scan" in node:
            schema_index = node["scan"]
            if (
                not isinstance(schema_index, int)
                or isinstance(schema_index, bool)
                or schema_index < 0
                or schema_index >= len(self.schemas)
            ):
                raise ProvenanceError("parsed QED scan index is invalid")
            schema = self.schemas[schema_index]
            scan = self.next_scan
            self.next_scan += 1
            return [
                {
                    "type": field["type"],
                    "origin": {
                        "scanOccurrence": scan,
                        "table": schema["name"],
                        "column": field["name"],
                        "parserColumnOrdinal": field["parserColumnOrdinal"],
                    },
                }
                for field in schema["fields"]
            ]
        if "filter" in node:
            body = node["filter"]
            if (
                not isinstance(body, dict)
                or set(body) != {"source", "condition"}
                or not isinstance(body.get("source"), dict)
            ):
                raise ProvenanceError("parsed QED filter is malformed")
            return self.walk(body["source"])
        if "sort" in node:
            body = node["sort"]
            if (
                not isinstance(body, dict)
                or set(body) != {"source", "collation", "offset", "limit"}
                or not isinstance(body.get("source"), dict)
            ):
                raise ProvenanceError("parsed QED sort is malformed")
            return self.walk(body["source"])
        if "join" in node:
            body = node["join"]
            if (
                not isinstance(body, dict)
                or not set(body).issubset({"left", "right", "kind", "condition"})
                or not isinstance(body.get("left"), dict)
                or not isinstance(body.get("right"), dict)
            ):
                raise ProvenanceError("parsed QED join is malformed")
            return self.walk(body["left"]) + self.walk(body["right"])
        if "project" in node:
            body = node["project"]
            if (
                not isinstance(body, dict)
                or set(body) != {"source", "target"}
                or not isinstance(body.get("source"), dict)
            ):
                raise ProvenanceError("parsed QED project is malformed")
            targets = body.get("target")
            if not isinstance(targets, list):
                raise ProvenanceError("parsed QED project has no target list")
            source = self.walk(body["source"])
            self.project_count += 1
            outputs = []
            for target in targets:
                if not isinstance(target, dict) or set(target) != {"column", "type"}:
                    raise ProvenanceError(
                        "parsed QED project target is not a direct column"
                    )
                column = target["column"]
                if (
                    not isinstance(column, int)
                    or isinstance(column, bool)
                    or column < 0
                    or column >= len(source)
                ):
                    raise ProvenanceError("parsed QED project column index is invalid")
                field = _copy_field(source[column])
                if target["type"] != field["type"]:
                    raise ProvenanceError(
                        "parsed QED project type disagrees with its source column"
                    )
                outputs.append(field)
            return outputs
        raise ProvenanceError(
            f"parsed QED relation {next(iter(node))} is outside direct provenance"
        )


def validate_qed_json_direct_provenance(
    query: dict,
    schemas: list[dict],
    expected_outputs: Sequence[dict],
    expected_output_types: Sequence[str],
) -> dict:
    """Validate parsed-QED direct lineage, including name-sorted schemas.

    ``expected_output_types`` must contain the post-abstraction types (for
    example, ``INTEGER`` where a source ``VARCHAR`` was opaquely encoded).
    """

    if not isinstance(query, dict):
        raise ProvenanceError("parsed QED query root is malformed")
    if not isinstance(expected_outputs, Sequence) or isinstance(
        expected_outputs, (str, bytes)
    ):
        raise ProvenanceError("expected source outputs must be a sequence")
    if not isinstance(expected_output_types, Sequence) or isinstance(
        expected_output_types, (str, bytes)
    ):
        raise ProvenanceError("expected QED output types must be a sequence")
    expected = list(expected_outputs)
    expected_types = list(expected_output_types)
    resolver = _QedResolver(schemas)
    actual = resolver.walk(query)
    if resolver.project_count == 0:
        raise ProvenanceError("parsed QED query has no direct projection")
    if len(actual) != len(expected) or len(actual) != len(expected_types):
        raise ProvenanceError("parsed QED output arity disagrees with source star")
    for index, (actual_field, expected_field, expected_type) in enumerate(
        zip(actual, expected, expected_types)
    ):
        expected_origin = _source_origin_key(expected_field)
        actual_origin = actual_field["origin"]
        actual_key = (
            actual_origin["scanOccurrence"],
            _identifier_key(actual_origin["table"]),
            _identifier_key(actual_origin["column"]),
        )
        if actual_key != expected_origin[:3]:
            raise ProvenanceError(
                f"parsed QED output provenance disagrees at ordinal {index}"
            )
        if not isinstance(expected_type, str) or actual_field["type"] != expected_type:
            raise ProvenanceError(
                f"parsed QED output type disagrees at ordinal {index}"
            )
    return {
        "status": "verified-qed-direct-output-provenance",
        "outputs": [
            {
                "ordinal": index,
                "type": field["type"],
                "origin": _copy_field(field["origin"]),
            }
            for index, field in enumerate(actual)
        ],
    }
