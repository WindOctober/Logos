#!/usr/bin/env python3
import argparse
import json
import re
from collections import Counter
from dataclasses import dataclass, field
from functools import partial
from pathlib import Path

from materializer_sql import (
    MYSQL_MATERIALIZER_QUOTE_POLICY,
    find_matching_paren as _shared_find_matching_paren,
    find_next_unquoted as _shared_find_next_unquoted,
    mask_sql_regions as _shared_mask_sql_regions,
    normalize_sql_layout as _shared_normalize_sql_layout,
    parse_schema as _shared_parse_schema,
    split_sql_statements as _shared_split_sql_statements,
    split_top_level_commas as _shared_split_top_level_commas,
    strip_sql_comments as _shared_strip_sql_comments,
)


find_matching_paren = partial(
    _shared_find_matching_paren,
    quote_policy=MYSQL_MATERIALIZER_QUOTE_POLICY,
)
find_next_unquoted = partial(
    _shared_find_next_unquoted,
    quote_policy=MYSQL_MATERIALIZER_QUOTE_POLICY,
)
mask_sql_regions = partial(
    _shared_mask_sql_regions,
    quote_policy=MYSQL_MATERIALIZER_QUOTE_POLICY,
)
normalize_sql_layout = partial(
    _shared_normalize_sql_layout,
    quote_policy=MYSQL_MATERIALIZER_QUOTE_POLICY,
)
parse_schema = partial(
    _shared_parse_schema,
    quote_policy=MYSQL_MATERIALIZER_QUOTE_POLICY,
)
split_sql_statements = partial(
    _shared_split_sql_statements,
    quote_policy=MYSQL_MATERIALIZER_QUOTE_POLICY,
)
split_top_level_commas = partial(
    _shared_split_top_level_commas,
    quote_policy=MYSQL_MATERIALIZER_QUOTE_POLICY,
)
strip_sql_comments = partial(
    _shared_strip_sql_comments,
    quote_policy=MYSQL_MATERIALIZER_QUOTE_POLICY,
)


RESERVED_IDENTIFIERS = {
    "all",
    "and",
    "as",
    "authorization",
    "binary",
    "by",
    "case",
    "count",
    "current_user",
    "date",
    "data",
    "default",
    "external",
    "false",
    "filter",
    "from",
    "group",
    "groups",
    "having",
    "in",
    "is",
    "key",
    "last_value",
    "limit",
    "max",
    "method",
    "min",
    "not",
    "null",
    "offset",
    "on",
    "or",
    "order",
    "percent_rank",
    "primary",
    "position",
    "rank",
    "range",
    "reads",
    "ref",
    "references",
    "scope",
    "select",
    "system",
    "table",
    "true",
    "trigger",
    "type",
    "unique",
    "user",
    "value",
    "when",
    "where",
}


@dataclass
class Column:
    name: str
    type_sql: str
    source_type: str
    source_declaration: str
    not_null: bool = False
    default: str | None = None
    generated: bool = False
    auto_increment: bool = False
    inline_primary: bool = False
    inline_unique: bool = False


@dataclass
class Table:
    name: str
    columns: list[Column] = field(default_factory=list)
    primary_keys: list[tuple[str, ...]] = field(default_factory=list)
    unique_keys: list[tuple[str, ...]] = field(default_factory=list)
    unique_indexes: list[dict] = field(default_factory=list)
    foreign_keys: list[dict] = field(default_factory=list)
    checks: list[dict] = field(default_factory=list)
    unsupported_semantic_constraints: list[str] = field(default_factory=list)
    dropped_items: Counter = field(default_factory=Counter)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Extract solver-compatible core CREATE TABLE DDL from WeTune schema dumps."
    )
    parser.add_argument("--input", help="Input WeTune schema dump.")
    parser.add_argument("--output", help="Output sanitized schema SQL.")
    parser.add_argument("--report", help="Optional JSON audit report.")
    parser.add_argument(
        "--all",
        action="store_true",
        help="Sanitize every *.schema.sql file under --source-dir into --output-dir.",
    )
    parser.add_argument(
        "--source-dir",
        default="benchmarks/core/wetune/schemas",
        help="Source directory for --all, relative to the Logos root.",
    )
    parser.add_argument(
        "--output-dir",
        default="benchmarks/core/wetune/schemas/core",
        help="Output directory for --all, relative to the Logos root.",
    )
    args = parser.parse_args()

    root = Path(__file__).resolve().parents[3]
    if args.all:
        source_dir = resolve(root, args.source_dir)
        output_dir = resolve(root, args.output_dir)
        output_dir.mkdir(parents=True, exist_ok=True)
        for source in sorted(source_dir.glob("*.schema.sql")):
            target = output_dir / source.name
            sanitize_file(source, target, None)
        return 0

    if not args.input or not args.output:
        parser.error("--input and --output are required unless --all is used")

    sanitize_file(
        resolve(root, args.input),
        resolve(root, args.output),
        resolve(root, args.report) if args.report else None,
    )
    return 0


def resolve(root: Path, value: str | Path) -> Path:
    path = Path(value)
    return path if path.is_absolute() else root / path


def sanitize_file(source: Path, target: Path, report_path: Path | None) -> dict:
    raw = source.read_text(errors="replace")
    tables, audit, constraints = sanitize_schema(raw)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(render_schema(tables))
    constraints_path = target.with_suffix(".constraints.json")
    constraints_path.write_text(json.dumps(constraints, indent=2, sort_keys=True) + "\n")

    audit = {
        "source": str(source),
        "target": str(target),
        "constraints": str(constraints_path),
        **audit,
    }
    if report_path:
        report_path.parent.mkdir(parents=True, exist_ok=True)
        report_path.write_text(json.dumps(audit, indent=2, sort_keys=True) + "\n")
    return audit


def sanitize_schema(raw: str) -> tuple[list[Table], dict, dict]:
    stripped = strip_sql_comments(raw)
    tables = parse_schema(
        stripped,
        clean_identifier=clean_create_table_name,
        parse_table=parse_table_body,
    )
    constraints, constraint_audit = parse_alter_constraints(stripped)
    unique_indexes, index_audit = parse_unique_indexes(stripped)

    by_name = {table.name: table for table in tables}
    for table_name, kind, columns in constraints + unique_indexes:
        table = by_name.get(table_name)
        if not table:
            continue
        if kind == "primary":
            add_unique_tuple(table.primary_keys, columns)
        elif kind == "unique":
            add_unique_tuple(table.unique_keys, columns)
        elif kind == "unique_index":
            table.unique_indexes.append(columns)
        elif kind == "foreign":
            table.foreign_keys.append(columns)
        elif kind == "check":
            table.checks.append(columns)
        elif kind == "unsupported":
            table.unsupported_semantic_constraints.append(columns)

    semantic_constraints = collect_semantic_constraints(tables)
    audit = {
        "tables": len(tables),
        "columns": sum(len(table.columns) for table in tables),
        "typeLowerings": sum(
            1
            for table in tables
            for column in table.columns
            if normalize_spaces(column.source_type).upper() != column.type_sql.upper()
        ),
        "primaryKeys": sum(len(table.primary_keys) for table in tables),
        "uniqueKeys": sum(len(table.unique_keys) for table in tables),
        "uniqueIndexes": sum(len(table.unique_indexes) for table in tables),
        "foreignKeys": sum(len(table.foreign_keys) for table in tables),
        "checks": sum(len(table.checks) for table in tables),
        "unsupportedSemanticConstraints": sum(
            len(table.unsupported_semantic_constraints) for table in tables
        ),
        "droppedTableItems": sum_counters(table.dropped_items for table in tables),
        "alterConstraints": constraint_audit,
        "indexConstraints": index_audit,
        "semanticConstraintsPreservedIn": "constraints sidecar JSON",
    }
    return tables, audit, semantic_constraints


def clean_create_table_name(name_part: str) -> str:
    name_part = re.sub(
        r"(?is)^\s*IF\s+NOT\s+EXISTS\s+",
        "",
        name_part,
    ).strip()
    return normalize_table_name(name_part)


def parse_table_body(table_name: str, body: str) -> Table:
    table = Table(name=table_name)
    for item in split_top_level_commas(body):
        item = item.strip()
        if not item:
            continue
        upper = normalize_spaces(item).upper()
        if upper.startswith("PRIMARY KEY"):
            add_unique_tuple(table.primary_keys, parse_columns_in_parens(item))
        elif upper.startswith("UNIQUE ") or upper.startswith("UNIQUE KEY"):
            add_unique_tuple(table.unique_keys, parse_columns_in_parens(item))
        elif upper.startswith("CONSTRAINT "):
            if " PRIMARY KEY " in f" {upper} ":
                add_unique_tuple(table.primary_keys, parse_columns_in_parens(item))
            elif " UNIQUE " in f" {upper} ":
                add_unique_tuple(table.unique_keys, parse_columns_in_parens(item))
            elif " FOREIGN KEY " in f" {upper} ":
                foreign_key = parse_foreign_key(item, table.name, "create_table")
                if foreign_key:
                    table.foreign_keys.append(foreign_key)
                else:
                    table.unsupported_semantic_constraints.append(normalize_spaces(item))
            elif " CHECK " in f" {upper} ":
                table.checks.append(
                    {
                        "table": table.name,
                        "expression": parse_check_expression(item),
                        "source": "create_table",
                    }
                )
            else:
                table.unsupported_semantic_constraints.append(normalize_spaces(item))
        elif is_secondary_index_item(item) or starts_with_any(
            upper,
            (
                "EXCLUDE ",
            ),
        ):
            if upper.startswith("EXCLUDE "):
                table.unsupported_semantic_constraints.append(normalize_spaces(item))
            else:
                table.dropped_items["secondary_index"] += 1
        elif upper.startswith("FOREIGN KEY"):
            foreign_key = parse_foreign_key(item, table.name, "create_table")
            if foreign_key:
                table.foreign_keys.append(foreign_key)
            else:
                table.unsupported_semantic_constraints.append(normalize_spaces(item))
        elif upper.startswith("CHECK "):
            table.checks.append(
                {
                    "table": table.name,
                    "expression": parse_check_expression(item),
                    "source": "create_table",
                }
            )
        else:
            column = parse_column(item)
            if column:
                table.columns.append(column)
                if column.inline_primary:
                    add_unique_tuple(table.primary_keys, (column.name,))
                if column.inline_unique:
                    add_unique_tuple(table.unique_keys, (column.name,))
            else:
                table.dropped_items["unparsed_column"] += 1
    return table


def parse_column(item: str) -> Column | None:
    match = re.match(
        r'(?is)\s*("(?:""|[^"])+?"|`[^`]+?`|\[[^\]]+?\]|[A-Za-z_][A-Za-z0-9_$]*)\s+(.+)$',
        item,
    )
    if not match:
        return None
    name = clean_identifier(match.group(1))
    rest = match.group(2).strip()
    searchable_rest = mask_sql_regions(rest)
    type_sql = normalize_column_type(rest)
    if not type_sql:
        return None
    return Column(
        name=name,
        type_sql=type_sql,
        source_type=extract_source_type(rest),
        source_declaration=normalize_spaces(item),
        not_null=bool(re.search(r"(?is)\bNOT\s+NULL\b", searchable_rest)),
        default=extract_default(rest),
        generated=bool(re.search(r"(?is)\bGENERATED\b", searchable_rest)),
        auto_increment=bool(
            re.search(r"(?is)\bAUTO_INCREMENT\b", searchable_rest)
        ),
        inline_primary=bool(
            re.search(r"(?is)\bPRIMARY\s+KEY\b", searchable_rest)
        ),
        inline_unique=bool(re.search(r"(?is)\bUNIQUE\b", searchable_rest)),
    )


def normalize_column_type(rest: str) -> str:
    normalized = normalize_spaces(rest).lower()
    checks = [
        (r"bigint(?:\(\d+\))?", "BIGINT"),
        (r"(?:integer|int)(?:\(\d+\))?", "INTEGER"),
        (r"(?:smallint|mediumint|tinyint)(?:\(\d+\))?", "INTEGER"),
        (r"boolean|bool", "BOOLEAN"),
        (r"(?:double\s+precision|float|real)", "FLOAT"),
        (r"(?:numeric|decimal)(?:\s*\([^)]*\))?", "FLOAT"),
        (r"timestamp(?:\(\d+\))?(?:\s+with(?:out)?\s+time\s+zone)?", "TIMESTAMP"),
        (r"datetime(?:\(\d+\))?", "TIMESTAMP"),
        (r"date", "DATE"),
        (r"time(?:\(\d+\))?(?:\s+with(?:out)?\s+time\s+zone)?", "TIME"),
        (r"character\s+varying(?:\s*\([^)]*\))?", "VARCHAR(255)"),
        (r"varchar(?:\s*\([^)]*\))?", "VARCHAR(255)"),
        (r"char(?:acter)?(?:\s*\([^)]*\))?", "VARCHAR(255)"),
        (r"(?:text|longtext|mediumtext|tinytext)", "VARCHAR(255)"),
        (r"(?:jsonb?|uuid|inet|cidr|bytea|tsvector|xml)(?:\[\])?", "VARCHAR(255)"),
        (r"[A-Za-z_][A-Za-z0-9_]*(?:\s*\([^)]*\))?\[\]", "VARCHAR(255)"),
    ]
    for pattern, replacement in checks:
        if re.match(pattern + r"\b", normalized):
            return replacement
    return "VARCHAR(255)"


def extract_source_type(rest: str) -> str:
    stop = find_first_modifier(rest)
    return normalize_spaces(rest[:stop] if stop is not None else rest)


def find_first_modifier(rest: str) -> int | None:
    searchable = mask_sql_regions(rest)
    patterns = (
        r"\bNOT\s+NULL\b",
        r"\bNULL\b",
        r"\bDEFAULT\b",
        r"\bPRIMARY\s+KEY\b",
        r"\bUNIQUE\b",
        r"\bREFERENCES\b",
        r"\bCHECK\s*\(",
        r"\bCONSTRAINT\b",
        r"\bGENERATED\b",
        r"\bAUTO_INCREMENT\b",
        r"\bCOMMENT\b",
    )
    positions = [
        match.start()
        for pattern in patterns
        for match in [re.search(pattern, searchable, flags=re.IGNORECASE)]
        if match
    ]
    return min(positions) if positions else None


def extract_default(rest: str) -> str | None:
    match = re.search(r"(?is)\bDEFAULT\b", mask_sql_regions(rest))
    if not match:
        return None
    start = match.end()
    tail = rest[start:].strip()
    if not tail:
        return ""
    stop = find_default_stop(tail)
    return normalize_spaces(tail[:stop] if stop is not None else tail)


def find_default_stop(text: str) -> int | None:
    searchable = mask_sql_regions(text)
    depth = 0
    index = 0
    stop_patterns = (
        "NOT NULL",
        "NULL",
        "PRIMARY KEY",
        "UNIQUE",
        "REFERENCES",
        "CHECK",
        "CONSTRAINT",
        "COMMENT",
    )
    upper = searchable.upper()
    while index < len(text):
        char = searchable[index]
        if char == "(":
            depth += 1
        elif char == ")":
            depth = max(0, depth - 1)
        elif depth == 0:
            for pattern in stop_patterns:
                if upper.startswith(pattern, index) and (
                    index == 0 or not upper[index - 1].isalnum()
                ):
                    return index
        index += 1
    return None


def parse_alter_constraints(sql: str) -> tuple[list[tuple[str, str, object]], dict]:
    constraints = []
    audit = Counter()
    for statement in split_sql_statements(sql):
        compact = normalize_spaces(statement)
        if not re.match(r"(?is)^ALTER\s+TABLE\b", compact):
            continue
        table_match = re.match(r"(?is)^ALTER\s+TABLE\s+(?:ONLY\s+)?(.+?)\s+ADD\s+", compact)
        table_name = normalize_table_name(table_match.group(1)) if table_match else ""
        match = re.match(
            r"(?is)^ALTER\s+TABLE\s+(?:ONLY\s+)?(.+?)\s+ADD\s+CONSTRAINT\s+.+?\s+(PRIMARY\s+KEY|UNIQUE)\s*\((.+)\)",
            compact,
        )
        if match:
            table_name = normalize_table_name(match.group(1))
            kind = "primary" if match.group(2).upper().startswith("PRIMARY") else "unique"
            columns = tuple(clean_identifier(part.strip()) for part in split_top_level_commas(match.group(3)))
            constraints.append((table_name, kind, columns))
            audit[f"kept_{kind}"] += 1
            continue

        if table_name and re.search(r"(?is)\bFOREIGN\s+KEY\b", compact):
            foreign_key = parse_foreign_key(compact, table_name, "alter_table")
            if foreign_key:
                constraints.append((table_name, "foreign", foreign_key))
                audit["kept_foreign"] += 1
                continue

        if table_name and re.search(r"(?is)\bCHECK\s*\(", compact):
            constraints.append(
                (
                    table_name,
                    "check",
                    {
                        "table": table_name,
                        "expression": parse_check_expression(compact),
                        "source": "alter_table",
                    },
                )
            )
            audit["kept_check"] += 1
            continue

        if table_name and re.search(r"(?is)\b(EXCLUDE)\b", compact):
            constraints.append((table_name, "unsupported", compact))
            audit["unsupported_semantic_alter_table"] += 1
            continue

        audit["dropped_nonsemantic_alter_table"] += 1
    return constraints, dict(audit)


def parse_unique_indexes(sql: str) -> tuple[list[tuple[str, str, object]], dict]:
    constraints = []
    audit = Counter()
    for statement in split_sql_statements(sql):
        compact = normalize_spaces(statement)
        if not re.match(r"(?is)^CREATE\s+UNIQUE\s+INDEX\b", compact):
            continue
        match = re.match(
            r"(?is)^CREATE\s+UNIQUE\s+INDEX\s+.+?\s+ON\s+(.+)$",
            compact,
        )
        if not match:
            audit["unsupported_unique_index"] += 1
            continue
        rest = match.group(1)
        open_paren = find_next_unquoted(rest, "(", 0)
        close_paren = find_matching_paren(rest, open_paren) if open_paren >= 0 else -1
        if open_paren < 0 or close_paren < 0:
            audit["unsupported_unique_index"] += 1
            continue
        table_part = re.sub(r"(?is)\s+USING\s+\w+$", "", rest[:open_paren].strip()).strip()
        table_name = normalize_table_name(table_part)
        raw_terms = tuple(normalize_spaces(part) for part in split_top_level_commas(rest[open_paren + 1 : close_paren]))
        tail = normalize_spaces(rest[close_paren + 1 :])
        where = normalize_spaces(re.sub(r"(?is)^WHERE\s+", "", tail)) if tail.upper().startswith("WHERE ") else ""
        simple_columns = tuple(parse_simple_index_column(term) for term in raw_terms)
        if simple_columns and all(simple_columns) and not where:
            constraints.append((table_name, "unique", simple_columns))
            audit["kept_simple_unique_index"] += 1
        else:
            constraints.append(
                (
                    table_name,
                    "unique_index",
                    {
                        "table": table_name,
                        "terms": list(raw_terms),
                        "where": where,
                        "source": "create_unique_index",
                    },
                )
            )
            audit["kept_structured_unique_index"] += 1
    return constraints, dict(audit)


def parse_simple_index_column(term: str) -> str | None:
    term = normalize_spaces(term)
    match = re.match(
        r'(?is)^("(?:""|[^"])+?"|`[^`]+?`|\[[^\]]+?\]|[A-Za-z_][A-Za-z0-9_$]*)'
        r'(?:\s+(?:ASC|DESC))?$',
        term,
    )
    if not match:
        return None
    return clean_identifier(match.group(1))


def parse_foreign_key(item: str, table_name: str, source: str) -> dict | None:
    match = re.search(
        r"(?is)\bFOREIGN\s+KEY\s*\((?P<columns>.*?)\)\s+REFERENCES\s+"
        r"(?P<ref_table>(?:\"(?:\"\"|[^\"])+?\"|`[^`]+?`|\[[^\]]+?\]|[A-Za-z_][A-Za-z0-9_$]*)(?:\s*\.\s*(?:\"(?:\"\"|[^\"])+?\"|`[^`]+?`|\[[^\]]+?\]|[A-Za-z_][A-Za-z0-9_$]*))?)"
        r"\s*\((?P<ref_columns>.*?)\)(?P<actions>.*)$",
        item,
    )
    if not match:
        return None
    return {
        "table": table_name,
        "columns": tuple(
            clean_identifier(part.strip()) for part in split_top_level_commas(match.group("columns"))
        ),
        "refTable": normalize_table_name(match.group("ref_table")),
        "refColumns": tuple(
            clean_identifier(part.strip()) for part in split_top_level_commas(match.group("ref_columns"))
        ),
        "actions": normalize_spaces(match.group("actions")),
        "source": source,
    }


def parse_check_expression(item: str) -> str:
    match = re.search(r"(?is)\bCHECK\s*\(", item)
    if not match:
        return normalize_spaces(item)
    open_paren = item.find("(", match.start())
    close_paren = find_matching_paren(item, open_paren)
    if close_paren < 0:
        return normalize_spaces(item[match.end() :])
    return normalize_spaces(item[open_paren + 1 : close_paren])


def collect_semantic_constraints(tables: list[Table]) -> dict:
    return {
        "semanticSchema": {
            "tables": [
                {
                    "name": table.name,
                    "columns": [
                        {
                            "name": column.name,
                            "sourceDeclaration": column.source_declaration,
                            "sourceType": column.source_type,
                            "normalizedFrontendType": column.type_sql,
                            "nullable": not column.not_null,
                            "notNull": column.not_null,
                            "default": column.default,
                            "generated": column.generated,
                            "autoIncrement": column.auto_increment,
                            "inlinePrimary": column.inline_primary,
                            "inlineUnique": column.inline_unique,
                        }
                        for column in table.columns
                    ],
                }
                for table in tables
            ],
            "typeSemantics": "sourceType/sourceDeclaration are authoritative for benchmark semantics; normalizedFrontendType is a tool-facing lowering.",
        },
        "primaryKeys": [
            {"table": table.name, "columns": list(columns)}
            for table in tables
            for columns in table.primary_keys
        ],
        "uniqueKeys": [
            {
                "table": table.name,
                "columns": list(columns),
                "nullableColumns": nullable_columns(table, columns),
                "semantics": "sql_unique_allows_multiple_nulls",
            }
            for table in tables
            for columns in table.unique_keys
        ],
        "uniqueIndexes": [
            unique_index
            for table in tables
            for unique_index in table.unique_indexes
        ],
        "foreignKeys": [
            {
                **foreign_key,
                "columns": list(foreign_key["columns"]),
                "refColumns": list(foreign_key["refColumns"]),
            }
            for table in tables
            for foreign_key in table.foreign_keys
        ],
        "checks": [
            check
            for table in tables
            for check in table.checks
        ],
        "unsupportedSemanticConstraints": [
            {"table": table.name, "constraint": constraint}
            for table in tables
            for constraint in table.unsupported_semantic_constraints
        ],
    }


def nullable_columns(table: Table, columns: tuple[str, ...]) -> list[str]:
    by_name = {column.name: column for column in table.columns}
    return [name for name in columns if name not in by_name or not by_name[name].not_null]


def parse_columns_in_parens(item: str) -> tuple[str, ...]:
    open_paren = find_next_unquoted(item, "(", 0)
    if open_paren < 0:
        return ()
    close_paren = find_matching_paren(item, open_paren)
    if close_paren < 0:
        return ()
    return tuple(first_identifier(part) for part in split_top_level_commas(item[open_paren + 1 : close_paren]))


def normalize_table_name(name_part: str) -> str:
    name_part = normalize_spaces(name_part)
    name_part = re.sub(r"(?is)\s+INHERITS\s*\(.+\)$", "", name_part).strip()
    pieces = split_qualified_name(name_part)
    return clean_identifier(pieces[-1]) if pieces else clean_identifier(name_part)


def split_qualified_name(name: str) -> list[str]:
    parts = []
    start = 0
    for index, char in enumerate(mask_sql_regions(name)):
        if char == ".":
            parts.append(name[start:index].strip())
            start = index + 1
    parts.append(name[start:].strip())
    return [part for part in parts if part]


def clean_identifier(identifier: str) -> str:
    identifier = identifier.strip()
    if identifier.startswith('"') and identifier.endswith('"'):
        return identifier[1:-1].replace('""', '"')
    if identifier.startswith("`") and identifier.endswith("`"):
        return identifier[1:-1].replace("``", "`")
    if identifier.startswith("[") and identifier.endswith("]"):
        return identifier[1:-1]
    return identifier


def first_identifier(value: str) -> str:
    value = value.strip()
    match = re.match(r'(?is)("(?:""|[^"])+?"|`[^`]+?`|\[[^\]]+?\]|[A-Za-z_][A-Za-z0-9_$]*)', value)
    return clean_identifier(match.group(1)) if match else clean_identifier(value.split()[0])


def is_secondary_index_item(item: str) -> bool:
    compact = normalize_spaces(item)
    return bool(
        re.match(
            r"(?is)^(?:KEY|INDEX|FULLTEXT(?:\s+KEY|\s+INDEX)?|SPATIAL(?:\s+KEY|\s+INDEX)?)\s+"
            r'(?:"(?:""|[^"])+?"|`[^`]+?`|\[[^\]]+?\]|[A-Za-z_][A-Za-z0-9_$]*)\s*\(',
            compact,
        )
    )


def quote_identifier(identifier: str) -> str:
    if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", identifier) and identifier.lower() not in RESERVED_IDENTIFIERS:
        return identifier
    return '"' + identifier.replace('"', '""') + '"'


def add_unique_tuple(values: list[tuple[str, ...]], candidate: tuple[str, ...]) -> None:
    candidate = tuple(part for part in candidate if part)
    if candidate and candidate not in values:
        values.append(candidate)


def render_schema(tables: list[Table]) -> str:
    rendered = []
    for table in tables:
        items = [
            f"  {quote_identifier(column.name)} {column.type_sql}{' NOT NULL' if column.not_null else ''}"
            for column in table.columns
        ]
        for columns in table.primary_keys:
            items.append("  PRIMARY KEY (" + ", ".join(quote_identifier(column) for column in columns) + ")")
        for columns in table.unique_keys:
            items.append("  UNIQUE (" + ", ".join(quote_identifier(column) for column in columns) + ")")
        rendered.append(f"CREATE TABLE {quote_identifier(table.name)} (\n" + ",\n".join(items) + "\n);")
    return "\n\n".join(rendered) + ("\n" if rendered else "")


def starts_with_any(value: str, prefixes: tuple[str, ...]) -> bool:
    return any(value.startswith(prefix) for prefix in prefixes)


def normalize_spaces(value: str) -> str:
    return normalize_sql_layout(value)


def sum_counters(counters) -> dict[str, int]:
    total = Counter()
    for counter in counters:
        total.update(counter)
    return dict(total)


if __name__ == "__main__":
    raise SystemExit(main())
