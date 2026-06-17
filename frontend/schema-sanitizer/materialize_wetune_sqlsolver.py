#!/usr/bin/env python3
import argparse
import csv
import json
import re
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path


READ_DIALECT_BY_APP = {
    "diaspora": "mysql",
    "discourse": "postgres",
    "gitlab": "postgres",
    "lobsters": "mysql",
    "redmine": "postgres",
    "solidus": "mysql",
    "spree": "mysql",
}

SQLSOLVER_RESERVED = {
    "all",
    "and",
    "as",
    "authorization",
    "binary",
    "by",
    "case",
    "check",
    "count",
    "current",
    "current_user",
    "data",
    "date",
    "default",
    "external",
    "false",
    "filter",
    "from",
    "group",
    "groups",
    "having",
    "in",
    "index",
    "is",
    "key",
    "keys",
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
    "range",
    "rank",
    "read",
    "reads",
    "regexp",
    "ref",
    "references",
    "scope",
    "select",
    "ssl",
    "system",
    "table",
    "true",
    "trigger",
    "type",
    "unique",
    "usage",
    "user",
    "value",
    "when",
    "where",
}


@dataclass
class Column:
    name: str
    type_sql: str
    not_null: bool


@dataclass
class Table:
    name: str
    columns: list[Column] = field(default_factory=list)
    primary_keys: list[tuple[str, ...]] = field(default_factory=list)
    unique_keys: list[tuple[str, ...]] = field(default_factory=list)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Materialize SQLSolver-compatible WeTune inputs from core schemas."
    )
    parser.add_argument(
        "--issues",
        default="benchmarks/core/wetune/issues/issues.tsv",
        help="WeTune issue TSV path relative to the Logos root.",
    )
    parser.add_argument(
        "--schema-dir",
        default="benchmarks/core/wetune/schemas/core",
        help="Sanitized core schema directory relative to the Logos root.",
    )
    parser.add_argument(
        "--output-dir",
        default="benchmarks/core/.generated/sqlsolver/wetune-issues",
        help="Output directory relative to the Logos root.",
    )
    parser.add_argument(
        "--case",
        action="append",
        help="Case id regex to materialize. May be repeated.",
    )
    parser.add_argument("--force", action="store_true", help="Overwrite existing case directories.")
    parser.add_argument(
        "--allow-unsafe-lowering",
        action="store_true",
        help="Materialize cases even when a query observes a type lowering that may change semantics.",
    )
    args = parser.parse_args()

    root = Path(__file__).resolve().parents[2]
    issues_path = resolve(root, args.issues)
    schema_dir = resolve(root, args.schema_dir)
    output_dir = resolve(root, args.output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    case_patterns = [re.compile(pattern) for pattern in args.case or []]

    materialized = 0
    unsupported = 0
    with issues_path.open(newline="") as handle:
        for row in csv.reader(handle, delimiter="\t"):
            case_id, app_name, rewrite_type, commit_url, before_sql, after_sql = row
            if case_patterns and not any(pattern.search(case_id) for pattern in case_patterns):
                continue
            case_dir = output_dir / case_id
            if case_dir.exists() and args.force:
                shutil.rmtree(case_dir)
            case_dir.mkdir(parents=True, exist_ok=True)

            schema_path = schema_dir / f"{app_name}.base.schema.sql"
            status = materialize_case(
                root=root,
                case_dir=case_dir,
                case_id=case_id,
                app_name=app_name,
                rewrite_type=rewrite_type,
                commit_url=commit_url,
                schema_path=schema_path,
                before_sql=before_sql,
                after_sql=after_sql,
                allow_unsafe_lowering=args.allow_unsafe_lowering,
            )
            if status == "materialized":
                materialized += 1
                print(f"materialized wetune-issues/{case_id}", file=sys.stderr)
            else:
                unsupported += 1
                print(f"unsupported wetune-issues/{case_id}: {status}", file=sys.stderr)

    print(
        f"summary: materialized={materialized} unsupported={unsupported}",
        file=sys.stderr,
    )
    return 0


def resolve(root: Path, value: str | Path) -> Path:
    path = Path(value)
    return path if path.is_absolute() else root / path


def materialize_case(
    root: Path,
    case_dir: Path,
    case_id: str,
    app_name: str,
    rewrite_type: str,
    commit_url: str,
    schema_path: Path,
    before_sql: str,
    after_sql: str,
    allow_unsafe_lowering: bool,
) -> str:
    with tempfile.TemporaryDirectory(prefix="wetune-sqlsolver-") as tmp:
        tmp_dir = Path(tmp)
        before_raw = write_text(tmp_dir / "before.raw.sql", ensure_sql_terminated(before_sql))
        after_raw = write_text(tmp_dir / "after.raw.sql", ensure_sql_terminated(after_sql))
        before_norm = tmp_dir / "before.normalized.sql"
        after_norm = tmp_dir / "after.normalized.sql"
        read_dialect = READ_DIALECT_BY_APP[app_name]

        normalize_query(root, before_raw, before_norm, read_dialect)
        normalize_query(root, after_raw, after_norm, read_dialect)

        normalized_before = before_norm.read_text()
        normalized_after = after_norm.read_text()
        schema_sql = schema_path.read_text()
        tables = parse_schema(schema_sql)
        referenced_tables = collect_referenced_tables(normalized_before + "\n" + normalized_after)
        selected_tables = tables
        constraints_path = schema_path.with_suffix(".constraints.json")
        semantic_constraints = (
            json.loads(constraints_path.read_text()) if constraints_path.exists() else {}
        )
        lowering_audit = audit_type_lowerings(
            normalized_before + "\n" + normalized_after,
            semantic_constraints,
        )
        if lowering_audit["unsafeLowerings"] and not allow_unsafe_lowering:
            write_text(
                case_dir / "metadata.json",
                json.dumps(
                    build_metadata(
                        root=root,
                        case_id=case_id,
                        app_name=app_name,
                        rewrite_type=rewrite_type,
                        commit_url=commit_url,
                        schema_path=schema_path,
                        constraints_path=constraints_path,
                        read_dialect=read_dialect,
                        referenced_tables=referenced_tables,
                        materialized_tables=[],
                        semantic_constraints=semantic_constraints,
                        rename_map={},
                        lowering_audit=lowering_audit,
                        status="unsupported",
                        unsupported_reason=(
                            "The query observes a source column whose parser-facing type "
                            "lowering may change equivalence results."
                        ),
                    ),
                    indent=2,
                    sort_keys=True,
                )
                + "\n",
            )
            return "unsafe-lowering"
        rename_map = build_rename_map(selected_tables, normalized_before + "\n" + normalized_after)

        rendered_schema = render_schema(selected_tables, rename_map)
        rendered_before = render_query(normalized_before, rename_map)
        rendered_after = render_query(normalized_after, rename_map)

        write_text(case_dir / "schema.sql", rendered_schema)
        write_text(case_dir / "sql1.sql", ensure_one_line(rendered_before))
        write_text(case_dir / "sql2.sql", ensure_one_line(rendered_after))
        write_text(
            case_dir / "metadata.json",
            json.dumps(
                build_metadata(
                    root=root,
                    case_id=case_id,
                    app_name=app_name,
                    rewrite_type=rewrite_type,
                    commit_url=commit_url,
                    schema_path=schema_path,
                    constraints_path=constraints_path,
                    read_dialect=read_dialect,
                    referenced_tables=referenced_tables,
                    materialized_tables=[table.name for table in selected_tables],
                    semantic_constraints=semantic_constraints,
                    rename_map=rename_map,
                    lowering_audit=lowering_audit,
                    status="materialized",
                    unsupported_reason=None,
                ),
                indent=2,
                sort_keys=True,
            )
            + "\n",
        )
        return "materialized"


def normalize_query(root: Path, source: Path, target: Path, read_dialect: str) -> None:
    completed = subprocess.run(
        [
            str(root / "scripts/sqlglot-normalize"),
            "--input",
            str(source),
            "--output",
            str(target),
            "--read",
            read_dialect,
            "--write",
            "postgres",
            "--identify",
        ],
        cwd=root,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if completed.returncode != 0:
        raise RuntimeError(completed.stderr)


def build_metadata(
    root: Path,
    case_id: str,
    app_name: str,
    rewrite_type: str,
    commit_url: str,
    schema_path: Path,
    constraints_path: Path,
    read_dialect: str,
    referenced_tables: set[str],
    materialized_tables: list[str],
    semantic_constraints: dict,
    rename_map: dict[str, str],
    lowering_audit: dict,
    status: str,
    unsupported_reason: str | None,
) -> dict:
    metadata = {
        "sourceBenchmark": "wetune-issues",
        "sourceCase": case_id,
        "appName": app_name,
        "rewriteType": rewrite_type,
        "commitUrl": commit_url,
        "schema": str(schema_path.relative_to(root)),
        "readDialect": read_dialect,
        "writeDialect": "postgres",
        "profile": "sqlsolver",
        "status": status,
        "referencedTables": sorted(referenced_tables),
        "materializedTables": materialized_tables,
        "semanticConstraints": {
            "source": str(constraints_path.relative_to(root))
            if constraints_path.exists()
            else None,
            "columns": count_semantic_columns(semantic_constraints),
            "typeLowerings": count_type_lowerings(semantic_constraints),
            "primaryKeys": len(semantic_constraints.get("primaryKeys", [])),
            "uniqueKeys": len(semantic_constraints.get("uniqueKeys", [])),
            "uniqueIndexes": len(semantic_constraints.get("uniqueIndexes", [])),
            "foreignKeys": len(semantic_constraints.get("foreignKeys", [])),
            "checks": len(semantic_constraints.get("checks", [])),
            "unsupportedSemanticConstraints": len(
                semantic_constraints.get("unsupportedSemanticConstraints", [])
            ),
            "includedInSqlsolverDdl": False,
            "reason": "SQLSolver's DDL frontend does not support the full constraint vocabulary.",
        },
        "typeLoweringAudit": lowering_audit,
        "renamedIdentifiers": {
            key: value for key, value in sorted(rename_map.items()) if key != value
        },
        "semanticNote": "Identifier alpha-renaming over the full application core schema; constraints are retained in the sidecar metadata and not lowered into SQLSolver DDL when unsupported by the tool frontend.",
    }
    if unsupported_reason:
        metadata["unsupportedReason"] = unsupported_reason
    return metadata


def count_semantic_columns(semantic_constraints: dict) -> int:
    return sum(
        len(table.get("columns", []))
        for table in semantic_constraints.get("semanticSchema", {}).get("tables", [])
    )


def count_type_lowerings(semantic_constraints: dict) -> int:
    return sum(
        1
        for table in semantic_constraints.get("semanticSchema", {}).get("tables", [])
        for column in table.get("columns", [])
        if normalize_spaces(column.get("sourceType", "")).upper()
        != normalize_spaces(column.get("normalizedFrontendType", "")).upper()
    )


def audit_type_lowerings(query_sql: str, semantic_constraints: dict) -> dict:
    column_index = semantic_column_index(semantic_constraints)
    aliases = collect_table_aliases(query_sql)
    referenced_tables = set(aliases.values())
    qualified_refs = collect_qualified_column_refs(query_sql, aliases)
    unqualified_refs = collect_unqualified_column_refs(
        query_sql,
        referenced_tables,
        column_index,
    )
    used_refs = sorted(qualified_refs | unqualified_refs)
    safe_lowerings = []
    unsafe_lowerings = []
    for table_name, column_name in used_refs:
        column = column_index.get((table_name, column_name))
        if not column or not is_type_lowered(column):
            continue
        aliases_for_table = sorted(
            alias for alias, table in aliases.items() if table == table_name
        )
        nullness_only = column_is_used_only_for_nullness(
            query_sql,
            table_name,
            column_name,
            aliases_for_table,
        )
        entry = {
            "table": table_name,
            "column": column_name,
            "sourceType": column.get("sourceType"),
            "normalizedFrontendType": column.get("normalizedFrontendType"),
            "sourceDeclaration": column.get("sourceDeclaration"),
            "use": "nullness-only" if nullness_only else "value-observing",
        }
        if lowering_is_safe_for_query(column, nullness_only):
            entry["reason"] = lowering_safety_reason(column, nullness_only)
            safe_lowerings.append(entry)
        else:
            entry["reason"] = lowering_unsafety_reason(column)
            unsafe_lowerings.append(entry)
    return {
        "policy": (
            "Materialize only query cases whose observed type lowerings are known to "
            "preserve this query's equivalence result. Value-observing uses of "
            "precision-sensitive or domain-specific lowerings are reported as an "
            "unsupported solver frontend case."
        ),
        "observedLowerings": len(safe_lowerings) + len(unsafe_lowerings),
        "safeLowerings": safe_lowerings,
        "unsafeLowerings": unsafe_lowerings,
    }


def semantic_column_index(semantic_constraints: dict) -> dict[tuple[str, str], dict]:
    columns = {}
    for table in semantic_constraints.get("semanticSchema", {}).get("tables", []):
        table_name = table.get("name")
        if not table_name:
            continue
        for column in table.get("columns", []):
            column_name = column.get("name")
            if column_name:
                columns[(table_name, column_name)] = column
    return columns


def is_type_lowered(column: dict) -> bool:
    return normalize_type_name(column.get("sourceType", "")) != normalize_type_name(
        column.get("normalizedFrontendType", "")
    )


def normalize_type_name(value: str) -> str:
    return normalize_spaces(value).lower()


def collect_table_aliases(sql: str) -> dict[str, str]:
    aliases = {}
    relation_re = re.compile(
        r'(?is)(?:\bFROM\b|\bJOIN\b|,)\s+"((?:""|[^"])+?)"'
        r'(?:\s+(?:AS\s+)?"?([A-Za-z_][A-Za-z0-9_]*)"?\b)?'
    )
    stopwords = {
        "where",
        "join",
        "inner",
        "left",
        "right",
        "full",
        "cross",
        "on",
        "group",
        "order",
        "having",
        "limit",
        "offset",
        "union",
        "except",
        "intersect",
    }
    for match in relation_re.finditer(sql):
        table_name = match.group(1).replace('""', '"')
        alias = match.group(2)
        aliases[table_name] = table_name
        if alias and alias.lower() not in stopwords:
            aliases[alias] = table_name
    return aliases


def collect_qualified_column_refs(sql: str, aliases: dict[str, str]) -> set[tuple[str, str]]:
    refs = set()
    for match in re.finditer(r'"((?:""|[^"])+?)"\."((?:""|[^"])+?)"', sql):
        qualifier = match.group(1).replace('""', '"')
        column_name = match.group(2).replace('""', '"')
        table_name = aliases.get(qualifier, qualifier)
        refs.add((table_name, column_name))
    return refs


def collect_unqualified_column_refs(
    sql: str,
    referenced_tables: set[str],
    column_index: dict[tuple[str, str], dict],
) -> set[tuple[str, str]]:
    refs = set()
    quoted_names = [match.group(1).replace('""', '"') for match in re.finditer(r'"((?:""|[^"])+?)"', sql)]
    for name in quoted_names:
        candidates = [
            (table, column)
            for table, column in column_index
            if column == name and table in referenced_tables
        ]
        if len(candidates) == 1:
            refs.add(candidates[0])
    return refs


def column_is_used_only_for_nullness(
    sql: str,
    table_name: str,
    column_name: str,
    aliases_for_table: list[str],
) -> bool:
    variants = {quoted_identifier(column_name)}
    for alias in aliases_for_table + [table_name]:
        variants.add(f"{quoted_identifier(alias)}.{quoted_identifier(column_name)}")

    found = False
    for variant in sorted(variants, key=len, reverse=True):
        for match in re.finditer(re.escape(variant), sql):
            found = True
            before = sql[max(0, match.start() - 16) : match.start()]
            after = sql[match.end() : match.end() + 24]
            if re.match(r"(?is)^\s+IS\s+(?:NOT\s+)?NULL\b", after):
                continue
            if re.search(r"(?is)\bNOT\s*$", before) and re.match(
                r"(?is)^\s+IS\s+NULL\b", after
            ):
                continue
            return False
    return found


def quoted_identifier(identifier: str) -> str:
    return '"' + identifier.replace('"', '""') + '"'


def lowering_is_safe_for_query(column: dict, nullness_only: bool) -> bool:
    if nullness_only:
        return True
    source_type = normalize_type_name(column.get("sourceType", ""))
    if is_temporal_type(source_type):
        return False
    if is_unsigned_integral_type(source_type):
        return False
    if is_precision_sensitive_type(source_type):
        return False
    if is_domain_specific_type(source_type):
        return False
    return True


def lowering_safety_reason(column: dict, nullness_only: bool) -> str:
    if nullness_only:
        return "The query observes only NULL/NOT NULL status, which is preserved by type lowering."
    return "The observed lowering is treated as representation-only for this query use."


def lowering_unsafety_reason(column: dict) -> str:
    source_type = normalize_type_name(column.get("sourceType", ""))
    if is_temporal_type(source_type):
        return "The query observes a temporal value after lowering; SQLSolver does not preserve full timestamp/datetime semantics."
    if is_unsigned_integral_type(source_type):
        return "The query observes an unsigned integral value after lowering without preserving the unsigned domain constraint."
    if is_precision_sensitive_type(source_type):
        return "The query observes a precision-sensitive numeric or timezone-aware type after lowering."
    return "The query observes a domain-specific source type after lowering."


def is_temporal_type(source_type: str) -> bool:
    return any(
        marker in source_type
        for marker in (
            "timestamp",
            "datetime",
            "date",
            "time",
        )
    )


def is_unsigned_integral_type(source_type: str) -> bool:
    return "unsigned" in source_type and any(
        marker in source_type
        for marker in (
            "int",
            "integer",
            "bigint",
            "smallint",
            "tinyint",
            "mediumint",
        )
    )


def is_precision_sensitive_type(source_type: str) -> bool:
    return any(
        marker in source_type
        for marker in (
            "double precision",
            "float",
            "real",
            "decimal",
            "numeric",
            "timestamp with time zone",
        )
    )


def is_domain_specific_type(source_type: str) -> bool:
    if source_type.endswith("[]"):
        return True
    return any(
        marker in source_type
        for marker in (
            "bytea",
            "json",
            "jsonb",
            "uuid",
            "inet",
            "cidr",
            "xml",
            "tsvector",
            "money",
            "enum",
        )
    )


def parse_schema(schema_sql: str) -> list[Table]:
    tables = []
    position = 0
    pattern = re.compile(r"(?is)\bCREATE\s+TABLE\b")
    while True:
        match = pattern.search(schema_sql, position)
        if not match:
            break
        open_paren = find_next_unquoted(schema_sql, "(", match.end())
        if open_paren < 0:
            break
        table_name = clean_identifier(schema_sql[match.end() : open_paren].strip())
        close_paren = find_matching_paren(schema_sql, open_paren)
        if close_paren < 0:
            break
        tables.append(parse_table(table_name, schema_sql[open_paren + 1 : close_paren]))
        position = close_paren + 1
    return tables


def parse_table(table_name: str, body: str) -> Table:
    table = Table(name=table_name)
    for item in split_top_level_commas(body):
        item = item.strip()
        if not item:
            continue
        upper = normalize_spaces(item).upper()
        if upper.startswith("PRIMARY KEY"):
            table.primary_keys.append(parse_columns_in_parens(item))
        elif re.match(r"(?is)^UNIQUE(?:\s|\()", upper):
            table.unique_keys.append(parse_columns_in_parens(item))
        else:
            match = re.match(
                r'(?is)\s*("(?:""|[^"])+?"|[A-Za-z_][A-Za-z0-9_]*)\s+(.+)$',
                item,
            )
            if not match:
                continue
            name = clean_identifier(match.group(1))
            rest = match.group(2)
            type_sql = normalize_type_for_sqlsolver(rest)
            not_null = bool(re.search(r"(?is)\bNOT\s+NULL\b", rest))
            table.columns.append(Column(name=name, type_sql=type_sql, not_null=not_null))
    return table


def normalize_type_for_sqlsolver(type_sql: str) -> str:
    lower = normalize_spaces(type_sql).lower()
    if lower.startswith("bigint"):
        return "BIGINT"
    if lower.startswith(("integer", "int", "smallint")):
        return "INT"
    if lower.startswith("boolean"):
        return "BOOLEAN"
    if lower.startswith(("float", "double", "real")):
        return "FLOAT"
    if lower.startswith(("timestamp", "datetime")):
        return "TIMESTAMP"
    if lower.startswith("date"):
        return "DATE"
    if lower.startswith("time"):
        return "TIME"
    return "VARCHAR(255)"


def collect_referenced_tables(sql: str) -> set[str]:
    tables = set()
    token_re = re.compile(
        r'(?is)"(?:""|[^"])+?"|[(),]|\bFROM\b|\bJOIN\b|\bWHERE\b|\bGROUP\b|\bORDER\b|'
        r'\bHAVING\b|\bLIMIT\b|\bOFFSET\b|\bUNION\b|\bEXCEPT\b|\bINTERSECT\b|\bON\b|'
        r'\bCROSS\b|\bINNER\b|\bLEFT\b|\bRIGHT\b|\bFULL\b|\bOUTER\b|\bAS\b'
    )
    expect_table = False
    in_from_list = False
    for match in token_re.finditer(sql):
        token = match.group(0)
        upper = token.upper()
        if upper in {"FROM", "JOIN"}:
            expect_table = True
            in_from_list = True
        elif upper in {"WHERE", "GROUP", "ORDER", "HAVING", "LIMIT", "OFFSET", "UNION", "EXCEPT", "INTERSECT", "ON"}:
            expect_table = False
            in_from_list = False
        elif token == "," and in_from_list:
            expect_table = True
        elif token.startswith('"') and expect_table:
            tables.add(clean_identifier(token))
            expect_table = False
            in_from_list = True
    return tables


def build_rename_map(tables: list[Table], query_sql: str) -> dict[str, str]:
    identifiers = set(re.findall(r'"((?:""|[^"])+?)"', query_sql))
    for table in tables:
        identifiers.add(table.name)
        for column in table.columns:
            identifiers.add(column.name)
        for key in table.primary_keys + table.unique_keys:
            identifiers.update(key)

    used = {identifier for identifier in identifiers if is_sqlsolver_safe(identifier)}
    rename_map = {}
    for identifier in sorted(identifiers):
        cleaned = identifier.replace('""', '"')
        if is_sqlsolver_safe(cleaned):
            rename_map[cleaned] = cleaned
            continue
        candidate = make_safe_identifier(cleaned)
        base = candidate
        suffix = 2
        while candidate.lower() in {value.lower() for value in used}:
            candidate = f"{base}_{suffix}"
            suffix += 1
        rename_map[cleaned] = candidate
        used.add(candidate)
    return rename_map


def render_schema(tables: list[Table], rename_map: dict[str, str]) -> str:
    statements = []
    for table in tables:
        items = []
        for column in table.columns:
            name = rename_identifier(column.name, rename_map)
            items.append(
                f"  {name} {column.type_sql}{' NOT NULL' if column.not_null else ''}"
            )
        for key in table.primary_keys:
            if not key:
                continue
            items.append(
                "  PRIMARY KEY ("
                + ", ".join(rename_identifier(column, rename_map) for column in key)
                + ")"
            )
        for key in table.unique_keys:
            if not key:
                continue
            items.append(
                "  UNIQUE ("
                + ", ".join(rename_identifier(column, rename_map) for column in key)
                + ")"
            )
        statements.append(
            f"CREATE TABLE {rename_identifier(table.name, rename_map)} (\n"
            + ",\n".join(items)
            + "\n);"
        )
    return "\n\n".join(statements) + ("\n" if statements else "")


def render_query(sql: str, rename_map: dict[str, str]) -> str:
    return re.sub(
        r'"((?:""|[^"])+?)"',
        lambda match: rename_identifier(match.group(1).replace('""', '"'), rename_map),
        sql,
    )


def rename_identifier(identifier: str, rename_map: dict[str, str]) -> str:
    return rename_map.get(identifier, make_safe_identifier(identifier))


def is_sqlsolver_safe(identifier: str) -> bool:
    return bool(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", identifier)) and (
        identifier.lower() not in SQLSOLVER_RESERVED
    )


def make_safe_identifier(identifier: str) -> str:
    candidate = re.sub(r"[^A-Za-z0-9_]+", "_", identifier).strip("_")
    if not candidate or not re.match(r"[A-Za-z_]", candidate):
        candidate = f"c_{candidate}"
    if candidate.lower() in SQLSOLVER_RESERVED:
        candidate = f"{candidate}_x"
    return candidate


def split_top_level_commas(text: str) -> list[str]:
    parts = []
    start = 0
    quote = None
    depth = 0
    index = 0
    while index < len(text):
        char = text[index]
        if quote:
            if char == quote:
                quote = None
        elif char == '"':
            quote = char
        elif char == "(":
            depth += 1
        elif char == ")":
            depth = max(0, depth - 1)
        elif char == "," and depth == 0:
            parts.append(text[start:index])
            start = index + 1
        index += 1
    parts.append(text[start:])
    return parts


def parse_columns_in_parens(item: str) -> tuple[str, ...]:
    open_paren = find_next_unquoted(item, "(", 0)
    close_paren = find_matching_paren(item, open_paren) if open_paren >= 0 else -1
    if open_paren < 0 or close_paren < 0:
        return ()
    columns = []
    for part in split_top_level_commas(item[open_paren + 1 : close_paren]):
        match = re.match(r'(?is)\s*("(?:""|[^"])+?"|[A-Za-z_][A-Za-z0-9_]*)', part)
        if match:
            columns.append(clean_identifier(match.group(1)))
    return tuple(columns)


def find_next_unquoted(text: str, needle: str, start: int) -> int:
    quote = None
    for index in range(start, len(text)):
        char = text[index]
        if quote:
            if char == quote:
                quote = None
        elif char == '"':
            quote = char
        elif char == needle:
            return index
    return -1


def find_matching_paren(text: str, open_index: int) -> int:
    quote = None
    depth = 0
    index = open_index
    while index < len(text):
        char = text[index]
        if quote:
            if char == quote:
                quote = None
        elif char == '"':
            quote = char
        elif char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
            if depth == 0:
                return index
        index += 1
    return -1


def clean_identifier(identifier: str) -> str:
    identifier = identifier.strip()
    if identifier.startswith('"') and identifier.endswith('"'):
        return identifier[1:-1].replace('""', '"')
    return identifier


def normalize_spaces(value: str) -> str:
    return re.sub(r"\s+", " ", value).strip()


def ensure_sql_terminated(sql: str) -> str:
    stripped = sql.strip()
    return stripped if stripped.endswith(";") else stripped + ";\n"


def ensure_one_line(sql: str) -> str:
    sql = re.sub(r";\s*$", "", sql.strip())
    return re.sub(r"\s+", " ", sql) + "\n"


def write_text(path: Path, content: str) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content)
    return path


if __name__ == "__main__":
    raise SystemExit(main())
