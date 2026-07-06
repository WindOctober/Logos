#!/usr/bin/env python3
import argparse
import importlib.util
from importlib.machinery import SourceFileLoader
import json
import re
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[3]
EXPORTER_PATH = ROOT / "scripts/export-benchmark-ir"
DEFAULT_CONFIG = "benchmarks/core/ingestion.json"
DEFAULT_OUTPUT = "benchmarks/core/.generated/qed"


@dataclass
class Column:
    name: str
    type_sql: str
    not_null: bool


@dataclass
class Table:
    name: str
    columns: list[Column] = field(default_factory=list)


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Materialize core benchmark cases as QED inputs. Each case directory "
            "contains qed.sql, metadata.json, and qed.json when QED's parser accepts it."
        )
    )
    parser.add_argument("--config", default=DEFAULT_CONFIG)
    parser.add_argument("--output-dir", default=DEFAULT_OUTPUT)
    parser.add_argument(
        "--target",
        choices=("all", "wetune", "nonwetune"),
        default="all",
        help="Benchmark subset to materialize.",
    )
    parser.add_argument("--benchmark", action="append")
    parser.add_argument("--case", action="append", help="Case id regex. May be repeated.")
    parser.add_argument("--limit", type=int)
    parser.add_argument("--force", action="store_true")
    parser.add_argument(
        "--skip-parser",
        action="store_true",
        help="Only write qed.sql/metadata.json; do not invoke PaperTools/scripts/qed-parser.",
    )
    args = parser.parse_args()

    exporter = load_exporter()
    config = json.loads(resolve_path(args.config).read_text())
    output_dir = resolve_path(args.output_dir)
    selected = set(args.benchmark or [])
    case_patterns = [re.compile(pattern) for pattern in args.case or []]

    if args.force:
        remove_selected_outputs(output_dir, args.target)
    output_dir.mkdir(parents=True, exist_ok=True)

    materialized = 0
    parser_failed = 0
    failed = 0
    for benchmark in config["benchmarks"]:
        benchmark_id = benchmark["id"]
        if not target_includes(args.target, benchmark_id):
            continue
        if selected and benchmark_id not in selected:
            continue
        for case in exporter.iter_cases(config, benchmark):
            if case_patterns and not case_matches(case, benchmark_id, case_patterns):
                continue
            if args.limit is not None and materialized >= args.limit:
                return finish(materialized, parser_failed, failed)
            try:
                status = materialize_case(config, case, output_dir, skip_parser=args.skip_parser)
                materialized += 1
                if status != "parsed":
                    parser_failed += 1
                print(f"materialized {benchmark_id}/{case.case_id}: {status}", file=sys.stderr)
            except Exception as exc:
                failed += 1
                print(f"failed {benchmark_id}/{case.case_id}: {exc}", file=sys.stderr)
    return finish(materialized, parser_failed, failed)


def finish(materialized: int, parser_failed: int, failed: int) -> int:
    print(
        f"summary: materialized={materialized} parser_failed={parser_failed} failed={failed}",
        file=sys.stderr,
    )
    return 1 if failed else 0


def remove_selected_outputs(output_dir: Path, target: str) -> None:
    if target == "all":
        if output_dir.exists():
            shutil.rmtree(output_dir)
        return
    selected = output_dir / ("wetune-issues" if target == "wetune" else "nonwetune-flat")
    if selected.exists():
        shutil.rmtree(selected)


def target_includes(target: str, benchmark_id: str) -> bool:
    if target == "all":
        return True
    if target == "wetune":
        return benchmark_id == "wetune-issues"
    return benchmark_id != "wetune-issues"


def case_matches(case: Any, benchmark_id: str, patterns: list[re.Pattern]) -> bool:
    flat_case_id = flat_id(benchmark_id, case.case_id)
    return any(pattern.search(case.case_id) or pattern.search(flat_case_id) for pattern in patterns)


def load_exporter():
    loader = SourceFileLoader("logos_export_benchmark_ir", str(EXPORTER_PATH))
    spec = importlib.util.spec_from_loader("logos_export_benchmark_ir", loader)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load exporter from {EXPORTER_PATH}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def resolve_path(path: str | Path) -> Path:
    candidate = Path(path)
    return candidate if candidate.is_absolute() else ROOT / candidate


def materialize_case(
    config: dict[str, Any],
    case: Any,
    output_dir: Path,
    skip_parser: bool,
) -> str:
    benchmark_id = case.benchmark["id"]
    flat_case_id = flat_id(benchmark_id, case.case_id)
    case_dir = output_dir / ("wetune-issues" if benchmark_id == "wetune-issues" else "nonwetune-flat") / flat_case_id
    if benchmark_id == "wetune-issues":
        case_dir = output_dir / "wetune-issues" / case.case_id
    case_dir.mkdir(parents=True, exist_ok=True)

    read_dialect = case.read_dialect or case.benchmark.get("readDialect") or "postgres"
    write_dialect = "postgres"
    adapter = case.benchmark.get("adapter", config["defaults"].get("adapter", "none"))

    with tempfile.TemporaryDirectory(prefix="logos-qed-") as tmp:
        tmp_dir = Path(tmp)
        before_sql, before_report = normalize_query(
            tmp_dir=tmp_dir,
            name="before",
            sql=case.before_sql,
            read=read_dialect,
            write=write_dialect,
            normalize=adapter == "sqlglot" or benchmark_id == "wetune-issues",
        )
        after_sql, after_report = normalize_query(
            tmp_dir=tmp_dir,
            name="after",
            sql=case.after_sql,
            read=read_dialect,
            write=write_dialect,
            normalize=adapter == "sqlglot" or benchmark_id == "wetune-issues",
        )
        quote_schema_identifiers = adapter == "sqlglot" or benchmark_id == "wetune-issues"
        schema_sql = render_qed_schema(
            case.schema_sql,
            before_sql + "\n" + after_sql,
            quote_identifiers=quote_schema_identifiers,
        )

    qed_sql = schema_sql + "\n" + ensure_sql_terminated(before_sql) + ensure_sql_terminated(after_sql)
    qed_sql = patch_qed_interval_precision(qed_sql)
    write_text(case_dir / "qed.sql", qed_sql)

    parser_status = {"skipped": True} if skip_parser else run_qed_parser(case_dir / "qed.sql")
    parser_problem = None if skip_parser else classify_qed_parser_problem(parser_status)
    if parser_problem and (case_dir / "qed.json").exists():
        (case_dir / "qed.json").unlink()
        parser_status["jsonExists"] = False
    status = (
        "not-parsed"
        if skip_parser
        else ("parsed" if parser_status.get("jsonExists") and parser_problem is None else "parser-error")
    )

    write_text(
        case_dir / "metadata.json",
        json.dumps(
            {
                **build_metadata(config, case, flat_case_id),
                "profile": "qed",
                "status": status,
                "qedInput": "qed.sql",
                "qedJson": "qed.json" if (case_dir / "qed.json").exists() else None,
                "normalizationForSolverRun": {
                    "schema": {
                        "renderer": "logos-qed-schema-renderer",
                        "semanticNote": (
                            "DDL is simplified to QED parser-supported CREATE TABLE "
                            "statements. Identifiers are double-quoted and unsupported "
                            "constraints/indexes are omitted."
                        ),
                    },
                    "before": before_report,
                    "after": after_report,
                },
                "parser": parser_status,
                "parserProblem": parser_problem,
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
    )
    return status


def flat_id(benchmark_id: str, case_id: str) -> str:
    return f"{benchmark_id}__{case_id}"


def normalize_query(
    tmp_dir: Path,
    name: str,
    sql: str,
    read: str,
    write: str,
    normalize: bool,
) -> tuple[str, dict[str, Any]]:
    source = write_text(tmp_dir / f"{name}.source.sql", ensure_sql_terminated(sql))
    if not normalize:
        return patch_qed_sql(strip_sql_comments(source.read_text())), {"skipped": True}

    target = tmp_dir / f"{name}.normalized.sql"
    report = tmp_dir / f"{name}.normalization.json"
    command = [
        str(ROOT / "benchmarks/scripts/sqlglot-normalize"),
        "--input",
        str(source),
        "--output",
        str(target),
        "--report",
        str(report),
        "--read",
        read,
        "--write",
        write,
        "--identify",
    ]
    completed = subprocess.run(
        command,
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if completed.returncode != 0:
        raise RuntimeError(completed.stderr)
    return patch_qed_sql(target.read_text()), {
        "command": command,
        "returnCode": completed.returncode,
        "stderrTail": tail(completed.stderr),
        "report": json.loads(report.read_text()),
    }


def run_qed_parser(sql_path: Path) -> dict[str, Any]:
    case_dir = sql_path.parent
    for generated in ("qed.json", "qed.rkt"):
        path = case_dir / generated
        if path.exists():
            path.unlink()
    command = [str(ROOT.parent / "PaperTools/scripts/qed-parser"), str(sql_path)]
    started = subprocess.run(
        command,
        cwd=ROOT.parent,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    write_text(case_dir / "qed-parser.stdout.log", started.stdout)
    write_text(case_dir / "qed-parser.stderr.log", started.stderr)
    return {
        "command": command,
        "returnCode": started.returncode,
        "jsonExists": (case_dir / "qed.json").exists(),
        "rktExists": (case_dir / "qed.rkt").exists(),
        "stdoutTail": tail(started.stdout),
        "stderrTail": tail(started.stderr),
    }


def classify_qed_parser_problem(parser_status: dict[str, Any]) -> dict[str, str] | None:
    text = "\n".join(
        str(parser_status.get(key, ""))
        for key in ("stdoutTail", "stderrTail")
    )
    if not text.strip():
        return None
    patterns = [
        ("unsupported", r"UnsupportedOperationException:\s*([^\n]+)"),
        ("unsupported", r"Not supported [^\n]+"),
        ("parser-error", r"CalciteContextException:\s*([^\n]+)"),
        ("parser-error", r"ParseException:\s*([^\n]+)"),
        ("parser-error", r"Encountered [^\n]+"),
        ("parser-error", r"Correlation ID not declared"),
        ("parser-error", r"NullPointerException:\s*([^\n]+)"),
        ("parser-error", r"Exception:\s*([^\n]+)"),
        ("parser-error", r"RuntimeException:\s*([^\n]+)"),
    ]
    for kind, pattern in patterns:
        match = re.search(pattern, text, re.IGNORECASE)
        if match:
            return {
                "kind": kind,
                "message": match.group(1).strip() if match.groups() else match.group(0).strip(),
            }
    return None


def build_metadata(config: dict[str, Any], case: Any, flat_case_id: str) -> dict[str, Any]:
    defaults = config["defaults"]
    benchmark = case.benchmark
    return {
        "sourceBenchmark": benchmark["id"],
        "sourceCase": case.case_id,
        "flatCaseId": flat_case_id,
        "source": case.source_metadata,
        "schemaScope": benchmark["schemaScope"],
        "constraintScope": benchmark.get("constraintScope", "none"),
        "constraints": case.constraints,
        "adapter": benchmark.get("adapter", defaults.get("adapter", "none")),
        "sourceDialect": case.source_dialect or benchmark.get("sourceDialect"),
        "readDialect": case.read_dialect or benchmark.get("readDialect"),
        "writeDialect": "postgres",
        "frontendTargetDialectPurpose": "qed-calcite-parser",
        "semanticProfile": benchmark.get("semanticProfile", defaults["semanticProfile"]),
        "bagSemantics": benchmark.get("bagSemantics", defaults["bagSemantics"]),
        "nullSemantics": benchmark.get("nullSemantics", defaults["nullSemantics"]),
        "featureTags": case.feature_tags,
    }


def render_qed_schema(schema_sql: str, query_sql: str, quote_identifiers: bool) -> str:
    tables = prune_schema_columns(parse_schema(schema_sql), query_sql)
    rendered = []
    for table in tables:
        columns = []
        for column in table.columns:
            suffix = " NOT NULL" if column.not_null else ""
            columns.append(
                f"  {render_identifier(column.name, quote_identifiers)} {column.type_sql}{suffix}"
            )
        if not columns:
            continue
        rendered.append(
            f"CREATE TABLE {render_identifier(table.name, quote_identifiers)} (\n"
            + ",\n".join(columns)
            + "\n);\n"
        )
    return "\n".join(rendered)


def prune_schema_columns(tables: list[Table], query_sql: str) -> list[Table]:
    aliases = collect_table_aliases(query_sql)
    referenced_tables = {table.lower() for table in aliases.values()}
    referenced_tables.update(
        table.name.lower() for table in tables if identifier_is_referenced(query_sql, table.name)
    )
    refs = collect_column_refs(query_sql, aliases)
    refs_lower = {(table.lower(), column.lower()) for table, column in refs}
    referenced_columns = {column.lower() for _, column in refs}

    by_name = {table.name: table for table in tables}
    pruned = []
    for table in tables:
        if referenced_tables and table.name.lower() not in referenced_tables:
            continue
        columns = [
            column
            for column in table.columns
            if (table.name.lower(), column.name.lower()) in refs_lower
            or column.name.lower() in referenced_columns
            or unqualified_column_is_referenced(query_sql, column.name)
        ]
        if not columns and table.columns:
            columns = [preferred_dummy_column(table)]
        pruned.append(Table(name=table.name, columns=columns))
    if pruned:
        return pruned
    return list(by_name.values())


def unqualified_column_is_referenced(sql: str, column_name: str) -> bool:
    return identifier_is_referenced(sql, column_name, forbid_preceding_dot=True)


def identifier_is_referenced(sql: str, identifier: str, forbid_preceding_dot: bool = False) -> bool:
    quoted = quote_identifier(identifier)
    quoted_prefix = r"(?<!\.)" if forbid_preceding_dot else ""
    if re.search(rf"{quoted_prefix}{re.escape(quoted)}(?!\s*\.)", sql):
        return True
    bare_prefix = r"(?<![.A-Za-z0-9_])" if forbid_preceding_dot else r"(?<![A-Za-z0-9_])"
    return bool(re.search(rf"(?is){bare_prefix}{re.escape(identifier)}(?![A-Za-z0-9_])", sql))


def preferred_dummy_column(table: Table) -> Column:
    for column in table.columns:
        if column.type_sql.upper() not in {"VARCHAR(255)", "CHAR", "CHAR(255)"}:
            return column
    return table.columns[0]


def collect_table_aliases(sql: str) -> dict[str, str]:
    aliases: dict[str, str] = {}
    relation_re = re.compile(
        r'(?is)(?:\bFROM\b|\bJOIN\b)\s*'
        r'("(?:""|[^"])+?"|[A-Za-z_][A-Za-z0-9_]*)'
        r'(?:\s+(?:AS\s+)?("(?:""|[^"])+?"|[A-Za-z_][A-Za-z0-9_]*))?'
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
        table_name = clean_identifier(match.group(1))
        alias = clean_identifier(match.group(2)) if match.group(2) else None
        aliases[table_name] = table_name
        if alias and alias.lower() not in stopwords:
            aliases[alias] = table_name
    aliases.update(collect_comma_from_aliases(sql, stopwords))
    return aliases


def collect_comma_from_aliases(sql: str, stopwords: set[str]) -> dict[str, str]:
    aliases: dict[str, str] = {}
    from_re = re.compile(
        r"(?is)\bFROM\b(?P<body>.*?)(?=\bWHERE\b|\bGROUP\b|\bORDER\b|\bHAVING\b|\bLIMIT\b|\bUNION\b|\bEXCEPT\b|\bINTERSECT\b|$)"
    )
    for match in from_re.finditer(sql):
        for item in split_top_level_commas(match.group("body")):
            item = item.strip()
            if not item or item.startswith("("):
                continue
            rel = re.match(
                r'(?is)^("(?:""|[^"])+?"|[A-Za-z_][A-Za-z0-9_]*)(?:\s+(?:AS\s+)?("(?:""|[^"])+?"|[A-Za-z_][A-Za-z0-9_]*))?',
                item,
            )
            if not rel:
                continue
            table_name = clean_identifier(rel.group(1))
            alias = clean_identifier(rel.group(2)) if rel.group(2) else None
            aliases[table_name] = table_name
            if alias and alias.lower() not in stopwords:
                aliases[alias] = table_name
    return aliases


def collect_column_refs(sql: str, aliases: dict[str, str]) -> set[tuple[str, str]]:
    refs: set[tuple[str, str]] = set()
    for match in re.finditer(r'"((?:""|[^"])+?)"\."((?:""|[^"])+?)"', sql):
        qualifier = match.group(1).replace('""', '"')
        column = match.group(2).replace('""', '"')
        refs.add((aliases.get(qualifier, qualifier), column))
    for match in re.finditer(
        r"(?is)\b([A-Za-z_][A-Za-z0-9_]*)\.([A-Za-z_][A-Za-z0-9_]*)\b",
        sql,
    ):
        qualifier, column = match.group(1), match.group(2)
        refs.add((aliases.get(qualifier, qualifier), column))
    return refs


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
        if upper.startswith(("PRIMARY KEY", "FOREIGN KEY", "UNIQUE", "CHECK", "CONSTRAINT", "KEY", "INDEX")):
            continue
        match = re.match(
            r'(?is)\s*("(?:""|[^"])+?"|`(?:``|[^`])+?`|[A-Za-z_][A-Za-z0-9_]*)\s+(.+)$',
            item,
        )
        if not match:
            continue
        name = clean_identifier(match.group(1))
        rest = match.group(2)
        table.columns.append(
            Column(
                name=name,
                type_sql=normalize_type_for_qed(rest),
                not_null=bool(re.search(r"(?is)\bNOT\s+NULL\b", rest)),
            )
        )
    return table


def normalize_type_for_qed(type_sql: str) -> str:
    lower = normalize_spaces(type_sql).lower()
    if lower.startswith("bigint"):
        return "BIGINT"
    if lower.startswith(("integer", "int", "smallint", "tinyint", "mediumint")):
        return "INTEGER"
    if lower.startswith(("decimal", "numeric")):
        return "DECIMAL"
    if lower.startswith(("double", "float", "real")):
        return "DOUBLE"
    if lower.startswith(("bool", "boolean")):
        return "BOOLEAN"
    if lower.startswith("date"):
        return "DATE"
    if lower.startswith(("timestamp", "datetime", "time")):
        return "TIMESTAMP"
    if lower.startswith(("char", "varchar", "character", "text", "string")):
        return "VARCHAR(255)"
    return "VARCHAR(255)"


def patch_qed_sql(sql: str) -> str:
    return patch_qed_interval_precision(strip_sql_comments(sql))


def patch_qed_interval_precision(sql: str) -> str:
    def repl(match: re.Match) -> str:
        value = match.group(1)
        precision = len(value)
        return f"INTERVAL '{value}' DAY({precision})"

    return re.sub(r"(?i)INTERVAL\s+'([0-9]{3,})'\s+DAY(?!\s*\()", repl, sql)


def ensure_sql_terminated(sql: str) -> str:
    stripped = sql.strip()
    if not stripped:
        return "\n"
    return stripped if stripped.endswith(";") else stripped + ";\n"


def quote_identifier(identifier: str) -> str:
    return '"' + identifier.replace('"', '""') + '"'


def render_identifier(identifier: str, quote: bool) -> str:
    if quote or not re.match(r"^[A-Za-z_][A-Za-z0-9_]*$", identifier):
        return quote_identifier(identifier)
    return identifier


def clean_identifier(value: str) -> str:
    value = value.strip()
    if "." in value:
        value = value.split(".")[-1]
    if value.startswith('"') and value.endswith('"'):
        return value[1:-1].replace('""', '"')
    if value.startswith("`") and value.endswith("`"):
        return value[1:-1].replace("``", "`")
    return value


def split_top_level_commas(text: str) -> list[str]:
    parts = []
    start = 0
    depth = 0
    in_single = False
    in_double = False
    in_backtick = False
    index = 0
    while index < len(text):
        char = text[index]
        next_char = text[index + 1] if index + 1 < len(text) else ""
        if char == "'" and not in_double and not in_backtick:
            if in_single and next_char == "'":
                index += 2
                continue
            in_single = not in_single
        elif char == '"' and not in_single and not in_backtick:
            in_double = not in_double
        elif char == "`" and not in_single and not in_double:
            in_backtick = not in_backtick
        elif not in_single and not in_double and not in_backtick:
            if char == "(":
                depth += 1
            elif char == ")":
                depth -= 1
            elif char == "," and depth == 0:
                parts.append(text[start:index])
                start = index + 1
        index += 1
    parts.append(text[start:])
    return parts


def find_next_unquoted(text: str, target: str, start: int) -> int:
    in_single = False
    in_double = False
    in_backtick = False
    index = start
    while index < len(text):
        char = text[index]
        next_char = text[index + 1] if index + 1 < len(text) else ""
        if char == "'" and not in_double and not in_backtick:
            if in_single and next_char == "'":
                index += 2
                continue
            in_single = not in_single
        elif char == '"' and not in_single and not in_backtick:
            in_double = not in_double
        elif char == "`" and not in_single and not in_double:
            in_backtick = not in_backtick
        elif char == target and not in_single and not in_double and not in_backtick:
            return index
        index += 1
    return -1


def find_matching_paren(text: str, open_index: int) -> int:
    depth = 0
    in_single = False
    in_double = False
    in_backtick = False
    index = open_index
    while index < len(text):
        char = text[index]
        next_char = text[index + 1] if index + 1 < len(text) else ""
        if char == "'" and not in_double and not in_backtick:
            if in_single and next_char == "'":
                index += 2
                continue
            in_single = not in_single
        elif char == '"' and not in_single and not in_backtick:
            in_double = not in_double
        elif char == "`" and not in_single and not in_double:
            in_backtick = not in_backtick
        elif not in_single and not in_double and not in_backtick:
            if char == "(":
                depth += 1
            elif char == ")":
                depth -= 1
                if depth == 0:
                    return index
        index += 1
    return -1


def normalize_spaces(value: str) -> str:
    return re.sub(r"\s+", " ", value.strip())


def strip_sql_comments(sql: str) -> str:
    output: list[str] = []
    index = 0
    in_single_quote = False
    in_double_quote = False
    in_line_comment = False
    in_block_comment = False
    while index < len(sql):
        char = sql[index]
        next_char = sql[index + 1] if index + 1 < len(sql) else ""

        if in_line_comment:
            if char == "\n":
                in_line_comment = False
                output.append(char)
            index += 1
            continue

        if in_block_comment:
            if char == "*" and next_char == "/":
                in_block_comment = False
                output.append(" ")
                index += 2
                continue
            index += 1
            continue

        if not in_single_quote and not in_double_quote:
            if char == "-" and next_char == "-":
                in_line_comment = True
                output.append(" ")
                index += 2
                continue
            if char == "/" and next_char == "*":
                in_block_comment = True
                output.append(" ")
                index += 2
                continue

        if char == "'" and not in_double_quote:
            if in_single_quote and next_char == "'":
                output.append(char)
                output.append(next_char)
                index += 2
                continue
            in_single_quote = not in_single_quote
        elif char == '"' and not in_single_quote:
            in_double_quote = not in_double_quote

        output.append(char)
        index += 1
    return "".join(output)


def write_text(path: Path, content: str) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content)
    return path


def tail(text: str, limit: int = 4000) -> str:
    return text[-limit:]


if __name__ == "__main__":
    raise SystemExit(main())
