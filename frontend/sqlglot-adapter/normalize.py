#!/usr/bin/env python3
import argparse
import json
import re
import sys
from pathlib import Path

import sqlglot


def patch_tpcds_intervals(sql: str, normalizations: list[dict]) -> str:
    pattern = re.compile(r"(?i)([+-]\s*)(\d+)\s+days\b")

    def repl(match: re.Match) -> str:
        normalizations.append(
            {
                "kind": "tpcds_interval_days",
                "source": match.group(0),
                "target": f"{match.group(1).strip()} INTERVAL '{match.group(2)}' DAY",
            }
        )
        return f"{match.group(1)}INTERVAL '{match.group(2)}' DAY"

    return pattern.sub(repl, sql)


def patch_timestamp_with_time_zone_for_sqlglot(sql: str, normalizations: list[dict]) -> str:
    pattern = re.compile(
        r"(?i)TIMESTAMP\s*(\(\s*[0-6]\s*\))?\s+WITH\s+(?:LOCAL\s+)?TIME\s+ZONE"
    )

    def repl(match: re.Match) -> str:
        precision = match.group(1) or ""
        target = f"TIMESTAMPTZ{precision}"
        normalizations.append(
            {
                "kind": "timestamp_with_time_zone_parse_patch",
                "source": match.group(0),
                "target": target,
            }
        )
        return target

    return pattern.sub(repl, sql)


def patch_timestamptz_for_calcite(sql: str, normalizations: list[dict]) -> str:
    pattern = re.compile(r"(?i)\bTIMESTAMPTZ\s*(\(\s*[0-6]\s*\))?")

    def repl(match: re.Match) -> str:
        precision = match.group(1) or ""
        target = f"TIMESTAMP{precision} WITH TIME ZONE"
        normalizations.append(
            {
                "kind": "calcite_timestamptz_type",
                "source": match.group(0),
                "target": target,
            }
        )
        return target

    return pattern.sub(repl, sql)


def patch_calcite_interval_literals(sql: str, normalizations: list[dict]) -> str:
    pattern = re.compile(
        r"(?i)INTERVAL\s+'([0-9]+)\s+"
        r"(DAY|DAYS|HOUR|HOURS|MINUTE|MINUTES|MONTH|MONTHS|QUARTER|QUARTERS|SECOND|SECONDS|WEEK|WEEKS|YEAR|YEARS)'"
    )

    def repl(match: re.Match) -> str:
        unit = match.group(2).upper()
        if unit.endswith("S"):
            unit = unit[:-1]
        normalizations.append(
            {
                "kind": "calcite_interval_literal",
                "source": match.group(0),
                "target": f"INTERVAL '{match.group(1)}' {unit}",
            }
        )
        return f"INTERVAL '{match.group(1)}' {unit}"

    return pattern.sub(repl, sql)


def patch_sqlglot_days_alias(sql: str, normalizations: list[dict]) -> str:
    pattern = re.compile(r"(?i)([+-]\s*)([0-9]+)\s+AS\s+\"?days\"?")

    def repl(match: re.Match) -> str:
        normalizations.append(
            {
                "kind": "sqlglot_days_alias",
                "source": match.group(0),
                "target": f"{match.group(1)}INTERVAL '{match.group(2)}' DAY",
            }
        )
        return f"{match.group(1)}INTERVAL '{match.group(2)}' DAY"

    return pattern.sub(repl, sql)


def patch_date_column_integer_arithmetic(sql: str, normalizations: list[dict]) -> str:
    identifier = r'(?:"[^"]+"|[A-Za-z_][A-Za-z0-9_]*)'
    qualified_identifier = rf"{identifier}(?:\s*\.\s*{identifier})?"
    pattern = re.compile(rf"(?i)({qualified_identifier})\s*([+-])\s*([0-9]+)")

    def repl(match: re.Match) -> str:
        column = match.group(1)
        normalized_column = column.replace('"', "").replace(" ", "").lower()
        leaf = normalized_column.split(".")[-1]
        if not leaf.endswith("_date") and leaf != "d_date":
            return match.group(0)
        normalizations.append(
            {
                "kind": "date_column_integer_arithmetic",
                "source": match.group(0),
                "target": f"{column} {match.group(2)} INTERVAL '{match.group(3)}' DAY",
            }
        )
        return f"{column} {match.group(2)} INTERVAL '{match.group(3)}' DAY"

    return pattern.sub(repl, sql)


def patch_cast_date_integer_arithmetic(sql: str, normalizations: list[dict]) -> str:
    pattern = re.compile(
        r"(?i)(CAST\s*\([^)]*?\s+AS\s+DATE\s*\))\s*([+-])\s*([0-9]+)(?!\s*(?:DAY|DAYS|'))"
    )

    def repl(match: re.Match) -> str:
        normalizations.append(
            {
                "kind": "cast_date_integer_arithmetic",
                "source": match.group(0),
                "target": f"{match.group(1)} {match.group(2)} INTERVAL '{match.group(3)}' DAY",
            }
        )
        return f"{match.group(1)} {match.group(2)} INTERVAL '{match.group(3)}' DAY"

    return pattern.sub(repl, sql)


def normalize_sql(
    sql: str,
    read: str,
    write: str,
    identify: bool,
    pretty: bool,
    apply_patches: bool,
) -> tuple[str, dict]:
    normalizations: list[dict] = []
    patched = patch_tpcds_intervals(sql, normalizations) if apply_patches else sql
    if apply_patches:
        patched = patch_timestamp_with_time_zone_for_sqlglot(patched, normalizations)

    report = {
        "readDialect": read,
        "writeDialect": write,
        "identify": identify,
        "pretty": pretty,
        "sqlglotVersion": sqlglot.__version__,
        "normalizations": normalizations,
        "errors": [],
    }

    try:
        statements = sqlglot.transpile(
            patched,
            read=read,
            write=write,
            identify=identify,
            pretty=pretty,
        )
    except Exception as exc:
        report["errors"].append(
            {
                "stage": "sqlglot.transpile",
                "type": type(exc).__name__,
                "message": str(exc),
            }
        )
        return "", report

    effective_statements = [stmt.strip() for stmt in statements if is_effective_statement(stmt)]
    normalized = ";\n\n".join(effective_statements)
    if normalized:
        normalized += ";\n"

    if apply_patches:
        normalized = patch_timestamptz_for_calcite(normalized, normalizations)
        normalized = patch_sqlglot_days_alias(normalized, normalizations)
        normalized = patch_calcite_interval_literals(normalized, normalizations)
        normalized = patch_cast_date_integer_arithmetic(normalized, normalizations)
        normalized = patch_date_column_integer_arithmetic(normalized, normalizations)

    report["statementCount"] = len(effective_statements)
    return normalized, report


def is_effective_statement(statement: str) -> bool:
    stripped = statement.strip()
    if not stripped:
        return False
    without_block_comments = re.sub(r"(?s)/\*.*?\*/", "", stripped).strip()
    without_line_comments = re.sub(r"(?m)^\s*--.*$", "", without_block_comments).strip()
    return bool(without_line_comments)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Normalize vendor SQL dialects into Calcite-friendly SQL with SQLGlot."
    )
    parser.add_argument("--input", required=True, help="Input SQL file.")
    parser.add_argument("--output", required=True, help="Output normalized SQL file.")
    parser.add_argument("--report", help="Optional JSON normalization report.")
    parser.add_argument("--read", default="tsql", help="Input SQLGlot dialect.")
    parser.add_argument("--write", default="postgres", help="Output SQLGlot dialect.")
    parser.add_argument(
        "--identify",
        action="store_true",
        help="Quote identifiers in the output to avoid reserved-word collisions.",
    )
    parser.add_argument("--pretty", action="store_true", help="Pretty-print output SQL.")
    parser.add_argument(
        "--no-patches",
        action="store_true",
        help="Disable Logos' small Calcite-compatibility patches.",
    )
    args = parser.parse_args()

    sql = Path(args.input).read_text()
    normalized, report = normalize_sql(
        sql=sql,
        read=args.read,
        write=args.write,
        identify=args.identify,
        pretty=args.pretty,
        apply_patches=not args.no_patches,
    )

    if report["errors"]:
        if args.report:
            Path(args.report).write_text(json.dumps(report, indent=2))
        print(json.dumps(report, indent=2), file=sys.stderr)
        return 1

    Path(args.output).write_text(normalized)
    if args.report:
        Path(args.report).write_text(json.dumps(report, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
