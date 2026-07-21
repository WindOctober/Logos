#!/usr/bin/env python3
import argparse
import json
import re
import shutil
import sys
from dataclasses import dataclass
from pathlib import Path

from materializer_sql import (
    ASCII_SQL_WHITESPACE,
    find_matching_paren,
    mask_sql_regions,
    normalize_sql_layout,
    parse_schema,
    protected_sql_regions,
    split_top_level_commas,
)


ROOT = Path(__file__).resolve().parents[3]
DEFAULT_INPUT = "benchmarks/core/.generated/sqlsolver"
DEFAULT_OUTPUT = "benchmarks/core/.generated/cosette"

TABLE_CONSTRAINT_PREFIXES = {
    "constraint",
    "primary",
    "foreign",
    "unique",
    "check",
    "key",
    "index",
}

COLUMN_TYPE_STOP = {
    "not",
    "null",
    "default",
    "primary",
    "unique",
    "references",
    "check",
    "constraint",
    "collate",
    "generated",
    "auto_increment",
}

COSETTE_SQL_KEYWORDS = {
    "and",
    "as",
    "by",
    "distinct",
    "exists",
    "fetch",
    "from",
    "group",
    "having",
    "inner",
    "join",
    "limit",
    "not",
    "on",
    "or",
    "order",
    "offset",
    "select",
    "union",
    "where",
}

COSETTE_SUPPORTED_AGGREGATES = frozenset(("sum", "count", "max", "min"))
COSETTE_SIMPLE_COLUMN_PATH = re.compile(
    r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*",
    flags=re.ASCII,
)

FATAL_FEATURES = (
    ("with", r"\bwith\b", "CTE/WITH queries are not accepted by Cosette's SQL parser."),
    ("outer-join", r"\b(left|right|full)\s+(outer\s+)?join\b", "Outer joins are not accepted by Cosette's SQL parser."),
    ("cross-natural-join", r"\b(cross|natural)\s+join\b", "CROSS/NATURAL joins are not accepted by Cosette's SQL parser."),
    ("set-op", r"\b(except|intersect)\b", "EXCEPT/INTERSECT are not accepted by Cosette's SQL parser."),
    ("union-distinct", r"\bunion\b(?!\s+all\b)", "UNION without ALL has duplicate-elimination semantics not expressible as Cosette UNION ALL."),
    ("values", r"\bvalues\b", "VALUES relations are not accepted by Cosette's SQL parser."),
    ("window", r"\bover\s*\(", "Window functions are not accepted by Cosette's SQL parser."),
    ("rollup-grouping", r"\b(rollup|grouping|grouping\s+sets)\b", "ROLLUP/GROUPING/GROUPING SETS are not accepted by Cosette's SQL parser."),
    ("case", r"\bcase\b", "CASE expressions are not accepted by Cosette's SQL parser."),
    ("cast", r"\bcast\s*\(", "CAST expressions are not accepted by Cosette's SQL parser."),
    ("null", r"\bnull\b|\bis\s+null\b|\bis\s+not\s+null\b", "NULL literals and IS NULL predicates are not represented in Cosette's public DSL."),
    ("like", r"\blike\b", "LIKE predicates are not represented in Cosette's public DSL."),
    ("date-interval", r"\b(date|interval|timestamp)\b", "Date/time literals and interval arithmetic need benchmark-specific integer encodings."),
    ("decimal", r"(?<![\w.])\d+\.\d+(?![\w.])", "Decimal literals are outside Cosette's int/string scalar surface."),
    ("aggregate-distinct", r"\b(count|sum|min|max)\s*\(\s*distinct\b", "DISTINCT inside aggregate calls is not accepted by Cosette's aggregate parser."),
    ("aggregate-modifier", r"\b(?:filter|within\s+group)\s*\(", "Aggregate FILTER/WITHIN GROUP modifiers are outside Cosette's aggregate parser."),
)


@dataclass
class Column:
    name: str
    cosette_type: str
    source_type: str


@dataclass
class Table:
    name: str
    columns: list[Column]


@dataclass
class QueryMaterialization:
    sql: str
    syntax_blockers: list[str]
    semantic_blockers: list[str]

    @property
    def blockers(self) -> list[str]:
        """Backward-compatible aggregate view used by focused unit tests."""

        return dedupe(self.syntax_blockers + self.semantic_blockers)


@dataclass(frozen=True)
class CaseCompatibility:
    status: str
    syntax_compatibility: str
    semantic_profile_compatibility: str


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Materialize SQL benchmark cases as Cosette DSL inputs. The source "
            "profile is the solver-neutral schema/sql1/sql2 layout currently "
            "also used by SQLSolver."
        )
    )
    parser.add_argument("--input-root", default=DEFAULT_INPUT)
    parser.add_argument("--output-dir", default=DEFAULT_OUTPUT)
    parser.add_argument("--case", action="append", help="Case id regex. May be repeated.")
    parser.add_argument("--limit", type=int)
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args()

    input_root = resolve(args.input_root)
    output_dir = resolve(args.output_dir)
    if not input_root.is_dir():
        print(f"Cosette input root does not exist or is not a directory: {input_root}", file=sys.stderr)
        return 2

    patterns = [re.compile(pattern) for pattern in args.case or []]
    cases = discover_cases(input_root, patterns, args.limit)
    if not cases:
        print(f"No Cosette source cases were discovered under: {input_root}", file=sys.stderr)
        return 2

    if args.force and output_dir.exists():
        shutil.rmtree(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    emitted = 0
    syntax_compatible = 0
    semantic_profile_compatible = 0
    partition = {
        "fullyCompatible": 0,
        "syntaxOnlyCompatible": 0,
        "semanticProfileOnlyCompatible": 0,
        "flaggedOnBothAxes": 0,
    }
    failed = 0
    for case_dir in cases:
        relative = case_dir.relative_to(input_root)
        target = output_dir / relative
        try:
            compatibility = materialize_case(input_root, case_dir, target)
            emitted += 1
            syntax_ok = compatibility.syntax_compatibility == "compatible"
            semantic_ok = compatibility.semantic_profile_compatibility == "compatible"
            syntax_compatible += int(syntax_ok)
            semantic_profile_compatible += int(semantic_ok)
            if syntax_ok and semantic_ok:
                partition["fullyCompatible"] += 1
            elif syntax_ok:
                partition["syntaxOnlyCompatible"] += 1
            elif semantic_ok:
                partition["semanticProfileOnlyCompatible"] += 1
            else:
                partition["flaggedOnBothAxes"] += 1
            print(f"{compatibility.status} cosette/{relative}", file=sys.stderr)
        except Exception as exc:
            failed += 1
            target.mkdir(parents=True, exist_ok=True)
            write_json(
                target / "metadata.json",
                {
                    "sourceProfile": "sqlsolver",
                    "sourceCase": str(relative),
                    "profile": "cosette",
                    "status": "materialization-error",
                    "error": str(exc),
                },
            )
            print(f"failed cosette/{relative}: {exc}", file=sys.stderr)

    write_json(
        output_dir / "manifest.json",
        {
            "profile": "cosette",
            "inputRoot": portable_path(input_root),
            "outputLayout": ".",
            "discovered": len(cases),
            "emitted": emitted,
            "failed": failed,
            "staticCompatibility": {
                "compatible": syntax_compatible,
                "flagged": emitted - syntax_compatible,
            },
            "semanticProfileCompatibility": {
                "compatible": semantic_profile_compatible,
                "flagged": emitted - semantic_profile_compatible,
            },
            "compatibilityPartition": partition,
            "countingNote": (
                "The four compatibilityPartition buckets are disjoint and sum to emitted. "
                "staticCompatibility and semanticProfileCompatibility are independent axes."
            ),
        },
    )
    print(
        "summary: "
        f"discovered={len(cases)} emitted={emitted} "
        f"fully_compatible={partition['fullyCompatible']} failed={failed}",
        file=sys.stderr,
    )
    return 1 if failed else 0


def resolve(path: str | Path) -> Path:
    candidate = Path(path)
    return candidate if candidate.is_absolute() else ROOT / candidate


def portable_path(path: Path) -> str:
    try:
        return str(path.resolve().relative_to(ROOT.resolve()))
    except ValueError:
        return str(path.resolve())


def discover_cases(input_root: Path, patterns: list[re.Pattern], limit: int | None) -> list[Path]:
    if limit is not None and limit <= 0:
        return []
    if is_solver_case(input_root):
        relative = input_root.name
        if patterns and not any(
            pattern.search(input_root.name) or pattern.search(relative)
            for pattern in patterns
        ):
            return []
        return [input_root]
    cases: list[Path] = []
    for case_dir in sorted(input_root.rglob("*"), key=lambda path: str(path.relative_to(input_root))):
        if not case_dir.is_dir() or not is_solver_case(case_dir):
            continue
        relative = str(case_dir.relative_to(input_root))
        if patterns and not any(pattern.search(case_dir.name) or pattern.search(relative) for pattern in patterns):
            continue
        cases.append(case_dir)
        if limit is not None and len(cases) >= limit:
            break
    return cases


def is_solver_case(path: Path) -> bool:
    return all((path / name).exists() for name in ("schema.sql", "sql1.sql", "sql2.sql"))


def materialize_case(
    input_root: Path,
    case_dir: Path,
    target: Path,
) -> CaseCompatibility:
    target.mkdir(parents=True, exist_ok=True)
    schema_sql = (case_dir / "schema.sql").read_text()
    sql1 = normalize_query_payload((case_dir / "sql1.sql").read_text())
    sql2 = normalize_query_payload((case_dir / "sql2.sql").read_text())
    tables = parse_tables(schema_sql)
    if not tables:
        raise ValueError("no CREATE TABLE declarations were recognized")

    source_metadata = read_required_metadata(case_dir / "metadata.json")
    q1 = materialize_query(sql1)
    q2 = materialize_query(sql2)
    syntax_blockers = dedupe(
        q1.syntax_blockers
        + q2.syntax_blockers
        + detect_missing_base_table_aliases(sql1, tables)
        + detect_missing_base_table_aliases(sql2, tables)
    )
    semantic_blockers = dedupe(
        q1.semantic_blockers
        + q2.semantic_blockers
        + detect_authoritative_constraint_blockers(source_metadata, schema_sql)
        + detect_null_profile_blockers(source_metadata)
        + detect_source_type_audit_blockers(source_metadata)
        + detect_pair_semantic_blockers(sql1, sql2)
        + detect_type_lowering_blockers(sql1, sql2, tables)
        + detect_aggregate_error_semantics_blockers(sql1, sql2)
    )
    syntax_compatibility = "flagged" if syntax_blockers else "compatible"
    semantic_profile_compatibility = (
        "flagged" if semantic_blockers else "compatible"
    )
    status = (
        "materialized"
        if syntax_compatibility == "compatible"
        and semantic_profile_compatibility == "compatible"
        else "flagged"
    )
    cosette = render_cosette(tables, q1.sql, q2.sql)
    (target / "case.cos").write_text(cosette)
    metadata = {
        "sourceProfile": "sqlsolver",
        "sourceCase": str(case_dir.relative_to(input_root)),
        "profile": "cosette",
        "status": status,
        "syntaxCompatibility": syntax_compatibility,
        "semanticProfileCompatibility": semantic_profile_compatibility,
        "syntaxCompatibilityBlockers": syntax_blockers,
        "semanticProfileCompatibilityBlockers": semantic_blockers,
        # Retained for readers of the earlier generated profile. The two fields
        # below are the overall conjunction/union of the explicit axes above;
        # they must not be used to infer parser-only compatibility.
        "cosetteCompatibility": status,
        "cosetteFile": "case.cos",
        "cosetteUnsupportedFeatures": dedupe(syntax_blockers + semantic_blockers),
        "legacyCompatibilityFieldNote": (
            "cosetteCompatibility and cosetteUnsupportedFeatures are retained for "
            "generated-profile compatibility; syntaxCompatibility and "
            "semanticProfileCompatibility are authoritative."
        ),
        "tables": [
            {
                "name": table.name,
                "columns": [
                    {
                        "name": column.name,
                        "sourceType": column.source_type,
                        "cosetteType": column.cosette_type,
                    }
                    for column in table.columns
                ],
            }
            for table in tables
        ],
        "loweringNote": (
            "Cosette's public DSL exposes int/string scalar sorts. SQL scalar "
            "types are therefore lowered to int or string for frontend testing; "
            "constraints not expressible in the DSL remain in the source metadata. "
            "The Cosette SQL parser is narrower than the benchmark SQL corpus. "
            "Cases with unsupported frontend constructs are still emitted so "
            "Cosette can produce an auditable run log; unsafe rewrites are not "
            "applied silently."
        ),
    }
    metadata["sourceMetadata"] = source_metadata
    write_json(target / "metadata.json", metadata)
    return CaseCompatibility(
        status=status,
        syntax_compatibility=syntax_compatibility,
        semantic_profile_compatibility=semantic_profile_compatibility,
    )


def parse_tables(schema_sql: str) -> list[Table]:
    parsed = parse_schema(
        schema_sql,
        clean_identifier=clean_cosette_table_name,
        parse_table=parse_cosette_table,
    )
    return [table for table in parsed if table is not None]


def clean_cosette_table_name(value: str) -> str:
    """Retain Cosette's prior unquoted, optionally-qualified table grammar."""

    match = re.fullmatch(
        r"(?is)(?:if\s+not\s+exists\s+)?(?P<name>[A-Za-z_][\w.]*)",
        normalize_sql_layout(value),
    )
    return match.group("name").split(".")[-1] if match else ""


def parse_cosette_table(table_name: str, body: str) -> Table | None:
    columns = parse_columns(body)
    return Table(name=table_name, columns=columns) if table_name and columns else None


def parse_columns(body: str) -> list[Column]:
    columns: list[Column] = []
    for item in split_top_level_commas(body):
        tokens = item.strip().split()
        if len(tokens) < 2:
            continue
        head = unquote_identifier(tokens[0])
        if head.lower() in TABLE_CONSTRAINT_PREFIXES:
            continue
        type_tokens: list[str] = []
        for token in tokens[1:]:
            normalized = token.strip(",").lower()
            if normalized in COLUMN_TYPE_STOP:
                break
            type_tokens.append(token)
        source_type = " ".join(type_tokens).strip() or "unknown"
        columns.append(
            Column(
                name=head,
                source_type=source_type,
                cosette_type=map_type(source_type),
            )
        )
    return columns


def map_type(source_type: str) -> str:
    lowered = source_type.lower()
    if any(key in lowered for key in ("char", "text", "string", "uuid", "json", "inet")):
        return "string"
    return "int"


def detect_authoritative_constraint_blockers(
    metadata: dict,
    schema_sql: str = "",
) -> list[str]:
    constraints = metadata.get("constraints")
    if constraints is not None and not isinstance(constraints, list):
        raise ValueError("source metadata constraints must be a list or null")

    contract = metadata.get("integrityContract")
    if contract is not None and not isinstance(contract, dict):
        raise ValueError("source metadata integrityContract must be an object")
    contract = contract or {}

    has_pair_constraints = isinstance(constraints, list) and bool(constraints)
    has_semantic_sidecar = bool(contract.get("semanticSidecar"))
    has_wetune_contract = (
        str(contract.get("sourceKind") or "").lower().startswith("wetune")
        or has_semantic_sidecar
    )
    blockers: list[str] = []
    if has_pair_constraints or has_wetune_contract:
        blockers.append(
            "The authoritative benchmark contract contains integrity constraints, but Cosette's public DSL input does not encode pair constraints or the selected WeTune semantic sidecar."
        )

    scanned_schema = mask_sql_regions(schema_sql)
    if re.search(
        r"\b(?:NOT\s+NULL|PRIMARY\s+KEY|UNIQUE|FOREIGN\s+KEY|REFERENCES|CHECK\s*\()",
        scanned_schema,
        flags=re.IGNORECASE,
    ):
        blockers.append(
            "The parser-facing schema DDL contains integrity constraints, but Cosette's public DSL schema declarations encode only column sorts."
        )
    return blockers


def detect_null_profile_blockers(metadata: dict) -> list[str]:
    null_semantics = metadata.get("nullSemantics")
    if isinstance(null_semantics, str) and null_semantics.lower() in {
        "cosette-null-free",
        "null-free",
        "two-valued",
    }:
        return []
    if isinstance(null_semantics, str) and null_semantics:
        detail = f"declares {null_semantics!r}"
    else:
        detail = "does not attest a null-free value domain"
    return [
        "The source benchmark "
        + detail
        + ", while Cosette's public DSL profile does not preserve SQL NULL and three-valued predicate semantics."
    ]


def detect_source_type_audit_blockers(metadata: dict) -> list[str]:
    audit = metadata.get("typeLoweringAudit")
    if audit is None:
        return []
    if not isinstance(audit, dict):
        raise ValueError("source metadata typeLoweringAudit must be an object")
    unsafe = audit.get("unsafeLowerings")
    if unsafe is None:
        return []
    if not isinstance(unsafe, list):
        raise ValueError("source metadata typeLoweringAudit.unsafeLowerings must be a list")
    if not unsafe:
        return []
    source_types = sorted(
        {
            str(item.get("sourceType"))
            for item in unsafe
            if isinstance(item, dict) and item.get("sourceType")
        }
    )
    suffix = f" Source types: {', '.join(source_types)}." if source_types else ""
    return [
        f"The source type audit records {len(unsafe)} value-observing unsafe lowering(s) that Cosette's int/string profile cannot preserve."
        + suffix
    ]


def detect_pair_semantic_blockers(sql1: str, sql2: str) -> list[str]:
    if projection_group_by_without_aggregate(sql1) != projection_group_by_without_aggregate(sql2):
        return [
            "This pair compares a duplicate-eliminating GROUP BY projection with a plain projection; it depends on uniqueness constraints not encoded in Cosette's public DSL materialization."
        ]
    return []


def projection_group_by_without_aggregate(sql: str) -> bool:
    scanned = mask_sql_regions(sql)
    if not re.search(r"\bgroup\s+by\b", scanned, flags=re.IGNORECASE):
        return False
    if re.search(r"\b(count|sum|avg|min|max)\s*\(", scanned, flags=re.IGNORECASE):
        return False
    if re.search(r"\bhaving\b", scanned, flags=re.IGNORECASE):
        return False
    return True


def detect_type_lowering_blockers(sql1: str, sql2: str, tables: list[Table]) -> list[str]:
    decimal_columns: set[tuple[str, str]] = set()
    for table in tables:
        for column in table.columns:
            lowered = column.source_type.lower()
            if any(marker in lowered for marker in ("decimal", "numeric", "real", "float", "double")):
                decimal_columns.add((table.name.lower(), column.name.lower()))
    if not decimal_columns:
        return []
    scanned = mask_sql_regions(f"{sql1}\n{sql2}").lower()
    for table, column in sorted(decimal_columns):
        if references_column(scanned, table, column):
            return [
                "This case references DECIMAL/FLOAT schema columns, but Cosette's public DSL materialization lowers them to int rather than preserving SQL numeric semantics."
            ]
    return []


def references_column(scanned_sql: str, table: str, column: str) -> bool:
    """Conservatively recognize unqualified, table-, and alias-qualified uses."""

    identifier = r"A-Za-z0-9_$\x80-\U0010ffff"
    start = rf"(?<![{identifier}.])"
    end = rf"(?![{identifier}])"
    unqualified = rf"{start}{re.escape(column)}{end}"
    table_qualified = (
        rf"{start}{re.escape(table)}\s*\.\s*{re.escape(column)}{end}"
    )
    # SQLSolver-facing queries use simple unquoted aliases. Binding those aliases
    # precisely would require parsing each nested scope; matching any simple
    # qualifier is a deliberate fail-closed approximation and fixes the previous
    # false negative for `FROM prices AS p ... p.amount`.
    alias_qualified = (
        rf"{start}[A-Za-z_][A-Za-z0-9_$]*\s*\.\s*{re.escape(column)}{end}"
    )
    return any(
        re.search(pattern, scanned_sql, flags=re.IGNORECASE)
        for pattern in (table_qualified, alias_qualified, unqualified)
    )


_SQL_TOKEN = re.compile(
    r"[A-Za-z_\x80-\U0010ffff][A-Za-z0-9_$\x80-\U0010ffff]*|[().,;]"
)
_FROM_CLAUSE_END = frozenset(
    ("where", "group", "having", "order", "limit", "offset", "fetch", "union")
)
_TABLE_REF_BOUNDARY = _FROM_CLAUSE_END | frozenset(
    ("inner", "left", "right", "full", "cross", "natural", "join", "on")
)


def detect_missing_base_table_aliases(sql: str, tables: list[Table]) -> list[str]:
    """Find base-table references that Cosette cannot parse without an alias.

    This is a read-only token audit. It intentionally does not insert aliases or
    otherwise rewrite the submitted query.
    """

    scanned = mask_sql_regions(sql)
    tokens = [match.group(0) for match in _SQL_TOKEN.finditer(scanned)]
    known_tables = {table.name.lower() for table in tables}
    active_from: dict[int, bool] = {}
    depth = 0
    missing: list[str] = []

    index = 0
    while index < len(tokens):
        token = tokens[index]
        lowered = token.lower()
        if token == "(":
            depth += 1
            index += 1
            continue
        if token == ")":
            active_from.pop(depth, None)
            depth = max(0, depth - 1)
            index += 1
            continue
        if lowered in _FROM_CLAUSE_END:
            active_from[depth] = False
        if lowered == "from":
            active_from[depth] = True
            table_index = index + 1
        elif lowered == "join" and active_from.get(depth, False):
            table_index = index + 1
        elif token == "," and active_from.get(depth, False):
            table_index = index + 1
        else:
            index += 1
            continue

        parsed = parse_base_table_reference(tokens, table_index, known_tables)
        if parsed is not None:
            table_name, alias_present = parsed
            if not alias_present and table_name not in missing:
                missing.append(table_name)
        index += 1

    if not missing:
        return []
    return [
        "Cosette requires every base-table reference to have an explicit or bare alias; missing aliases: "
        + ", ".join(missing)
        + "."
    ]


def parse_base_table_reference(
    tokens: list[str],
    start: int,
    known_tables: set[str],
) -> tuple[str, bool] | None:
    if start >= len(tokens) or not is_identifier_start_char(tokens[start][0]):
        return None
    if tokens[start].lower() in _TABLE_REF_BOUNDARY:
        return None

    parts = [tokens[start]]
    index = start + 1
    while (
        index + 1 < len(tokens)
        and tokens[index] == "."
        and is_identifier_start_char(tokens[index + 1][0])
    ):
        parts.append(tokens[index + 1])
        index += 2
    table_name = parts[-1].lower()
    if known_tables and table_name not in known_tables:
        return None

    if index < len(tokens) and tokens[index].lower() == "as":
        alias_present = (
            index + 1 < len(tokens)
            and is_identifier_start_char(tokens[index + 1][0])
            and tokens[index + 1].lower() not in _TABLE_REF_BOUNDARY
        )
        return table_name, alias_present
    if index < len(tokens):
        next_token = tokens[index].lower()
        if (
            is_identifier_start_char(tokens[index][0])
            and next_token not in _TABLE_REF_BOUNDARY
        ):
            return table_name, True
    return table_name, False


def detect_aggregate_error_semantics_blockers(sql1: str, sql2: str) -> list[str]:
    scanned = mask_sql_regions(f"{sql1}\n{sql2}")
    aggregates = sorted(
        {
            match.group(1).upper()
            for match in re.finditer(
                r"\b(count|sum)\s*\(",
                scanned,
                flags=re.IGNORECASE,
            )
        }
    )
    if not aggregates:
        return []
    return [
        "Cosette models "
        + "/".join(aggregates)
        + " over unbounded values and does not preserve PostgreSQL aggregate overflow or runtime-error outcomes without an explicit safety premise."
    ]


def materialize_query(sql: str) -> QueryMaterialization:
    syntax_blockers = detect_unsupported(sql)
    syntax_blockers.extend(detect_remaining_parser_blockers(sql))
    return QueryMaterialization(
        sql=sql,
        syntax_blockers=dedupe(syntax_blockers),
        semantic_blockers=detect_query_semantic_blockers(sql),
    )


def detect_query_semantic_blockers(sql: str) -> list[str]:
    blockers: list[str] = []
    scanned = mask_sql_regions(sql)
    if re.search(r"\b(?:true|false)\b", scanned, flags=re.IGNORECASE):
        blockers.append(
            "Boolean literals require a type-attested two-valued encoding that is absent from this Cosette profile."
        )
    if contains_unmodeled_integer_arithmetic(scanned):
        blockers.append(
            "Integer arithmetic is not semantically admitted because Cosette's unbounded integers do not preserve PostgreSQL overflow and runtime-error outcomes."
        )
    if contains_unmodeled_constant_group_key(sql):
        blockers.append(
            "Literal GROUP BY keys are not semantically admitted because PostgreSQL integer keys can be select-list ordinals and this adapter has no exact binding proof."
        )
    return dedupe(blockers)


def detect_unsupported(sql: str) -> list[str]:
    blockers: list[str] = []
    scanned = mask_sql_regions(sql)
    for _name, pattern, message in FATAL_FEATURES:
        if re.search(pattern, scanned, flags=re.IGNORECASE):
            blockers.append(message)
    regions = protected_sql_regions(sql)
    if any(region.kind == "double_quote" for region in regions):
        blockers.append(
            "Double-quoted identifiers or strings are not accepted by Cosette's identifier/string tokenizers."
        )
    if any(region.kind == "backtick_quote" for region in regions):
        blockers.append("Backtick-quoted identifiers conflict with Cosette query delimiters.")
    if re.search(r"\bin\s*\(\s*select\b", scanned, flags=re.IGNORECASE):
        blockers.append("IN subqueries require semantic semijoin rewriting; they are not lowered generically.")
    if re.search(r"\bnot\s+in\s*\(", scanned, flags=re.IGNORECASE):
        blockers.append("NOT IN depends on SQL NULL semantics and is not lowered generically.")
    return blockers


def detect_remaining_parser_blockers(sql: str) -> list[str]:
    blockers: list[str] = []
    scanned = mask_sql_regions(sql)
    checks = (
        (r"\binner\s+join\b", "INNER JOIN is outside the conservatively admitted Cosette SQL surface."),
        (r"\b(?:from|join)\s*\(", "Derived-table FROM/JOIN subqueries are outside the conservatively admitted Cosette SQL surface."),
        (r",\s*\(\s*(?:select|with)\b", "Derived-table FROM/JOIN subqueries are outside the conservatively admitted Cosette SQL surface."),
        (r"\bhaving\b", "HAVING is outside the conservatively admitted Cosette SQL surface."),
        (r"\bis\s+not\s+distinct\s+from\b", "IS NOT DISTINCT FROM needs NULL-aware equality semantics unavailable in this adapter."),
        (r"\bin\s*\(", "IN predicates are outside the conservatively admitted Cosette SQL surface."),
        (r"\bbetween\b", "BETWEEN is retained because this adapter has no parsed, type-checked lowering for it."),
        (r"<=|>=|!=|<>", "These comparison operators are retained because this adapter has no parsed lowering for them."),
        (r"\border\s+by\b", "ORDER BY is unsupported because key evaluation and runtime failures remain observable."),
        (r"\blimit\b|\boffset\b|\bfetch\b", "LIMIT/OFFSET/FETCH has unsupported cardinality and runtime-error semantics."),
    )
    for pattern, message in checks:
        if re.search(pattern, scanned, flags=re.IGNORECASE):
            blockers.append(message)
    blockers.extend(detect_cosette_call_blockers(sql, scanned))
    return blockers


def detect_cosette_call_blockers(sql: str, scanned_sql: str) -> list[str]:
    unsupported_names: list[str] = []
    unsupported_form = False
    index = 0
    while index < len(scanned_sql):
        if not is_identifier_start_char(scanned_sql[index]):
            index += 1
            continue
        start = index
        index += 1
        while index < len(scanned_sql) and is_identifier_byte(scanned_sql[index]):
            index += 1
        name = scanned_sql[start:index]
        open_paren = index
        while (
            open_paren < len(scanned_sql)
            and scanned_sql[open_paren] in ASCII_SQL_WHITESPACE
        ):
            open_paren += 1
        if open_paren >= len(scanned_sql) or scanned_sql[open_paren] != "(":
            continue

        lowered = name.lower()
        previous = start - 1
        while previous >= 0 and scanned_sql[previous] in ASCII_SQL_WHITESPACE:
            previous -= 1
        qualified = previous >= 0 and scanned_sql[previous] == "."
        if not qualified and lowered in COSETTE_SQL_KEYWORDS:
            continue
        if qualified or lowered not in COSETTE_SUPPORTED_AGGREGATES:
            if lowered not in unsupported_names:
                unsupported_names.append(lowered)
            continue

        close_paren = find_matching_paren(sql, open_paren)
        if close_paren < 0:
            unsupported_form = True
            continue
        argument = sql[open_paren + 1 : close_paren].strip(ASCII_SQL_WHITESPACE)
        simple_column = COSETTE_SIMPLE_COLUMN_PATH.fullmatch(argument) is not None
        if not simple_column and not (lowered == "count" and argument == "*"):
            unsupported_form = True

    blockers: list[str] = []
    if unsupported_names:
        blockers.append(
            "Function calls outside Cosette's closed SUM/COUNT/MAX/MIN aggregate surface are unsupported: "
            + ", ".join(unsupported_names)
            + "."
        )
    if unsupported_form:
        blockers.append(
            "Cosette aggregate calls are admitted only as unqualified SUM/COUNT/MAX/MIN over one simple unquoted column path, or COUNT(*)."
        )
    return blockers


def contains_unmodeled_integer_arithmetic(scanned_sql: str) -> bool:
    operand = r"(?:[A-Za-z_][A-Za-z0-9_$.]*|[0-9]+|\))"
    right_operand = r"(?:[A-Za-z_][A-Za-z0-9_$.]*|[+-]?[0-9]+|\()"
    pattern = re.compile(
        rf"(?P<left>{operand})\s*(?P<operator>[+*/-])\s*(?P<right>{right_operand})"
    )
    position = 0
    while match := pattern.search(scanned_sql, position):
        # Advance from the start so a skipped keyword/wildcard candidate cannot
        # hide a genuine overlapping arithmetic expression to its right.
        position = match.start() + 1
        left = match.group("left")
        right = match.group("right").lstrip("+-")
        if left.lower() in COSETTE_SQL_KEYWORDS or right.lower() in COSETTE_SQL_KEYWORDS:
            continue
        if match.group("operator") == "*" and left.endswith("."):
            # Qualified SELECT wildcards are not arithmetic multiplication.
            continue
        return True
    return False


def contains_unmodeled_constant_group_key(sql: str) -> bool:
    searchable = mask_sql_regions(sql)
    for match in re.finditer(r"\bgroup\s+by\b", searchable, flags=re.IGNORECASE):
        end = find_clause_boundary(
            sql,
            match.end(),
            ("having", "order", "limit", "offset", "fetch", "union"),
        )
        for key in split_top_level_commas(sql[match.end() : end]):
            stripped = key.strip()
            if re.fullmatch(r"[+-]?\d+", stripped) or re.fullmatch(
                r"'(?:''|[^'])*'", stripped
            ):
                return True
    return False


def find_top_level_keyword(sql: str, keyword: str, start: int = 0) -> int | None:
    searchable = mask_sql_regions(sql)
    lowered = searchable.lower()
    needle = keyword.lower()
    depth = 0
    index = start
    while index < len(sql):
        char = searchable[index]
        if char == "(":
            depth += 1
            index += 1
            continue
        if char == ")":
            depth = max(0, depth - 1)
            index += 1
            continue
        if depth == 0 and lowered.startswith(needle, index):
            left_ok = index == 0 or not (
                is_identifier_byte(searchable[index - 1])
            )
            right = index + len(needle)
            right_ok = right >= len(sql) or not (
                is_identifier_byte(searchable[right])
            )
            if left_ok and right_ok:
                return index
        index += 1
    return None


def is_identifier_byte(char: str) -> bool:
    return char.isalnum() or char in ("_", "$") or ord(char) >= 128


def is_identifier_start_char(char: str) -> bool:
    return char == "_" or (char.isascii() and char.isalpha()) or ord(char) >= 128


def find_clause_boundary(sql: str, start: int, keywords: tuple[str, ...]) -> int:
    candidates = [
        index
        for keyword in keywords
        if (index := find_top_level_keyword(sql, keyword, start)) is not None
    ]
    return min(candidates) if candidates else len(sql)


def dedupe(values: list[str]) -> list[str]:
    seen: set[str] = set()
    result: list[str] = []
    for value in values:
        if not value or value in seen:
            continue
        seen.add(value)
        result.append(value)
    return result


def render_cosette(tables: list[Table], sql1: str, sql2: str) -> str:
    lines: list[str] = []
    for table in tables:
        columns = ", ".join(f"{column.name}:{column.cosette_type}" for column in table.columns)
        lines.append(f"schema {table.name}({columns});")
    for table in tables:
        lines.append(f"table {table.name}({table.name});")
    lines.extend(
        [
            "",
            f"query q1 `{sql1}`;",
            "",
            f"query q2 `{sql2}`;",
            "",
            "verify q1 q2;",
            "",
        ]
    )
    return "\n".join(lines)


def normalize_query_payload(sql: str) -> str:
    return normalize_sql_layout(sql, strip_trailing_semicolon=True)


def unquote_identifier(value: str) -> str:
    value = value.strip()
    if len(value) >= 2 and value[0] in ('"', "`", "[") and value[-1] in ('"', "`", "]"):
        return value[1:-1]
    return value


def write_json(path: Path, payload: dict) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")


def read_required_metadata(path: Path) -> dict:
    if not path.exists():
        raise ValueError(f"required source metadata is missing: {path}")
    payload = json.loads(path.read_text())
    if not isinstance(payload, dict):
        raise ValueError(f"source metadata must be a JSON object: {path}")
    return payload


if __name__ == "__main__":
    raise SystemExit(main())
