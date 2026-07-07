#!/usr/bin/env python3
import argparse
import json
import re
import shutil
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Callable


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
    "from",
    "group",
    "having",
    "inner",
    "join",
    "not",
    "on",
    "or",
    "order",
    "select",
    "union",
    "where",
}

CASE_SPECIFIC_BLOCKERS = {
    "nonwetune-flat__verieql-calcite__calcite-95": "Known grouped VALUES(TRUE) witness-to-EXISTS lowering remains unimplemented; keep flagged rather than emitting unsupported VALUES/derived-table syntax as clean.",
    "nonwetune-flat__verieql-calcite__calcite-129": "Known typed-empty VALUES/NULL canonicalization opportunity remains unimplemented; keep flagged rather than emitting unsupported VALUES/NULL syntax as clean.",
    "nonwetune-flat__verieql-calcite__calcite-370": "Known grouped-right unused LEFT JOIN elimination remains unimplemented; keep flagged rather than emitting unsupported LEFT JOIN syntax as clean.",
    "nonwetune-flat__verieql-calcite__calcite-377": "Known null-rejected outer-to-inner join lowering remains unimplemented; keep flagged rather than emitting unsupported RIGHT JOIN syntax as clean.",
    "nonwetune-flat__verieql-literature__cex-benchmarks-csep544_hw3-49": "This aggregate/DISTINCT benchmark needs assumptions not represented in the current Cosette materialization.",
    "nonwetune-flat__verieql-literature__conditional-ex1sigmod92-0": "This literature rewrite depends on key/uniqueness constraints not encoded in Cosette's public DSL materialization.",
    "nonwetune-flat__verieql-literature__conditional-ex2sigmod83-1": "This literature rewrite depends on key/functional-dependency constraints not encoded in Cosette's public DSL materialization.",
    "nonwetune-flat__verieql-literature__conditional-ex2sigmod92simpl-3": "This literature rewrite depends on key/uniqueness constraints not encoded in Cosette's public DSL materialization.",
    "nonwetune-flat__verieql-literature__conditional-index_sigmod82-6": "This source pair is not a constraint-free bag-equivalence benchmark under the current Cosette materialization.",
    "nonwetune-flat__verieql-literature__conditional-missing-pred-8": "This case needs SQL NULL/three-valued-logic assumptions not represented in the current Cosette materialization.",
    "nonwetune-flat__verieql-literature__sqlrewrites-SelfJoin1-19": "This self-join identity rewrite requires NOT NULL assumptions not encoded in the current Cosette materialization.",
    "nonwetune-flat__verieql-literature__sqlrewrites-SelfJoin2-20": "This self-join identity rewrite requires NOT NULL assumptions not encoded in the current Cosette materialization.",
    "nonwetune-flat__verieql-literature__sqlrewrites-countProject-24": "COUNT(column) versus COUNT(*) requires NOT NULL assumptions not encoded in the current Cosette materialization.",
    "nonwetune-flat__verieql-calcite__calcite-216": "This correlated aggregate subquery still needs scoped column qualification or a scalar-aggregate EXISTS rewrite before it can be trusted as Cosette-clean.",
    "wetune-issues__3": "This WeTune rewrite depends on uniqueness/key constraints not encoded in Cosette's public DSL materialization.",
}

CLAUSE_BOUNDARY = (
    "where",
    "group",
    "having",
    "order",
    "limit",
    "offset",
    "fetch",
    "union",
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
    ("function", r"\b(coalesce|substring|substr|lower|upper|power|exp)\s*\(", "This scalar function is outside Cosette's arithmetic-only expression surface."),
    ("bit-aggregate", r"\b(bit_and|bit_or)\s*\(", "BIT_AND/BIT_OR aggregates are not represented in Cosette's public DSL."),
    ("any-value", r"\bany_value\s*\(", "ANY_VALUE has nondeterministic representative-value semantics not represented in Cosette's public DSL."),
    ("single-value", r"\bsingle_value\s*\(", "SINGLE_VALUE has runtime cardinality/error semantics not represented in Cosette's public DSL."),
    ("aggregate-distinct", r"\b(count|sum|avg|min|max)\s*\(\s*distinct\b", "DISTINCT inside aggregate calls is not accepted by Cosette's aggregate parser."),
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
class SourceFacts:
    not_null: set[str]


@dataclass
class QueryMaterialization:
    sql: str
    transformations: list[str]
    blockers: list[str]


@dataclass
class Compatibility:
    status: str
    blockers: list[str]
    transformations: list[str]


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
    if args.force and output_dir.exists():
        shutil.rmtree(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    patterns = [re.compile(pattern) for pattern in args.case or []]
    cases = discover_cases(input_root, patterns, args.limit)
    materialized = 0
    flagged = 0
    failed = 0
    for case_dir in cases:
        relative = case_dir.relative_to(input_root)
        case_id = "__".join(relative.parts)
        target = output_dir / relative
        try:
            status = materialize_case(input_root, case_dir, target, case_id)
            materialized += 1
            if status != "materialized":
                flagged += 1
            print(f"{status} cosette/{relative}", file=sys.stderr)
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
            "inputRoot": str(input_root),
            "outputRoot": str(output_dir),
            "materialized": materialized,
            "flagged": flagged,
            "unsupported": 0,
            "failed": failed,
        },
    )
    print(f"summary: materialized={materialized} flagged={flagged} failed={failed}", file=sys.stderr)
    return 1 if failed else 0


def resolve(path: str | Path) -> Path:
    candidate = Path(path)
    return candidate if candidate.is_absolute() else ROOT / candidate


def discover_cases(input_root: Path, patterns: list[re.Pattern], limit: int | None) -> list[Path]:
    if is_solver_case(input_root):
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


def materialize_case(input_root: Path, case_dir: Path, target: Path, case_id: str) -> str:
    target.mkdir(parents=True, exist_ok=True)
    schema_sql = (case_dir / "schema.sql").read_text(errors="replace")
    sql1 = first_query((case_dir / "sql1.sql").read_text(errors="replace"))
    sql2 = first_query((case_dir / "sql2.sql").read_text(errors="replace"))
    tables = parse_tables(schema_sql)
    if not tables:
        raise ValueError("no CREATE TABLE declarations were recognized")

    source_metadata = read_json_if_exists(case_dir / "metadata.json")
    source_facts = extract_source_facts(source_metadata)
    q1 = materialize_query(sql1, tables, source_facts)
    q2 = materialize_query(sql2, tables, source_facts)
    compatibility = combine_compatibility(q1, q2)
    metadata_blockers = detect_source_metadata_blockers(source_metadata)
    pair_blockers = detect_pair_semantic_blockers(sql1, sql2, source_metadata)
    type_blockers = detect_type_lowering_blockers(sql1, sql2, tables)
    case_blockers = detect_case_specific_blockers(case_id)
    if metadata_blockers or pair_blockers or type_blockers or case_blockers:
        compatibility = Compatibility(
            status="flagged",
            blockers=dedupe(
                compatibility.blockers
                + metadata_blockers
                + pair_blockers
                + type_blockers
                + case_blockers
            ),
            transformations=compatibility.transformations,
        )
    cosette = render_cosette(tables, q1.sql, q2.sql)
    (target / "case.cos").write_text(cosette)
    metadata = {
        "sourceProfile": "sqlsolver",
        "sourceCase": str(case_dir.relative_to(input_root)),
        "profile": "cosette",
        "status": compatibility.status,
        "cosetteCompatibility": compatibility.status,
        "cosetteFile": "case.cos",
        "cosetteTransformations": compatibility.transformations,
        "cosetteUnsupportedFeatures": compatibility.blockers,
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
    if source_metadata is not None:
        metadata["sourceMetadata"] = source_metadata
    write_json(target / "metadata.json", metadata)
    return compatibility.status


def parse_tables(schema_sql: str) -> list[Table]:
    cleaned = strip_comments(schema_sql)
    tables: list[Table] = []
    for match in re.finditer(
        r"create\s+table\s+(?:if\s+not\s+exists\s+)?([A-Za-z_][\w.]*)\s*\(",
        cleaned,
        flags=re.IGNORECASE,
    ):
        name = match.group(1).split(".")[-1]
        body_start = match.end()
        body_end = find_matching_paren(cleaned, body_start - 1)
        if body_end is None:
            continue
        body = cleaned[body_start:body_end]
        columns = parse_columns(body)
        if columns:
            tables.append(Table(name=name, columns=columns))
    return tables


def parse_columns(body: str) -> list[Column]:
    columns: list[Column] = []
    for item in split_top_level(body):
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


def find_matching_paren(text: str, open_index: int) -> int | None:
    depth = 0
    quote: str | None = None
    for index in range(open_index, len(text)):
        char = text[index]
        if quote:
            if char == quote:
                quote = None
            continue
        if char in ("'", '"', "`"):
            quote = char
            continue
        if char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
            if depth == 0:
                return index
    return None


def split_top_level(text: str) -> list[str]:
    items: list[str] = []
    start = 0
    depth = 0
    quote: str | None = None
    for index, char in enumerate(text):
        if quote:
            if char == quote:
                quote = None
            continue
        if char in ("'", '"', "`"):
            quote = char
            continue
        if char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
        elif char == "," and depth == 0:
            items.append(text[start:index])
            start = index + 1
    items.append(text[start:])
    return items


def map_type(source_type: str) -> str:
    lowered = source_type.lower()
    if any(key in lowered for key in ("char", "text", "string", "uuid", "json", "inet")):
        return "string"
    return "int"


def extract_source_facts(metadata: dict | None) -> SourceFacts:
    not_null: set[str] = set()
    if metadata is None:
        return SourceFacts(not_null=not_null)
    for constraint in metadata.get("constraints") or []:
        item = constraint.get("not_null") if isinstance(constraint, dict) else None
        if not isinstance(item, dict):
            continue
        value = item.get("value")
        if isinstance(value, str):
            not_null.add(value.upper())
    return SourceFacts(not_null=not_null)


def detect_source_metadata_blockers(metadata: dict | None) -> list[str]:
    if metadata is None:
        return []
    rewrite_type = str(metadata.get("rewriteType") or "").lower()
    if any(marker in rewrite_type for marker in ("join elimination", "distinct placement")):
        return [
            "This source rewrite class depends on schema constraints that are not encoded in Cosette's public DSL materialization."
        ]
    return []


def detect_case_specific_blockers(case_id: str) -> list[str]:
    blocker = CASE_SPECIFIC_BLOCKERS.get(case_id)
    return [blocker] if blocker else []


def detect_pair_semantic_blockers(sql1: str, sql2: str, metadata: dict | None) -> list[str]:
    if metadata is None:
        return []
    if projection_group_by_without_aggregate(sql1) != projection_group_by_without_aggregate(sql2):
        return [
            "This pair compares a duplicate-eliminating GROUP BY projection with a plain projection; it depends on uniqueness constraints not encoded in Cosette's public DSL materialization."
        ]
    return []


def projection_group_by_without_aggregate(sql: str) -> bool:
    scanned = mask_string_literals(sql)
    if not re.search(r"\bgroup\s+by\b", scanned, flags=re.IGNORECASE):
        return False
    if re.search(r"\b(count|sum|avg|min|max)\s*\(", scanned, flags=re.IGNORECASE):
        return False
    if re.search(r"\bhaving\b", scanned, flags=re.IGNORECASE):
        return False
    return True


def detect_type_lowering_blockers(sql1: str, sql2: str, tables: list[Table]) -> list[str]:
    decimal_columns: set[str] = set()
    for table in tables:
        for column in table.columns:
            lowered = column.source_type.lower()
            if any(marker in lowered for marker in ("decimal", "numeric", "real", "float", "double")):
                decimal_columns.add(column.name.lower())
                decimal_columns.add(f"{table.name.lower()}.{column.name.lower()}")
    if not decimal_columns:
        return []
    scanned = mask_string_literals(f"{sql1}\n{sql2}").lower()
    for column in sorted(decimal_columns, key=len, reverse=True):
        if re.search(rf"(?<![.\w]){re.escape(column)}(?!\w)", scanned):
            return [
                "This case references DECIMAL/FLOAT schema columns, but Cosette's public DSL materialization lowers them to int rather than preserving SQL numeric semantics."
            ]
    return []


def materialize_query(sql: str, tables: list[Table], facts: SourceFacts) -> QueryMaterialization:
    transformations: list[str] = []
    normalized = normalize_boolean_literals(sql)

    early_result = rewrite_safe_scalar_surface(normalized, tables, facts)
    normalized = early_result.sql
    transformations.extend(early_result.transformations)
    blockers = early_result.blockers

    fold_result = fold_integer_constant_arithmetic(normalized)
    normalized = fold_result.sql
    transformations.extend(fold_result.transformations)

    group_result = drop_constant_group_by_keys(normalized)
    normalized = group_result.sql
    transformations.extend(group_result.transformations)

    limit_result = remove_frontend_order_limit(normalized)
    normalized = limit_result.sql
    transformations.extend(limit_result.transformations)
    blockers.extend(limit_result.blockers)

    late_derived_union_result = unwrap_select_star_derived_union_all(normalized)
    normalized = late_derived_union_result.sql
    transformations.extend(late_derived_union_result.transformations)

    if not blockers:
        comparison_result = rewrite_comparisons(normalized, tables, facts)
        normalized = comparison_result.sql
        transformations.extend(comparison_result.transformations)
        blockers.extend(comparison_result.blockers)

        alias_result = add_safe_table_aliases(normalized, tables)
        normalized = alias_result.sql
        transformations.extend(alias_result.transformations)
        blockers.extend(alias_result.blockers)

        join_result = lower_simple_inner_joins(normalized)
        normalized = join_result.sql
        transformations.extend(join_result.transformations)
        blockers.extend(join_result.blockers)

        qualification_result = qualify_single_table_columns(normalized, tables)
        normalized = qualification_result.sql
        transformations.extend(qualification_result.transformations)
        blockers.extend(qualification_result.blockers)

        blockers.extend(detect_remaining_parser_blockers(normalized))
    else:
        blockers.extend(detect_remaining_parser_blockers(normalized))

    return QueryMaterialization(
        sql=normalized,
        transformations=dedupe(transformations),
        blockers=dedupe(blockers),
    )


def combine_compatibility(q1: QueryMaterialization, q2: QueryMaterialization) -> Compatibility:
    blockers = dedupe(q1.blockers + q2.blockers)
    transformations = dedupe(q1.transformations + q2.transformations)
    status = "flagged" if blockers else "materialized"
    return Compatibility(status=status, blockers=blockers, transformations=transformations)


def detect_unsupported(sql: str) -> list[str]:
    blockers: list[str] = []
    scanned = mask_string_literals(sql)
    for _name, pattern, message in FATAL_FEATURES:
        if re.search(pattern, scanned, flags=re.IGNORECASE):
            blockers.append(message)
    if re.search(r'"[^"]+"', scanned):
        blockers.append(
            "Double-quoted identifiers or strings are not accepted by Cosette's identifier/string tokenizers."
        )
    if re.search(r"`", sql):
        blockers.append("Backtick-quoted identifiers conflict with Cosette query delimiters.")
    if re.search(r"\bin\s*\(\s*select\b", scanned, flags=re.IGNORECASE):
        blockers.append("IN subqueries require semantic semijoin rewriting; they are not lowered generically.")
    if re.search(r"\bnot\s+in\s*\(", scanned, flags=re.IGNORECASE):
        blockers.append("NOT IN depends on SQL NULL semantics and is not lowered generically.")
    return blockers


def detect_remaining_parser_blockers(sql: str) -> list[str]:
    blockers: list[str] = []
    scanned = mask_string_literals(sql)
    checks = (
        (r"\binner\s+join\b", "INNER JOIN remains after normalization; Cosette's SQL parser expects comma products or its narrower join surface."),
        (r"\b(?:from|join)\s*\(", "Derived-table FROM/JOIN subqueries remain after normalization; this Cosette frontend path is not yet audited as safe."),
        (r"\bhaving\b", "HAVING remains after normalization; this Cosette frontend path is not yet audited as safe."),
        (r"\bis\s+not\s+distinct\s+from\b", "IS NOT DISTINCT FROM remains after normalization and needs NULL-aware equality semantics."),
        (r"\bin\s*\(", "IN predicates remain after normalization."),
        (r"<=|>=|!=|<>", "Unsupported comparison operators remain after normalization."),
        (r"\border\s+by\b", "ORDER BY remains after normalization."),
        (r"\blimit\b|\boffset\b|\bfetch\b", "LIMIT/OFFSET/FETCH remains after normalization."),
    )
    for pattern, message in checks:
        if re.search(pattern, scanned, flags=re.IGNORECASE):
            blockers.append(message)
    return blockers


def detect_non_rewriteable_context(sql: str) -> list[str]:
    blockers: list[str] = []
    scanned = mask_string_literals(sql)
    checks = (
        (r"\bwith\b", "CTE/WITH queries are not accepted by Cosette's SQL parser."),
        (r"\b(left|right|full)\s+(outer\s+)?join\b", "Outer joins are not accepted by Cosette's SQL parser."),
        (r"\bnatural\s+join\b", "NATURAL joins are not accepted by Cosette's SQL parser."),
        (r"\b(except|intersect)\b", "EXCEPT/INTERSECT are not accepted by Cosette's SQL parser."),
        (r"\bunion\b(?!\s+all\b)", "UNION without ALL has duplicate-elimination semantics not expressible as Cosette UNION ALL."),
        (r"\bvalues\b", "VALUES relations are not accepted by Cosette's SQL parser."),
        (r"\bover\s*\(", "Window functions are not accepted by Cosette's SQL parser."),
        (r"\b(rollup|grouping|grouping\s+sets)\b", "ROLLUP/GROUPING/GROUPING SETS are not accepted by Cosette's SQL parser."),
        (r"\bnull\b|\bis\s+null\b|\bis\s+not\s+null\b", "NULL literals and IS NULL predicates are not represented in Cosette's public DSL."),
        (r"\blike\b", "LIKE predicates are not represented in Cosette's public DSL."),
        (r"\b(date|interval|timestamp)\b", "Date/time literals and interval arithmetic need benchmark-specific integer encodings."),
        (r"\b(coalesce|substring|substr|lower|upper|power|exp)\s*\(", "This scalar function is outside Cosette's arithmetic-only expression surface."),
        (r"\b(bit_and|bit_or)\s*\(", "BIT_AND/BIT_OR aggregates are not represented in Cosette's public DSL."),
        (r"\b(any_value|single_value)\s*\(", "ANY_VALUE/SINGLE_VALUE aggregate semantics are not represented in Cosette's public DSL."),
        (r"\b(count|sum|avg|min|max)\s*\(\s*distinct\b", "DISTINCT inside aggregate calls is not accepted by Cosette's aggregate parser."),
        (r"\bin\s*\(\s*select\b", "IN subqueries require semantic semijoin rewriting; they are not lowered generically."),
    )
    for pattern, message in checks:
        if re.search(pattern, scanned, flags=re.IGNORECASE):
            blockers.append(message)
    if re.search(r"`", sql):
        blockers.append("Backtick-quoted identifiers conflict with Cosette query delimiters.")
    return blockers


def normalize_boolean_literals(sql: str) -> str:
    sql = sub_outside_string_literals(re.compile(r"=\s*TRUE\b", flags=re.IGNORECASE), "= 1", sql)
    sql = sub_outside_string_literals(re.compile(r"=\s*FALSE\b", flags=re.IGNORECASE), "= 0", sql)
    sql = sub_outside_string_literals(re.compile(r"\bwhere\s+TRUE\b", flags=re.IGNORECASE), "WHERE 1 = 1", sql)
    sql = sub_outside_string_literals(re.compile(r"\bwhere\s+FALSE\b", flags=re.IGNORECASE), "WHERE 1 = 0", sql)
    return sql


def rewrite_safe_scalar_surface(sql: str, tables: list[Table], facts: SourceFacts) -> QueryMaterialization:
    transformations: list[str] = []
    blockers: list[str] = []
    normalized = sql

    cross_join_result = rewrite_cross_joins(normalized)
    normalized = cross_join_result.sql
    transformations.extend(cross_join_result.transformations)

    decimal_result = rewrite_all_zero_decimals(normalized)
    normalized = decimal_result.sql
    transformations.extend(decimal_result.transformations)

    tautology_result = rewrite_null_tautologies(normalized)
    normalized = tautology_result.sql
    transformations.extend(tautology_result.transformations)

    typed_empty_result = rewrite_constant_empty_values(normalized, tables)
    normalized = typed_empty_result.sql
    transformations.extend(typed_empty_result.transformations)
    blockers.extend(typed_empty_result.blockers)

    fetch_zero_result = rewrite_fetch_zero_to_typed_empty(normalized, tables)
    normalized = fetch_zero_result.sql
    transformations.extend(fetch_zero_result.transformations)
    blockers.extend(fetch_zero_result.blockers)

    order_result = remove_unconsumed_order_by(normalized)
    normalized = order_result.sql
    transformations.extend(order_result.transformations)

    derived_empty_join_result = rewrite_empty_derived_join(normalized, tables)
    normalized = derived_empty_join_result.sql
    transformations.extend(derived_empty_join_result.transformations)
    blockers.extend(derived_empty_join_result.blockers)

    singleton_values_result = remove_singleton_values_group_key(normalized)
    normalized = singleton_values_result.sql
    transformations.extend(singleton_values_result.transformations)

    unused_left_join_result = remove_grouped_unused_left_join(normalized)
    normalized = unused_left_join_result.sql
    transformations.extend(unused_left_join_result.transformations)

    intersect_empty_result = rewrite_contradictory_intersect_to_empty(normalized, tables)
    normalized = intersect_empty_result.sql
    transformations.extend(intersect_empty_result.transformations)
    blockers.extend(intersect_empty_result.blockers)

    derived_union_result = unwrap_select_star_derived_union_all(normalized)
    normalized = derived_union_result.sql
    transformations.extend(derived_union_result.transformations)

    join_result = lower_simple_inner_joins(normalized)
    normalized = join_result.sql
    transformations.extend(join_result.transformations)
    blockers.extend(join_result.blockers)

    case_result = rewrite_simple_cases(normalized)
    normalized = case_result.sql
    transformations.extend(case_result.transformations)

    fold_result = fold_integer_constant_arithmetic(normalized)
    normalized = fold_result.sql
    transformations.extend(fold_result.transformations)

    cast_result = rewrite_safe_casts(normalized)
    normalized = cast_result.sql
    transformations.extend(cast_result.transformations)

    not_in_result = rewrite_literal_not_in_lists(normalized, tables, facts)
    normalized = not_in_result.sql
    transformations.extend(not_in_result.transformations)
    blockers.extend(not_in_result.blockers)

    context_blockers = detect_non_rewriteable_context(normalized)
    if context_blockers:
        blockers.extend(context_blockers)

    blockers.extend(detect_unsupported(normalized))
    return QueryMaterialization(normalized, dedupe(transformations), dedupe(blockers))


def rewrite_cross_joins(sql: str) -> QueryMaterialization:
    normalized = sub_starting_outside_string_literals(
        re.compile(r"\s+cross\s+join\s+", flags=re.IGNORECASE),
        ", ",
        sql,
    )
    transformations = []
    if normalized != sql:
        transformations.append("Rewrote CROSS JOIN to comma product for Cosette's SQL frontend.")
    return QueryMaterialization(normalized, transformations, [])


def rewrite_all_zero_decimals(sql: str) -> QueryMaterialization:
    transformations: list[str] = []
    pattern = re.compile(r"(?<![\w.])([+-]?\d+)\.0+(?![\w.])")
    normalized = sub_starting_outside_string_literals(pattern, r"\1", sql)
    if normalized != sql:
        transformations.append("Rewrote all-zero decimal literals to integer literals.")
    return QueryMaterialization(normalized, transformations, [])


def rewrite_null_tautologies(sql: str) -> QueryMaterialization:
    transformations: list[str] = []
    expr = r"(?P<expr>[A-Za-z_][\w.]*|[+-]?\d+|'[^']*')"
    patterns = (
        re.compile(rf"{expr}\s+is\s+null\s+or\s+(?P=expr)\s+is\s+not\s+null", flags=re.IGNORECASE),
        re.compile(rf"{expr}\s+is\s+not\s+null\s+or\s+(?P=expr)\s+is\s+null", flags=re.IGNORECASE),
    )
    normalized = sql
    for pattern in patterns:
        updated = sub_starting_outside_string_literals(pattern, "1 = 1", normalized)
        if updated != normalized:
            transformations.append("Simplified IS NULL / IS NOT NULL tautology to TRUE.")
            normalized = updated
    return QueryMaterialization(normalized, dedupe(transformations), [])


def rewrite_constant_empty_values(sql: str, tables: list[Table]) -> QueryMaterialization:
    pattern = re.compile(
        r"^\s*select\s+\*\s+from\s+\(\s*values\s*\((?P<values>[^()]*)\)\s*\)\s+as\s+(?P<alias>[A-Za-z_]\w*)\s*\((?P<columns>[^()]*)\)\s+where\s+1\s*=\s*0\s*$",
        flags=re.IGNORECASE | re.DOTALL,
    )
    match = pattern.match(sql)
    if not match:
        return QueryMaterialization(sql, [], [])
    values = [value.strip().lower() for value in split_top_level(match.group("values"))]
    columns = [unquote_identifier(column.strip()) for column in split_top_level(match.group("columns"))]
    if not values or len(values) != len(columns) or any(value != "null" for value in values):
        return QueryMaterialization(sql, [], [])
    projection = resolve_projection_columns(columns, tables)
    if projection is None:
        return QueryMaterialization(
            sql,
            [],
            ["Could not resolve VALUES(NULL, ...) typed-empty projection against schema columns."],
        )
    select_exprs, from_items = projection
    normalized = f"SELECT {', '.join(select_exprs)} FROM {', '.join(from_items)} WHERE 1 = 0"
    return QueryMaterialization(
        normalized,
        ["Canonicalized VALUES(NULL, ...) under WHERE 1 = 0 to a schema-backed typed empty projection."],
        [],
    )


def resolve_projection_columns(columns: list[str], tables: list[Table]) -> tuple[list[str], list[str]] | None:
    used_tables: list[Table] = []
    used_table_names: set[str] = set()
    select_exprs: list[str] = []
    column_by_name: dict[str, list[tuple[Table, Column]]] = {}
    for table in tables:
        for column in table.columns:
            column_by_name.setdefault(column.name.lower(), []).append((table, column))

    for raw_column in columns:
        candidates = column_by_name.get(raw_column.lower())
        if not candidates:
            candidates = column_by_name.get(strip_numeric_suffix(raw_column).lower())
        if not candidates:
            return None
        chosen: tuple[Table, Column] | None = None
        has_numeric_suffix = strip_numeric_suffix(raw_column) != raw_column
        if not has_numeric_suffix:
            for table, column in candidates:
                if table.name in used_table_names:
                    chosen = (table, column)
                    break
        if chosen is None:
            for table, column in candidates:
                if table.name not in used_table_names:
                    chosen = (table, column)
                    break
        if chosen is None:
            chosen = candidates[0]
        table, column = chosen
        if table.name not in used_table_names:
            used_table_names.add(table.name)
            used_tables.append(table)
        select_exprs.append(f"{table.name}.{column.name}")

    from_items = [f"{table.name} AS {table.name}" for table in used_tables]
    if not from_items:
        return None
    return select_exprs, from_items


def strip_numeric_suffix(identifier: str) -> str:
    return re.sub(r"\d+$", "", identifier)


def rewrite_fetch_zero_to_typed_empty(sql: str, tables: list[Table]) -> QueryMaterialization:
    scanned = mask_string_literals(sql)
    if not re.search(r"\b(?:limit\s+0|fetch\s+(?:first|next)\s+0\s+rows\s+only)\b", scanned, flags=re.IGNORECASE):
        return QueryMaterialization(sql, [], [])
    projection = infer_output_projection(sql, tables)
    if projection is None:
        return QueryMaterialization(
            sql,
            [],
            ["Could not infer output schema for LIMIT/FETCH 0 typed-empty canonicalization."],
        )
    select_exprs, from_items = projection
    normalized = f"SELECT {', '.join(select_exprs)} FROM {', '.join(from_items)} WHERE 1 = 0"
    return QueryMaterialization(
        normalized,
        ["Canonicalized LIMIT/FETCH 0 query to a schema-backed typed empty projection."],
        [],
    )


def infer_output_projection(sql: str, tables: list[Table]) -> tuple[list[str], list[str]] | None:
    simple = re.match(
        r"^\s*select\s+(?P<select>.+?)\s+from\s+(?P<table>[A-Za-z_]\w*)(?:\s+(?:as\s+)?[A-Za-z_]\w*)?(?:\s+where\b.*?|\s+order\s+by\b.*?|\s+limit\b.*?|\s+fetch\b.*?|$)",
        sql,
        flags=re.IGNORECASE | re.DOTALL,
    )
    if simple:
        table = find_table(tables, simple.group("table"))
        if table is None:
            return None
        select_list = simple.group("select").strip()
        if select_list == "*":
            return (
                [f"{table.name}.{column.name}" for column in table.columns],
                [f"{table.name} AS {table.name}"],
            )
        columns = [extract_select_output_name(item) for item in split_top_level(select_list)]
        if all(columns):
            return resolve_projection_columns([column for column in columns if column], tables)

    derived_union = re.match(
        r"^\s*select\s+\*\s+from\s+\(+\s*select\s+(?P<select>.+?)\s+from\s+(?P<table>[A-Za-z_]\w*)\b.*?\bunion\s+all\b.*?\)+\s+as\s+[A-Za-z_]\w*\b",
        sql,
        flags=re.IGNORECASE | re.DOTALL,
    )
    if derived_union:
        columns = [extract_select_output_name(item) for item in split_top_level(derived_union.group("select"))]
        if all(columns):
            return resolve_projection_columns([column for column in columns if column], tables)
    return None


def extract_select_output_name(item: str) -> str | None:
    stripped = item.strip()
    alias_match = re.search(r"\bas\s+([A-Za-z_]\w*)\s*$", stripped, flags=re.IGNORECASE)
    if alias_match:
        return alias_match.group(1)
    if re.fullmatch(r"[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)?", stripped):
        return stripped.rsplit(".", 1)[-1]
    return None


def find_table(tables: list[Table], name: str) -> Table | None:
    for table in tables:
        if table.name.lower() == name.lower():
            return table
    return None


def rewrite_empty_derived_join(sql: str, tables: list[Table]) -> QueryMaterialization:
    pattern = re.compile(
        r"^\s*select\s+\*\s+from\s+\(\s*select\s+\*\s+from\s+(?P<left>[A-Za-z_]\w*)(?:\s+(?:as\s+)?[A-Za-z_]\w*)?\s+where\s+1\s*=\s*0\s*\)\s+as\s+[A-Za-z_]\w*\s+(?P<join>inner|left)(?:\s+outer)?\s+join\s+(?P<right>[A-Za-z_]\w*)(?:\s+(?:as\s+)?[A-Za-z_]\w*)?\s+on\s+.+?\s*$",
        flags=re.IGNORECASE | re.DOTALL,
    )
    match = pattern.match(sql)
    if not match:
        return QueryMaterialization(sql, [], [])
    left = find_table(tables, match.group("left"))
    right = find_table(tables, match.group("right"))
    if left is None or right is None:
        return QueryMaterialization(
            sql,
            [],
            ["Could not resolve empty derived join table names for typed-empty canonicalization."],
        )
    select_exprs = [f"{left.name}.{column.name}" for column in left.columns]
    select_exprs.extend(f"{right.name}.{column.name}" for column in right.columns)
    normalized = (
        f"SELECT {', '.join(select_exprs)} FROM {left.name} AS {left.name}, "
        f"{right.name} AS {right.name} WHERE 1 = 0"
    )
    return QueryMaterialization(
        normalized,
        ["Canonicalized INNER/LEFT JOIN with an empty left input to a schema-backed typed empty projection."],
        [],
    )


def remove_singleton_values_group_key(sql: str) -> QueryMaterialization:
    pattern = re.compile(
        r"^\s*select\s+(?P<select>.+?)\s+from\s+(?P<table>[A-Za-z_]\w*(?:\s+(?:as\s+)?[A-Za-z_]\w*)?)\s*,\s*\(\s*values\s*\(\s*(?P<value>[+-]?\d+|'[^']*')\s*\)\s*\)\s+as\s+(?P<alias>[A-Za-z_]\w*)\s*\(\s*(?P<column>[A-Za-z_]\w*)\s*\)\s+group\s+by\s+(?P<group>.+?)\s*$",
        flags=re.IGNORECASE | re.DOTALL,
    )
    match = pattern.match(sql)
    if not match:
        return QueryMaterialization(sql, [], [])
    alias_column = f"{match.group('alias')}.{match.group('column')}".lower()
    if alias_column in match.group("select").lower():
        return QueryMaterialization(sql, [], [])
    keys = [key.strip() for key in split_top_level(match.group("group"))]
    retained = [key for key in keys if key.lower() != alias_column]
    if len(retained) == len(keys) or not retained:
        return QueryMaterialization(sql, [], [])
    normalized = f"SELECT {match.group('select').strip()} FROM {match.group('table').strip()} GROUP BY {', '.join(retained)}"
    return QueryMaterialization(
        normalized,
        ["Removed a one-row VALUES relation used only as a constant GROUP BY key."],
        [],
    )


def remove_grouped_unused_left_join(sql: str) -> QueryMaterialization:
    pattern = re.compile(
        r"^\s*select\s+(?P<select>.+?)\s+from\s+(?P<left>[A-Za-z_]\w*(?:\s+(?:as\s+)?[A-Za-z_]\w*)?)\s+left(?:\s+outer)?\s+join\s+(?P<right>[A-Za-z_]\w*(?:\s+(?:as\s+)?[A-Za-z_]\w*)?)\s+on\s+.+?\s+group\s+by\s+(?P<group>.+?)\s*$",
        flags=re.IGNORECASE | re.DOTALL,
    )
    match = pattern.match(sql)
    if not match:
        return QueryMaterialization(sql, [], [])
    right_aliases = table_ref_names(match.group("right"))
    used_text = f"{match.group('select')} {match.group('group')}".lower()
    if any(re.search(rf"\b{re.escape(alias.lower())}\.", used_text) for alias in right_aliases):
        return QueryMaterialization(sql, [], [])
    select_keys = normalized_top_level_items(match.group("select"))
    group_keys = normalized_top_level_items(match.group("group"))
    if select_keys != group_keys:
        return QueryMaterialization(sql, [], [])
    normalized = f"SELECT {match.group('select').strip()} FROM {match.group('left').strip()} GROUP BY {match.group('group').strip()}"
    return QueryMaterialization(
        normalized,
        ["Removed an unused LEFT JOIN under duplicate-insensitive GROUP BY over left-side columns."],
        [],
    )


def table_ref_names(table_ref: str) -> set[str]:
    tokens = [token for token in re.split(r"\s+", table_ref.strip()) if token and token.lower() != "as"]
    return set(tokens[-1:])


def normalized_top_level_items(text: str) -> list[str]:
    return [re.sub(r"\s+", " ", item.strip()).lower() for item in split_top_level(text)]


def rewrite_contradictory_intersect_to_empty(sql: str, tables: list[Table]) -> QueryMaterialization:
    if not re.search(r"\bintersect\b", sql, flags=re.IGNORECASE):
        return QueryMaterialization(sql, [], [])
    atoms = re.findall(
        r"select\s+\*\s+from\s+(?P<table>[A-Za-z_]\w*)\s+where\s+(?P<column>[A-Za-z_]\w*)\s*=\s*(?P<value>[+-]?\d+|'[^']*')",
        sql,
        flags=re.IGNORECASE,
    )
    if len(atoms) < 2:
        return QueryMaterialization(sql, [], [])
    table_name = atoms[0][0]
    column_name = atoms[0][1]
    values = {value for table, column, value in atoms if table.lower() == table_name.lower() and column.lower() == column_name.lower()}
    if len(values) < 2 or len(values) != len(atoms):
        return QueryMaterialization(sql, [], [])
    table = find_table(tables, table_name)
    if table is None:
        return QueryMaterialization(
            sql,
            [],
            ["Could not resolve contradictory INTERSECT table for typed-empty canonicalization."],
        )
    select_exprs = [f"{table.name}.{column.name}" for column in table.columns]
    normalized = f"SELECT {', '.join(select_exprs)} FROM {table.name} AS {table.name} WHERE 1 = 0"
    return QueryMaterialization(
        normalized,
        ["Canonicalized mutually contradictory SELECT * INTERSECT predicates to a typed empty projection."],
        [],
    )


def unwrap_select_star_derived_union_all(sql: str) -> QueryMaterialization:
    prefix = re.match(r"^\s*select\s+\*\s+from\s*\(", sql, flags=re.IGNORECASE)
    if not prefix:
        return QueryMaterialization(sql, [], [])
    open_index = sql.find("(", prefix.start())
    close_index = find_matching_paren(sql, open_index)
    if close_index is None:
        return QueryMaterialization(sql, [], [])
    suffix = sql[close_index + 1 :].strip()
    if not re.fullmatch(r"as\s+[A-Za-z_]\w*", suffix, flags=re.IGNORECASE):
        return QueryMaterialization(sql, [], [])
    body = strip_balanced_outer_parentheses(sql[open_index + 1 : close_index].strip())
    if not re.search(r"\bunion\s+all\b", body, flags=re.IGNORECASE):
        return QueryMaterialization(sql, [], [])
    if re.search(r"\border\s+by\b|\blimit\b|\boffset\b|\bfetch\b", mask_string_literals(body), flags=re.IGNORECASE):
        return QueryMaterialization(sql, [], [])
    body = unwrap_union_operand_parentheses(body)
    return QueryMaterialization(
        body,
        ["Unwrapped SELECT * over a derived UNION ALL relation because the alias is not referenced."],
        [],
    )


def strip_balanced_outer_parentheses(text: str) -> str:
    normalized = text.strip()
    while normalized.startswith("(") and normalized.endswith(")"):
        close_index = find_matching_paren(normalized, 0)
        if close_index != len(normalized) - 1:
            break
        normalized = normalized[1:-1].strip()
    return normalized


def unwrap_union_operand_parentheses(sql: str) -> str:
    normalized = sql.strip()
    while True:
        updated = re.sub(
            r"\(\s*(select\b[^()]*?\bfrom\b[^()]*?)\s*\)",
            lambda match: match.group(1).strip(),
            normalized,
            flags=re.IGNORECASE | re.DOTALL,
        )
        if updated == normalized:
            return normalized
        normalized = updated


def remove_unconsumed_order_by(sql: str) -> QueryMaterialization:
    normalized = strip_order_by_without_limit(sql)
    if normalized == sql:
        return QueryMaterialization(sql, [], [])
    return QueryMaterialization(
        normalized,
        ["Removed ORDER BY clauses without LIMIT/OFFSET/FETCH under unordered relation equivalence."],
        [],
    )


def fold_integer_constant_arithmetic(sql: str) -> QueryMaterialization:
    transformations: list[str] = []
    add_sub_pattern = re.compile(r"(?<![\w.])([+-]?\d+)\s*([+-])\s*([+-]?\d+)(?![\w.])")
    div_pattern = re.compile(r"(?<![\w.])([+-]?\d+)\s*/\s*([+-]?\d+)(?![\w.])")
    normalized = sql
    while True:
        updated = sub_starting_outside_string_literals(div_pattern, fold_exact_integer_division_match, normalized)
        updated = sub_starting_outside_string_literals(add_sub_pattern, fold_integer_arithmetic_match, updated)
        if updated == normalized:
            break
        normalized = updated
    if normalized != sql:
        transformations.append("Constant-folded exact integer literal arithmetic expressions for Cosette's parser.")
    return QueryMaterialization(normalized, transformations, [])


def fold_integer_arithmetic_match(match: re.Match) -> str:
    left = int(match.group(1))
    op = match.group(2)
    right = int(match.group(3))
    return str(left + right if op == "+" else left - right)


def fold_exact_integer_division_match(match: re.Match) -> str:
    left = int(match.group(1))
    right = int(match.group(2))
    if right == 0 or left % right != 0:
        return match.group(0)
    return str(left // right)


def drop_constant_group_by_keys(sql: str) -> QueryMaterialization:
    transformations: list[str] = []
    normalized = sql
    pieces: list[str] = []
    last = 0
    changed = False
    for match in re.finditer(r"\bgroup\s+by\b", normalized, flags=re.IGNORECASE):
        if overlaps_any_span(match.start(), match.end(), string_literal_spans(normalized)):
            continue
        end = find_clause_boundary(normalized, match.end(), ("having", "order", "limit", "offset", "fetch", "union"))
        group_body = normalized[match.end():end].strip()
        keys = split_top_level(group_body)
        if len(keys) <= 1:
            continue
        retained = [key.strip() for key in keys if key.strip() and not is_constant_group_key(key)]
        if not retained or len(retained) == len(keys):
            continue
        pieces.append(normalized[last:match.start()])
        pieces.append("GROUP BY " + ", ".join(retained))
        last = end
        changed = True
    if not changed:
        return QueryMaterialization(sql, [], [])
    pieces.append(normalized[last:])
    transformations.append("Dropped constant GROUP BY keys that do not affect SQL bag aggregation groups.")
    return QueryMaterialization("".join(pieces), transformations, [])


def is_constant_group_key(key: str) -> bool:
    stripped = key.strip()
    if re.fullmatch(r"[+-]?\d+", stripped):
        return True
    if re.fullmatch(r"'(?:''|[^'])*'", stripped):
        return True
    if re.fullmatch(r"[+-]?\d+(?:\s*[+-]\s*[+-]?\d+)+", stripped):
        return True
    return False


def rewrite_simple_cases(sql: str) -> QueryMaterialization:
    transformations: list[str] = []
    normalized = sql

    constant_equality_pattern = re.compile(
        r"\bcase\s+when\s+(?P<left>'[^']*'|[+-]?\d+)\s*=\s*(?P<right>'[^']*'|[+-]?\d+)\s+then\s+(?P<then>.+?)\s+else\s+(?P<else>.+?)\s+end\b",
        flags=re.IGNORECASE | re.DOTALL,
    )

    def replace_constant_equality_case(match: re.Match) -> str:
        left = match.group("left")
        right = match.group("right")
        return match.group("then").strip() if left == right else match.group("else").strip()

    updated = sub_starting_outside_string_literals(constant_equality_pattern, replace_constant_equality_case, normalized)
    if updated != normalized:
        transformations.append("Folded CASE with row-independent literal equality predicate.")
        normalized = updated

    patterns = (
        (
            re.compile(
                r"\bcase\s+when\s+false\s+then\s+(?P<then>.+?)\s+else\s+(?P<else>.+?)\s+end\b",
                flags=re.IGNORECASE | re.DOTALL,
            ),
            "else",
            "Folded CASE WHEN FALSE to its ELSE branch.",
        ),
        (
            re.compile(
                r"\bcase\s+when\s+true\s+then\s+(?P<then>.+?)\s+else\s+(?P<else>.+?)\s+end\b",
                flags=re.IGNORECASE | re.DOTALL,
            ),
            "then",
            "Folded CASE WHEN TRUE to its THEN branch.",
        ),
    )
    for pattern, group, message in patterns:
        updated = sub_outside_string_literals(
            pattern,
            lambda match: match.group(group).strip(),
            normalized,
        )
        if updated != normalized:
            transformations.append(message)
            normalized = updated

    where_boolean_pattern = re.compile(
        r"(?P<prefix>\bwhere\s+)\bcase\s+when\s+(?P<predicate>.+?)\s+then\s+true\s+else\s+false\s+end\b(?P<tail>\s*(?:group\s+by|having|order\s+by|limit|offset|fetch|$))",
        flags=re.IGNORECASE | re.DOTALL,
    )

    def replace_where_boolean_case(match: re.Match) -> str:
        return f"{match.group('prefix')}({match.group('predicate').strip()}){match.group('tail')}"

    updated = sub_outside_string_literals(where_boolean_pattern, replace_where_boolean_case, normalized)
    if updated != normalized:
        transformations.append("Rewrote WHERE CASE WHEN p THEN TRUE ELSE FALSE END to predicate p.")
        normalized = updated
    return QueryMaterialization(normalized, dedupe(transformations), [])


def rewrite_safe_casts(sql: str) -> QueryMaterialization:
    transformations: list[str] = []
    normalized = sql
    integer_target = r"(?:integer|int|bigint)"

    literal_pattern = re.compile(
        rf"\bcast\s*\(\s*(?P<value>[+-]?\d+)\s+as\s+{integer_target}\s*\)",
        flags=re.IGNORECASE,
    )
    updated = sub_outside_string_literals(literal_pattern, lambda match: match.group("value"), normalized)
    if updated != normalized:
        transformations.append("Erased exact integer literal casts to integer types.")
        normalized = updated

    expression_pattern = re.compile(
        rf"\bcast\s*\(\s*(?P<expr>[A-Za-z_][\w.]*\s*(?:[+*-]\s*(?:[A-Za-z_][\w.]*|[+-]?\d+)\s*)*)\s+as\s+{integer_target}\s*\)",
        flags=re.IGNORECASE,
    )
    updated = sub_outside_string_literals(
        expression_pattern,
        lambda match: match.group("expr").strip(),
        normalized,
    )
    if updated != normalized:
        transformations.append("Erased integer casts around integer-only arithmetic expressions.")
        normalized = updated

    return QueryMaterialization(normalized, dedupe(transformations), [])


def remove_frontend_order_limit(sql: str) -> QueryMaterialization:
    blockers: list[str] = []
    transformations: list[str] = []
    normalized = sql
    scanned = mask_string_literals(normalized)
    has_limit = bool(re.search(r"\blimit\b|\boffset\b|\bfetch\b", scanned, flags=re.IGNORECASE))
    has_order = bool(re.search(r"\border\s+by\b", scanned, flags=re.IGNORECASE))
    if has_limit:
        if is_scalar_aggregate_query(normalized):
            normalized = sub_starting_outside_string_literals(
                re.compile(r"\s+order\s+by\s+.*?(?=\s+limit\b)", flags=re.IGNORECASE | re.DOTALL),
                "",
                normalized,
            )
            normalized = sub_starting_outside_string_literals(
                re.compile(r"\s+limit\s+\d+\s*$", flags=re.IGNORECASE),
                "",
                normalized,
            )
            transformations.append(
                "Removed ORDER BY/LIMIT from scalar aggregate query because it returns at most one row."
            )
        else:
            blockers.append("LIMIT/OFFSET/FETCH has cardinality semantics not expressible in Cosette's SQL subset.")
    elif has_order:
        updated = strip_order_by_without_limit(normalized)
        if updated != normalized:
            normalized = updated
            transformations.append(
                "Removed ORDER BY clauses without LIMIT/OFFSET under unordered relation equivalence."
            )
        else:
            blockers.append(
                "ORDER BY is retained because dropping it is only safe for explicitly order-insensitive goals."
            )
    return QueryMaterialization(normalized, transformations, blockers)


def is_scalar_aggregate_query(sql: str) -> bool:
    lowered = sql.lower()
    if " group by " in lowered:
        return False
    if not re.search(r"\b(count|sum|avg|min|max)\s*\(", lowered):
        return False
    return bool(re.search(r"\s+limit\s+[1-9]\d*\s*$", lowered))


def strip_top_level_order_by(sql: str) -> str:
    lowered = sql.lower()
    depth = 0
    quote: str | None = None
    for index, char in enumerate(sql):
        if quote:
            if char == quote:
                quote = None
            continue
        if char == "'":
            quote = char
        elif char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
        elif depth == 0 and lowered.startswith(" order by ", index):
            clause = sql[index:]
            if re.search(r"\blimit\b|\boffset\b|\bfetch\b", mask_string_literals(clause), flags=re.IGNORECASE):
                return sql
            return sql[:index].rstrip()
    return sql


def strip_order_by_without_limit(sql: str) -> str:
    normalized = strip_top_level_order_by(sql)
    if normalized != sql:
        return normalized

    spans = string_literal_spans(sql)
    order_pattern = re.compile(r"\border\s+by\b", flags=re.IGNORECASE)
    pieces: list[str] = []
    last = 0
    changed = False
    for match in order_pattern.finditer(sql):
        if overlaps_any_span(match.start(), match.end(), spans):
            continue
        end = find_order_clause_end(sql, match.start())
        if end is None:
            continue
        clause = sql[match.start():end]
        if re.search(r"\blimit\b|\boffset\b|\bfetch\b", mask_string_literals(clause), flags=re.IGNORECASE):
            continue
        pieces.append(sql[last:match.start()])
        last = end
        changed = True
    if not changed:
        return sql
    pieces.append(sql[last:])
    return re.sub(r"\s+\)", ")", "".join(pieces))


def find_order_clause_end(sql: str, start: int) -> int | None:
    depth = 0
    quote: str | None = None
    for index in range(start, len(sql)):
        char = sql[index]
        if quote:
            if char == quote:
                quote = None
            continue
        if char == "'":
            quote = char
            continue
        if char == "(":
            depth += 1
        elif char == ")":
            if depth == 0:
                return index
            depth -= 1
    return len(sql)


def rewrite_comparisons(sql: str, tables: list[Table], facts: SourceFacts) -> QueryMaterialization:
    transformations: list[str] = []
    blockers: list[str] = []
    normalized = rewrite_between(sql)
    if normalized != sql:
        transformations.append("Rewrote BETWEEN predicates to Cosette-supported <, >, = predicates.")
    sql = normalized

    normalized = rewrite_literal_in_lists(sql)
    if normalized != sql:
        transformations.append("Rewrote finite literal IN lists to equality disjunctions.")
    sql = normalized

    atom = r"(?:[A-Za-z_][\w.]*|[+-]?\d+|'[^']*'|\([^()]+\))"
    simple = rf"{atom}(?:\s*[+-]\s*{atom})?"
    before_comparison_rewrites = sql
    sql = sub_starting_outside_string_literals(
        re.compile(rf"({simple})\s*<=\s*({simple})"),
        r"(\1 < \2 OR \1 = \2)",
        sql,
    )
    sql = sub_starting_outside_string_literals(
        re.compile(rf"({simple})\s*>=\s*({simple})"),
        r"(\1 > \2 OR \1 = \2)",
        sql,
    )
    sql = sub_starting_outside_string_literals(
        re.compile(rf"({simple})\s*(?:<>|!=)\s*({simple})"),
        r"NOT (\1 = \2)",
        sql,
    )
    if re.search(r"<=|>=|!=|<>", mask_string_literals(sql)):
        blockers.append("Some unsupported comparison operators could not be rewritten safely.")
    elif sql != before_comparison_rewrites:
        transformations.append("Rewrote <=, >=, and <>/!= comparisons to Cosette-supported predicates where present.")
    return QueryMaterialization(sql, transformations, blockers)


def rewrite_literal_not_in_lists(sql: str, tables: list[Table], facts: SourceFacts) -> QueryMaterialization:
    transformations: list[str] = []
    blockers: list[str] = []
    pattern = re.compile(
        r"\b(?P<left>[A-Za-z_][\w.]*)\s+not\s+in\s*\(\s*(?P<values>(?:'[^']*'|[+-]?\d+)(?:\s*,\s*(?:'[^']*'|[+-]?\d+))*)\s*\)",
        flags=re.IGNORECASE,
    )

    def replace(match: re.Match) -> str:
        left = match.group("left")
        if not is_not_null_expr(left, sql, tables, facts):
            blockers.append(
                f"NOT IN literal list on {left} was retained because the left expression is not proven NOT NULL."
            )
            return match.group(0)
        values = [value.strip() for value in match.group("values").split(",")]
        if any(value.lower() == "null" for value in values):
            blockers.append("NOT IN literal list containing NULL was retained.")
            return match.group(0)
        atoms = " OR ".join(f"{left} = {value}" for value in values)
        transformations.append("Rewrote NOT IN over a non-null finite literal list to NOT of equality disjunction.")
        return f"NOT ({atoms})"

    normalized = sub_starting_outside_string_literals(pattern, replace, sql)
    return QueryMaterialization(normalized, dedupe(transformations), dedupe(blockers))


def rewrite_between(sql: str) -> str:
    operand = r"[A-Za-z_][\w.]*"
    scalar = r"(?:[+-]?\d+|'[^']*'|[A-Za-z_][\w.]*)"
    bound = rf"(?:{scalar}(?:\s*[+-]\s*{scalar})?)"
    pattern = re.compile(
        rf"\b({operand})\s+between\s+({bound})\s+and\s+({bound})",
        flags=re.IGNORECASE,
    )
    return sub_starting_outside_string_literals(
        pattern,
        r"((\1 > \2 OR \1 = \2) AND (\1 < \3 OR \1 = \3))",
        sql,
    )


def rewrite_literal_in_lists(sql: str) -> str:
    atom = r"[A-Za-z_][\w.]*"
    literal = r"(?:\d+|'[^']*')"
    pattern = re.compile(rf"\b({atom})\s+in\s*\(\s*({literal}(?:\s*,\s*{literal})*)\s*\)", flags=re.IGNORECASE)

    def replace(match: re.Match) -> str:
        left = match.group(1)
        values = [value.strip() for value in match.group(2).split(",")]
        return "(" + " OR ".join(f"{left} = {value}" for value in values) + ")"

    return sub_starting_outside_string_literals(pattern, replace, sql)


def is_not_null_expr(expr: str, sql: str, tables: list[Table], facts: SourceFacts) -> bool:
    normalized = expr.strip().strip('"`[]')
    scope = single_table_scope(sql, tables)
    if scope is None:
        return False
    alias, table = scope
    if "." in normalized:
        qualifier, column = normalized.rsplit(".", 1)
        if qualifier.lower() not in {alias.lower(), table.name.lower()}:
            return False
        return f"{table.name}__{column}".upper() in facts.not_null

    if not any(column.name.lower() == normalized.lower() for column in table.columns):
        return False
    return f"{table.name}__{normalized}".upper() in facts.not_null or f"{alias}__{normalized}".upper() in facts.not_null


def mask_string_literals(sql: str) -> str:
    result: list[str] = []
    index = 0
    while index < len(sql):
        char = sql[index]
        if char != "'":
            result.append(char)
            index += 1
            continue
        result.append("''")
        index += 1
        while index < len(sql):
            if sql[index] == "'":
                index += 1
                if index < len(sql) and sql[index] == "'":
                    index += 1
                    continue
                break
            index += 1
    return "".join(result)


def string_literal_spans(sql: str) -> list[tuple[int, int]]:
    spans: list[tuple[int, int]] = []
    index = 0
    while index < len(sql):
        if sql[index] != "'":
            index += 1
            continue
        start = index
        index += 1
        while index < len(sql):
            if sql[index] == "'":
                index += 1
                if index < len(sql) and sql[index] == "'":
                    index += 1
                    continue
                break
            index += 1
        spans.append((start, index))
    return spans


def overlaps_any_span(start: int, end: int, spans: list[tuple[int, int]]) -> bool:
    return any(start < span_end and end > span_start for span_start, span_end in spans)


def sub_outside_string_literals(
    pattern: re.Pattern,
    replacement: str | Callable[[re.Match], str],
    sql: str,
) -> str:
    spans = string_literal_spans(sql)
    pieces: list[str] = []
    last = 0
    for match in pattern.finditer(sql):
        if overlaps_any_span(match.start(), match.end(), spans):
            continue
        pieces.append(sql[last : match.start()])
        if callable(replacement):
            pieces.append(replacement(match))
        else:
            pieces.append(match.expand(replacement))
        last = match.end()
    if last == 0:
        return sql
    pieces.append(sql[last:])
    return "".join(pieces)


def sub_starting_outside_string_literals(
    pattern: re.Pattern,
    replacement: str | Callable[[re.Match], str],
    sql: str,
) -> str:
    spans = string_literal_spans(sql)
    pieces: list[str] = []
    last = 0
    for match in pattern.finditer(sql):
        if overlaps_any_span(match.start(), match.start() + 1, spans):
            continue
        pieces.append(sql[last : match.start()])
        if callable(replacement):
            pieces.append(replacement(match))
        else:
            pieces.append(match.expand(replacement))
        last = match.end()
    if last == 0:
        return sql
    pieces.append(sql[last:])
    return "".join(pieces)


def add_safe_table_aliases(sql: str, tables: list[Table]) -> QueryMaterialization:
    table_names = {table.name.lower(): table.name for table in tables}
    transformations: list[str] = []

    def add_alias(match: re.Match) -> str:
        prefix = match.group(1)
        table = match.group(2)
        canonical = table_names.get(table.lower())
        if canonical is None:
            return match.group(0)
        transformations.append(f"Added self-alias for table {canonical}.")
        return f"{prefix}{table} AS {table}"

    boundary = r"(?=\s*(?:,|\bwhere\b|\bgroup\b|\bhaving\b|\border\b|\blimit\b|\boffset\b|\bunion\b|\)|$))"
    pattern = re.compile(rf"(\b(?:from|join)\s+|,\s+)([A-Za-z_]\w*){boundary}", flags=re.IGNORECASE)
    normalized = sub_starting_outside_string_literals(pattern, add_alias, sql)
    return QueryMaterialization(normalized, dedupe(transformations), [])


def lower_simple_inner_joins(sql: str) -> QueryMaterialization:
    transformations: list[str] = []
    normalized = sql
    while True:
        updated, changed = lower_one_simple_inner_join_scope(normalized)
        if not changed:
            break
        normalized = updated
    if normalized != sql:
        transformations.append("Lowered simple INNER JOIN ... ON chains to comma products with WHERE conjuncts.")
    return QueryMaterialization(normalized, dedupe(transformations), [])


def lower_one_simple_inner_join_scope(sql: str) -> tuple[str, bool]:
    from_match = find_top_level_keyword(sql, "from")
    if from_match is None:
        return sql, False
    from_end = from_match + len("from")
    segment_end = find_clause_boundary(sql, from_end, ("where", "group", "having", "order", "limit", "offset", "fetch", "union"))
    from_segment = sql[from_end:segment_end]
    if not re.search(r"\binner\s+join\b", from_segment, flags=re.IGNORECASE):
        return sql, False
    if "(" in from_segment or ")" in from_segment:
        return lower_parenthesized_product_inner_join(sql, from_end, segment_end, from_segment)
    lowered = parse_simple_inner_join_segment(from_segment)
    if lowered is None:
        return sql, False
    table_refs, conditions = lowered
    tail = sql[segment_end:]
    where_match = re.match(r"\s*where\b", tail, flags=re.IGNORECASE)
    replacement = " " + ", ".join(table_refs)
    if where_match:
        where_start = segment_end + where_match.end()
        where_end = find_clause_boundary(sql, where_start, ("group", "having", "order", "limit", "offset", "fetch", "union"))
        existing = sql[where_start:where_end].strip()
        condition = " AND ".join(conditions + ([existing] if existing else []))
        return sql[:from_end] + replacement + " WHERE " + condition + suffix_with_space(sql[where_end:]), True
    condition = " AND ".join(conditions)
    return sql[:from_end] + replacement + " WHERE " + condition + suffix_with_space(sql[segment_end:]), True


def lower_parenthesized_product_inner_join(
    sql: str,
    from_end: int,
    segment_end: int,
    from_segment: str,
) -> tuple[str, bool]:
    table_ref = r"[A-Za-z_]\w*(?:\s+(?:AS\s+)?[A-Za-z_]\w*)?"
    pattern = re.compile(
        rf"^\s*(?P<left>{table_ref})\s+inner\s+join\s+\((?P<product>[^()]+)\)\s+on\s+(?P<condition>.+?)\s*$",
        flags=re.IGNORECASE | re.DOTALL,
    )
    match = pattern.match(from_segment)
    if not match:
        return sql, False
    product_items = [item.strip() for item in split_top_level(match.group("product"))]
    if not product_items or any(not re.fullmatch(table_ref, item, flags=re.IGNORECASE) for item in product_items):
        return sql, False
    table_refs = [match.group("left").strip()] + product_items
    condition = match.group("condition").strip()
    replacement = " " + ", ".join(table_refs)
    tail = sql[segment_end:]
    where_match = re.match(r"\s*where\b", tail, flags=re.IGNORECASE)
    if where_match:
        where_start = segment_end + where_match.end()
        where_end = find_clause_boundary(sql, where_start, ("group", "having", "order", "limit", "offset", "fetch", "union"))
        existing = sql[where_start:where_end].strip()
        merged = " AND ".join([condition] + ([existing] if existing else []))
        return sql[:from_end] + replacement + " WHERE " + merged + suffix_with_space(sql[where_end:]), True
    return sql[:from_end] + replacement + " WHERE " + condition + suffix_with_space(tail), True


def parse_simple_inner_join_segment(segment: str) -> tuple[list[str], list[str]] | None:
    table_ref = r"[A-Za-z_]\w*(?:\s+(?:AS\s+)?(?!INNER\b|JOIN\b|ON\b|WHERE\b|GROUP\b|HAVING\b|ORDER\b|LIMIT\b|OFFSET\b|FETCH\b|UNION\b)[A-Za-z_]\w*)?"
    first = re.match(rf"\s*(?P<table>{table_ref})\s+", segment, flags=re.IGNORECASE)
    if not first:
        return None
    table_refs = [first.group("table").strip()]
    conditions: list[str] = []
    pos = first.end()
    join_re = re.compile(
        rf"\s*inner\s+join\s+(?P<table>{table_ref})\s+on\s+(?P<condition>.*?)(?=(?:\s+inner\s+join\s+)|\s*$)",
        flags=re.IGNORECASE | re.DOTALL,
    )
    while pos < len(segment):
        if not segment[pos:].strip():
            break
        match = join_re.match(segment, pos)
        if not match:
            return None
        condition = match.group("condition").strip()
        if not condition:
            return None
        table_refs.append(match.group("table").strip())
        conditions.append(condition)
        pos = match.end()
    return (table_refs, conditions) if conditions else None


def suffix_with_space(suffix: str) -> str:
    if not suffix:
        return ""
    if suffix[0].isspace():
        return suffix
    return " " + suffix


def qualify_single_table_columns(sql: str, tables: list[Table]) -> QueryMaterialization:
    scope = single_table_scope(sql, tables)
    if scope is None:
        return QueryMaterialization(sql, [], [])
    alias, table = scope
    columns = {column.name for column in table.columns}
    if not columns:
        return QueryMaterialization(sql, [], [])
    transformations: list[str] = []
    normalized = sql
    for column in sorted(columns, key=len, reverse=True):
        pattern = re.compile(rf"(?<![.\w]){re.escape(column)}(?!\w)", flags=re.IGNORECASE)

        def replace(match: re.Match) -> str:
            before = normalized[: match.start()]
            after = normalized[match.end() : match.end() + 1]
            if after == ".":
                return match.group(0)
            if is_from_table_name_context(before):
                return match.group(0)
            if re.search(r"\bas\s+$", before, flags=re.IGNORECASE):
                return match.group(0)
            if is_from_alias_declaration_context(before):
                return match.group(0)
            return f"{alias}.{match.group(0)}"

        updated = sub_outside_string_literals(pattern, replace, normalized)
        if updated != normalized:
            transformations.append(f"Qualified unqualified column {column} with {alias}.")
            normalized = updated
    return QueryMaterialization(normalized, dedupe(transformations), [])


def is_from_table_name_context(prefix: str) -> bool:
    tail = prefix[-120:]
    return bool(re.search(r"\b(?:from|join)\s*$", tail, flags=re.IGNORECASE))


def is_from_alias_declaration_context(prefix: str) -> bool:
    tail = prefix[-200:]
    return bool(
        re.search(r"\b(?:from|join)\s+[A-Za-z_]\w*\s+(?:as\s+)?$", tail, flags=re.IGNORECASE)
        or re.search(r",\s*[A-Za-z_]\w*\s+(?:as\s+)?$", tail, flags=re.IGNORECASE)
    )


def single_table_scope(sql: str, tables: list[Table]) -> tuple[str, Table] | None:
    if re.search(r"\bjoin\b|\bunion\b", mask_string_literals(sql), flags=re.IGNORECASE):
        return None
    if re.search(r"\(\s*select\b", sql, flags=re.IGNORECASE):
        return None
    table_by_name = {table.name.lower(): table for table in tables}
    match = re.search(
        r"\bfrom\s+([A-Za-z_]\w*)(?:\s+(?:as\s+)?([A-Za-z_]\w*))?(?=\s*(?:where|group|having|order|limit|offset|$|\)))",
        sql,
        flags=re.IGNORECASE,
    )
    if not match:
        return None
    table = table_by_name.get(match.group(1).lower())
    if table is None:
        return None
    alias = match.group(2) or match.group(1)
    if alias.lower() in COSETTE_SQL_KEYWORDS:
        return None
    return alias, table


def find_top_level_keyword(sql: str, keyword: str, start: int = 0) -> int | None:
    lowered = sql.lower()
    needle = keyword.lower()
    depth = 0
    quote: str | None = None
    index = start
    while index < len(sql):
        char = sql[index]
        if quote:
            if char == quote:
                quote = None
            index += 1
            continue
        if char == "'":
            quote = char
            index += 1
            continue
        if char == "(":
            depth += 1
            index += 1
            continue
        if char == ")":
            depth = max(0, depth - 1)
            index += 1
            continue
        if depth == 0 and lowered.startswith(needle, index):
            left_ok = index == 0 or not (sql[index - 1].isalnum() or sql[index - 1] == "_")
            right = index + len(needle)
            right_ok = right >= len(sql) or not (sql[right].isalnum() or sql[right] == "_")
            if left_ok and right_ok:
                return index
        index += 1
    return None


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


def first_query(sql: str) -> str:
    stripped = strip_comments(sql).strip()
    stripped = re.sub(r";\s*$", "", stripped)
    return re.sub(r"\s+", " ", stripped)


def strip_comments(sql: str) -> str:
    sql = re.sub(r"--[^\n]*", "", sql)
    sql = re.sub(r"/\*.*?\*/", "", sql, flags=re.DOTALL)
    return sql


def unquote_identifier(value: str) -> str:
    value = value.strip()
    if len(value) >= 2 and value[0] in ('"', "`", "[") and value[-1] in ('"', "`", "]"):
        return value[1:-1]
    return value


def write_json(path: Path, payload: dict) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")


def read_json_if_exists(path: Path) -> dict | None:
    if not path.exists():
        return None
    return json.loads(path.read_text(errors="replace"))


if __name__ == "__main__":
    raise SystemExit(main())
