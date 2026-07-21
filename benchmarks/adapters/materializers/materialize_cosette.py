#!/usr/bin/env python3
import argparse
import hashlib
import itertools
import json
import re
import shutil
import subprocess
import sys
from collections import Counter
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from materializer_sql import (
    ASCII_SQL_WHITESPACE,
    find_matching_paren,
    mask_sql_regions,
    normalize_sql_layout,
    parse_schema,
    protected_sql_regions,
    split_top_level_commas,
    substitute_unprotected,
    transform_double_quoted_identifiers,
)


ROOT = Path(__file__).resolve().parents[3]
CALCITE_BINDING_ANALYZER = (
    Path(__file__).resolve().parents[3]
    / "benchmarks/scripts/cosette-calcite-binding"
)
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
_CONSTANT_TRUE_INTEGER_CASE_PATTERN = re.compile(
    r"\bCASE\s+WHEN\s+"
    r"(?P<left>'(?:''|[^'])*'|[+-]?\d+)\s*=\s*"
    r"(?P<right>'(?:''|[^'])*'|[+-]?\d+)\s+THEN\s+"
    r"(?P<then>[+-]?\d+)\s+ELSE\s+NULL\s+END\b",
    flags=re.IGNORECASE,
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
    attestations: list[dict[str, Any]] = field(default_factory=list)

    @property
    def blockers(self) -> list[str]:
        """Backward-compatible aggregate view used by focused unit tests."""

        return dedupe(self.syntax_blockers + self.semantic_blockers)


@dataclass(frozen=True)
class CaseCompatibility:
    status: str
    syntax_compatibility: str
    semantic_profile_compatibility: str


@dataclass(frozen=True)
class CalciteIrSource:
    rel: dict[str, Any]
    path: Path
    sha256: str
    source_sql_sha256: str
    bound_source_sql_sha256: str
    embedded_sql_sha256: str
    schema_sha256: str
    authority_binding: dict[str, Any]
    representation_binding: dict[str, Any]


@dataclass(frozen=True)
class RexExpr:
    kind: str
    value: str
    args: tuple["RexExpr", ...] = ()
    type_name: str | None = None


@dataclass(frozen=True)
class IrField:
    expression: str
    type_name: str
    nullable: bool
    constant: bool = False


@dataclass
class FlatCosettePlan:
    from_items: list[str]
    predicates: list[str]
    fields: list[IrField]
    group_by: list[str] | None = None
    attestations: list[dict[str, Any]] = field(default_factory=list)


@dataclass(frozen=True)
class CompiledCosetteQuery:
    sql: str
    attestations: list[dict[str, Any]]
    flat_plan: FlatCosettePlan | None = None


@dataclass(frozen=True)
class SingletonValuesGroupAst:
    select_items: list[str]
    table: Table
    base_alias: str
    retained_group: list[str]
    values_alias_column: str
    literal: str


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
    schema_bytes = (case_dir / "schema.sql").read_bytes()
    sql1_bytes = (case_dir / "sql1.sql").read_bytes()
    sql2_bytes = (case_dir / "sql2.sql").read_bytes()
    schema_sql = schema_bytes.decode("utf-8")
    sql1 = normalize_query_payload(sql1_bytes.decode("utf-8"))
    sql2 = normalize_query_payload(sql2_bytes.decode("utf-8"))
    tables = parse_tables(schema_sql)
    if not tables:
        raise ValueError("no CREATE TABLE declarations were recognized")

    source_metadata = read_required_metadata(case_dir / "metadata.json")
    q1, q2, lowering_metadata = materialize_pair(
        sql1,
        sql2,
        tables,
        source_metadata,
    )
    syntax_blockers = dedupe(
        q1.syntax_blockers
        + q2.syntax_blockers
        + detect_missing_base_table_aliases(q1.sql, tables)
        + detect_missing_base_table_aliases(q2.sql, tables)
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
    cosette_path = target / "case.cos"
    cosette_path.write_text(cosette, encoding="utf-8")
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
        "cosetteFileSha256": hashlib.sha256(
            cosette_path.read_bytes()
        ).hexdigest(),
        "sourceSchemaSha256": hashlib.sha256(schema_bytes).hexdigest(),
        "sourceSql1Sha256": hashlib.sha256(sql1_bytes).hexdigest(),
        "sourceSql2Sha256": hashlib.sha256(sql2_bytes).hexdigest(),
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
        "compatibilityLowering": lowering_metadata,
        "loweringNote": (
            "Cosette's public DSL exposes int/string scalar sorts. SQL scalar "
            "types are therefore lowered to int or string for frontend testing; "
            "constraints not expressible in the DSL remain in the source metadata. "
            "The Cosette SQL parser is narrower than the benchmark SQL corpus. "
            "A compatibility lowering is admitted only when an exact generated "
            "Calcite relational tree satisfies the rule-specific side conditions. "
            "Standard syntax reserialization and semantic preprocessing are listed "
            "separately in compatibilityLowering. Cases outside those rules are "
            "emitted unchanged for an auditable run log."
        ),
    }
    metadata["sourceMetadata"] = source_metadata
    write_json(target / "metadata.json", metadata)
    return CaseCompatibility(
        status=status,
        syntax_compatibility=syntax_compatibility,
        semantic_profile_compatibility=semantic_profile_compatibility,
    )


def materialize_pair(
    sql1: str,
    sql2: str,
    tables: list[Table],
    source_metadata: dict[str, Any],
) -> tuple[QueryMaterialization, QueryMaterialization, dict[str, Any]]:
    """Lower a pair only when both exact Calcite trees pass the same gate.

    Cosette is a relation-algebra prover behind a deliberately small SQL parser.
    Reprinting an already-bound Calcite tree is a syntax bridge; a handful of
    additional reductions (for example a row-independent GROUP key) are semantic
    preprocessing and carry their own side-condition attestations.  We never
    lower just one side when the other side cannot be certified.
    """

    original_q1 = materialize_query(sql1)
    original_q2 = materialize_query(sql2)
    sources = load_calcite_ir_pair(
        source_metadata,
        (sql1, sql2),
        tables,
    )
    metadata: dict[str, Any] = {
        "version": 1,
        "authority": "exact-generated-calcite-ir",
        "applied": False,
        "pairAdmission": {},
        "queries": {"q1": [], "q2": []},
    }
    if sources is None:
        metadata["reason"] = "exact Calcite IR pair is unavailable"
        return original_q1, original_q2, metadata

    before, after = sources
    signature1 = output_type_signature(before.rel)
    signature2 = output_type_signature(after.rel)
    type_equal = signature_types(signature1) == signature_types(signature2)
    nullable_equal = signature_nullability(signature1) == signature_nullability(
        signature2
    )
    pair_specific_blockers = detect_pair_semantic_blockers(sql1, sql2)
    metadata["pairAdmission"] = {
        "q1Ir": ir_source_metadata(before),
        "q2Ir": ir_source_metadata(after),
        "q1OutputSignature": signature1,
        "q2OutputSignature": signature2,
        "orderedTypesEqual": type_equal,
        "nullableAnnotationsEqual": nullable_equal,
        "nullableAnnotationsAreNotFormalOutputAttributes": True,
        "pairSpecificSemanticBlockers": pair_specific_blockers,
    }
    aggregate_typing = {
        "q1": attest_postgres_aggregate_result_types(
            before.rel,
            read_dialect=source_metadata.get("readDialect"),
        ),
        "q2": attest_postgres_aggregate_result_types(
            after.rel,
            read_dialect=source_metadata.get("readDialect"),
        ),
    }
    if any(
        item["status"] != "not-applicable"
        for item in aggregate_typing.values()
    ):
        metadata["pairAdmission"]["sourceAggregateTyping"] = aggregate_typing
    if not type_equal:
        metadata["reason"] = (
            "ordered output SQL types differ; Cosette's int/string collapse must "
            "not erase that observation"
        )
        return original_q1, original_q2, metadata
    if any(item["status"] == "rejected" for item in aggregate_typing.values()):
        metadata["reason"] = (
            "one or both Calcite trees violate the PostgreSQL aggregate "
            "result-type contract"
        )
        return original_q1, original_q2, metadata
    if pair_specific_blockers:
        metadata["reason"] = (
            "the equivalence depends on a source constraint absent from Cosette; "
            "a parser-only rewrite would produce a misleading decision"
        )
        return original_q1, original_q2, metadata

    bag_observation = source_metadata.get("bagSemantics") is True
    normalized_rel1, preprocessing1 = preprocess_cosette_rel(
        before.rel,
        bag_observation=bag_observation,
    )
    normalized_rel2, preprocessing2 = preprocess_cosette_rel(
        after.rel,
        bag_observation=bag_observation,
    )
    normalized_rel1, contradiction1 = (
        preprocess_attested_nonnull_integer_contradiction_filter(
            normalized_rel1,
            tables,
            source_metadata,
        )
    )
    normalized_rel2, contradiction2 = (
        preprocess_attested_nonnull_integer_contradiction_filter(
            normalized_rel2,
            tables,
            source_metadata,
        )
    )
    preprocessing1.extend(contradiction1)
    preprocessing2.extend(contradiction2)
    (
        normalized_rel1,
        normalized_rel2,
        paired_preprocessing1,
        paired_preprocessing2,
    ) = preprocess_paired_where_true_acceptance(
        normalized_rel1,
        normalized_rel2,
    )
    preprocessing1.extend(paired_preprocessing1)
    preprocessing2.extend(paired_preprocessing2)
    compiled1 = compile_cosette_candidate(
        normalized_rel1, tables, sql1, preprocessing1
    )
    compiled2 = compile_cosette_candidate(
        normalized_rel2, tables, sql2, preprocessing2
    )
    if compiled1 is None or compiled2 is None:
        metadata["reason"] = "one or both Calcite trees are outside the admitted lowering rules"
        return original_q1, original_q2, metadata

    compiled1 = CompiledCosetteQuery(
        compiled1.sql,
        preprocessing1 + compiled1.attestations,
        compiled1.flat_plan,
    )
    compiled2 = CompiledCosetteQuery(
        compiled2.sql,
        preprocessing2 + compiled2.attestations,
        compiled2.flat_plan,
    )

    pair_attestation = attest_lowered_pair_safety(
        normalized_rel1,
        normalized_rel2,
        compiled1,
        compiled2,
    )
    if pair_attestation is None:
        metadata["reason"] = (
            "the lowered queries differ without a pair-level NULL/error-preserving "
            "attestation"
        )
        return original_q1, original_q2, metadata

    lowered_q1 = materialize_query(compiled1.sql)
    lowered_q2 = materialize_query(compiled2.sql)
    # Syntax checks apply to the emitted query.  Semantic-profile checks retain
    # the source-query obligations so a successful syntax bridge cannot conceal
    # NULL, overflow, or source-type limitations.
    lowered_q1.semantic_blockers = dedupe(
        original_q1.semantic_blockers + lowered_q1.semantic_blockers
    )
    lowered_q2.semantic_blockers = dedupe(
        original_q2.semantic_blockers + lowered_q2.semantic_blockers
    )
    lowered_q1.attestations = compiled1.attestations
    lowered_q2.attestations = compiled2.attestations
    if lowered_q1.syntax_blockers or lowered_q2.syntax_blockers:
        metadata["reason"] = "the certified lowering still falls outside Cosette's parser surface"
        metadata["queries"] = {
            "q1": compiled1.attestations,
            "q2": compiled2.attestations,
        }
        return original_q1, original_q2, metadata

    all_attestations = compiled1.attestations + compiled2.attestations
    metadata.update(
        {
            "applied": True,
            "queries": {
                "q1": compiled1.attestations,
                "q2": compiled2.attestations,
            },
            "classification": {
                "standardSyntaxLowering": sorted(
                    {
                        item["rule"]
                        for item in all_attestations
                        if item["kind"] == "standard-syntax-lowering"
                    }
                ),
                "semanticPreprocessing": sorted(
                    {
                        item["rule"]
                        for item in all_attestations
                        if item["kind"] == "semantic-preprocessing"
                    }
                ),
            },
            "pairSafety": pair_attestation,
        }
    )
    return lowered_q1, lowered_q2, metadata


_SAFE_AUTHORITY_IDENTIFIER = re.compile(
    r"[A-Za-z_][A-Za-z0-9_]*\Z", flags=re.ASCII
)
_TSQL_DATE_DAY_SOURCE = re.compile(
    r"(?is)(?P<predicate_prefix>\bBETWEEN\s+CAST\s*\(\s*"
    r"(?P<lower_literal>'(?:''|[^'])*')\s+AS\s+DATE\s*\)\s+AND\s*)"
    r"(?P<upper_prefix>\(\s*CAST\s*\(\s*"
    r"(?P<upper_literal>'(?:''|[^'])*')\s+AS\s+DATE\s*\)\s*\+\s*)"
    r"(?P<days>[0-9]+)"
    r"(?P<unit>\s+days\b)?"
    r"(?P<suffix>\s*\))"
)
_TSQL_DATE_DAY_SQLSOLVER = re.compile(
    r"(?is)(?P<predicate_prefix>\bBETWEEN\s+CAST\s*\(\s*"
    r"(?P<lower_literal>'(?:''|[^'])*')\s+AS\s+DATE\s*\)\s+AND\s*)"
    r"(?P<upper_prefix>\(\s*CAST\s*\(\s*"
    r"(?P<upper_literal>'(?:''|[^'])*')\s+AS\s+DATE\s*\)\s*\+\s*)"
    r"(?P<days>[0-9]+)"
    r"(?P<alias>\s+AS\s+days\b)?"
    r"(?P<suffix>\s*\))"
)


def authoritative_identifier_renames(
    source_metadata: dict[str, Any],
) -> dict[str, str] | None:
    """Load the exact SQLSolver alpha-renaming contract, if one is declared.

    The WeTune SQLSolver profile removes SQLGlot's double quotes and consistently
    alpha-renames parser-reserved identifiers.  That is a semantics-preserving
    bridge only when the generated metadata explicitly makes the rename map part
    of its authoritative integrity contract.  Arbitrary case folding, fuzzy SQL
    comparison, and inferred renames are intentionally not admitted here.
    """

    raw = source_metadata.get("renamedIdentifiers")
    if raw is None:
        return None
    if not isinstance(raw, dict) or not raw:
        return None
    contract = source_metadata.get("integrityContract")
    if (
        not isinstance(contract, dict)
        or contract.get("authoritativeForLogos") is not True
        or contract.get("identifierRenames")
        != "metadata.json#/renamedIdentifiers"
        or contract.get("parserFacingDdl") != "schema.sql"
    ):
        raise ValueError(
            "identifier renames lack an authoritative SQLSolver integrity contract"
        )

    renames: dict[str, str] = {}
    folded_sources: set[str] = set()
    folded_targets: set[str] = set()
    for source, target in raw.items():
        if (
            not isinstance(source, str)
            or not isinstance(target, str)
            or _SAFE_AUTHORITY_IDENTIFIER.fullmatch(source) is None
            or _SAFE_AUTHORITY_IDENTIFIER.fullmatch(target) is None
            or source == target
        ):
            raise ValueError("identifier rename map contains an unsafe entry")
        folded_source = source.casefold()
        folded_target = target.casefold()
        if folded_source in folded_sources or folded_target in folded_targets:
            raise ValueError("identifier rename map is not case-fold injective")
        folded_sources.add(folded_source)
        folded_targets.add(folded_target)
        renames[source] = target
    return renames


def _mapped_authority_identifier(
    identifier: Any,
    renames: dict[str, str] | None,
) -> str | None:
    if (
        not isinstance(identifier, str)
        or _SAFE_AUTHORITY_IDENTIFIER.fullmatch(identifier) is None
    ):
        return None
    if renames is None:
        return identifier
    mapped = renames.get(identifier, identifier)
    return mapped if _SAFE_AUTHORITY_IDENTIFIER.fullmatch(mapped) is not None else None


def bind_calcite_query_sql(
    embedded_sql: str,
    expected_sql: str,
    renames: dict[str, str] | None,
) -> dict[str, Any] | None:
    """Bind one IR query to source SQL exactly or by an attested alpha-renaming."""

    normalized_embedded = normalize_query_payload(embedded_sql)
    normalized_expected = normalize_query_payload(expected_sql)
    source_sha = sha256_text(normalized_expected)
    embedded_sha = sha256_text(normalized_embedded)
    if normalized_embedded == normalized_expected:
        return {
            "status": "verified-exact-normalized-sql",
            "policy": "protected-layout-normalization-only",
            "sourceSqlSha256": source_sha,
            "embeddedSqlSha256": embedded_sha,
            "boundEmbeddedSqlSha256": embedded_sha,
            "identifierRenameMapSha256": None,
            "quotedIdentifiersRewritten": 0,
        }
    rewritten_identifiers = 0
    source_spellings: dict[str, str] = {}
    target_origins: dict[str, str] = {}

    def rewrite(identifier: str) -> str:
        nonlocal rewritten_identifiers
        mapped = _mapped_authority_identifier(identifier, renames)
        if mapped is None:
            raise ValueError("Calcite SQL contains an unsafe identifier")
        source_key = identifier.casefold()
        target_key = mapped.casefold()
        if source_spellings.get(source_key, identifier) != identifier:
            raise ValueError("quoted identifiers collide after unquoted case folding")
        if target_origins.get(target_key, identifier) != identifier:
            raise ValueError("identifier alpha-renaming is not case-fold injective")
        source_spellings[source_key] = identifier
        target_origins[target_key] = identifier
        rewritten_identifiers += 1
        return mapped

    try:
        bound_sql = normalize_query_payload(
            transform_double_quoted_identifiers(embedded_sql, rewrite)
        )
    except ValueError:
        return None
    if not rewritten_identifiers:
        return None
    alias_style_attestation = None
    if bound_sql != normalized_expected:
        alias_style_attestation = attest_optional_alias_style_binding(
            bound_sql,
            normalized_expected,
        )
        if alias_style_attestation is None:
            return None
    rename_sha = (
        sha256_text(json.dumps(renames, sort_keys=True, separators=(",", ":")))
        if renames is not None
        else None
    )
    status = (
        "verified-authoritative-identifier-alpha-renaming"
        if renames is not None
        else "verified-protected-identifier-unquoting"
    )
    policy = (
        "remove simple ASCII identifier quotes and apply exactly "
        "metadata.json#/renamedIdentifiers"
        if renames is not None
        else "remove simple ASCII identifier quotes without changing names"
    )
    return {
        "status": status,
        "policy": (
            policy
            + "; then permit only the separately attested unquoted identifier/"
            "keyword case and optional AS spelling differences; preserve every "
            "other SQL token modulo protected-aware layout normalization"
        ),
        "sourceSqlSha256": source_sha,
        "embeddedSqlSha256": embedded_sha,
        "mappedEmbeddedSqlSha256": sha256_text(bound_sql),
        "boundEmbeddedSqlSha256": source_sha,
        "identifierRenameMapSha256": rename_sha,
        "quotedIdentifiersRewritten": rewritten_identifiers,
        "optionalAliasStyleAttestation": alias_style_attestation,
    }


def attest_optional_alias_style_binding(
    embedded_sql: str,
    source_sql: str,
) -> dict[str, Any] | None:
    """Ask the pinned SQLGlot environment for the closed optional-AS check."""

    completed = subprocess.run(
        [str(CALCITE_BINDING_ANALYZER)],
        input=json.dumps(
            {"embeddedSql": embedded_sql, "sourceSql": source_sql},
            sort_keys=True,
        ),
        cwd=Path(__file__).resolve().parents[3],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if completed.returncode != 0:
        return None
    try:
        report = json.loads(completed.stdout)
    except json.JSONDecodeError:
        return None
    if (
        not isinstance(report, dict)
        or report.get("status")
        not in {
            "verified-optional-alias-as-style",
            "verified-unquoted-case-style",
            "verified-unquoted-case-and-optional-alias-style",
        }
        or not isinstance(report.get("policy"), str)
        or not isinstance(report.get("canonicalTokenSha256"), str)
        or len(report["canonicalTokenSha256"]) != 64
        or not isinstance(report.get("embeddedAliasTokenCount"), int)
        or not isinstance(report.get("sourceAliasTokenCount"), int)
        or not isinstance(report.get("caseFoldedTokenCount"), int)
        or report["caseFoldedTokenCount"] < 0
        or (
            report["embeddedAliasTokenCount"]
            == report["sourceAliasTokenCount"]
            and report["caseFoldedTokenCount"] == 0
        )
        or not isinstance(report.get("nonAliasTokenCount"), int)
        or report["nonAliasTokenCount"] <= 0
    ):
        return None
    return report


def bind_calcite_schema(
    schema: Any,
    tables: list[Table],
    renames: dict[str, str] | None,
) -> dict[str, Any] | None:
    """Bind the complete ordered IR schema to the parser-facing source schema."""

    if not isinstance(schema, list) or len(schema) != len(tables):
        return None
    bound_schema: list[dict[str, Any]] = []
    source_schema: list[dict[str, Any]] = []
    folded_table_names: set[str] = set()
    for schema_table, table in zip(schema, tables):
        if not isinstance(schema_table, dict):
            return None
        bound_table_name = _mapped_authority_identifier(
            schema_table.get("name"), renames
        )
        table_names_match = (
            isinstance(bound_table_name, str)
            and bound_table_name.casefold() == table.name.casefold()
        )
        if (
            not table_names_match
            or table.name.casefold() in folded_table_names
        ):
            return None
        folded_table_names.add(table.name.casefold())
        columns = schema_table.get("columns")
        if not isinstance(columns, list) or len(columns) != len(table.columns):
            return None
        bound_columns: list[dict[str, str]] = []
        source_columns: list[dict[str, str]] = []
        folded_names: set[str] = set()
        for schema_column, column in zip(columns, table.columns):
            if not isinstance(schema_column, dict):
                return None
            bound_name = _mapped_authority_identifier(
                schema_column.get("name"), renames
            )
            actual_type = str(schema_column.get("type") or "")
            expected_type = calcite_schema_type_from_source(column.source_type)
            if (
                bound_name is None
                or bound_name.casefold() != column.name.casefold()
                or bound_name.casefold() in folded_names
                or not compatible_calcite_type(actual_type, expected_type)
            ):
                return None
            folded_names.add(bound_name.casefold())
            bound_columns.append(
                {"name": column.name, "type": canonical_type(actual_type)}
            )
            source_columns.append(
                {"name": column.name, "type": canonical_type(expected_type)}
            )
        bound_schema.append({"name": table.name, "columns": bound_columns})
        source_schema.append({"name": table.name, "columns": source_columns})
    if bound_schema != source_schema:
        return None
    rename_sha = (
        sha256_text(json.dumps(renames, sort_keys=True, separators=(",", ":")))
        if renames is not None
        else None
    )
    canonical_sha = sha256_text(
        json.dumps(bound_schema, sort_keys=True, separators=(",", ":"))
    )
    return {
        "status": "verified-complete-ordered-schema",
        "policy": (
            "exact ordered table/column/type equality after the authoritative "
            "identifier alpha-renaming"
            if renames is not None
            else "exact ordered table/column/type equality"
        ),
        "boundEmbeddedSchemaSha256": canonical_sha,
        "sourceSchemaSha256": canonical_sha,
        "identifierRenameMapSha256": rename_sha,
    }


def _unprotected_date_day_matches(
    pattern: re.Pattern[str], sql: str
) -> list[re.Match[str]]:
    found: list[re.Match[str]] = []

    def retain(match: re.Match[str]) -> str:
        found.append(match)
        return match.group(0)

    substitute_unprotected(pattern, retain, sql, start_only=True)
    return found


def _date_day_signature(matches: list[re.Match[str]]) -> Counter[tuple[str, str, str]]:
    return Counter(
        (
            match.group("lower_literal"),
            match.group("upper_literal"),
            match.group("days"),
        )
        for match in matches
    )


def _explicit_day_interval(match: re.Match[str]) -> str:
    return (
        match.group("predicate_prefix")
        + match.group("upper_prefix")
        + f"INTERVAL '{match.group('days')}' DAY"
        + match.group("suffix")
    )


def _ensure_sql_terminated(sql: str) -> str:
    stripped = sql.strip()
    if not stripped:
        return "\n"
    return stripped if stripped.endswith(";") else stripped + ";\n"


def attest_sqlglot_source_normalization_replay(
    raw_source_sql: str,
    generated_source_sql: str,
    expected_report: dict[str, Any],
) -> dict[str, Any] | None:
    completed = subprocess.run(
        [str(CALCITE_BINDING_ANALYZER)],
        input=json.dumps(
            {
                "mode": "source-normalization-replay",
                "rawSourceSql": raw_source_sql,
                "generatedSourceSql": generated_source_sql,
                "readDialect": expected_report.get("readDialect"),
                "writeDialect": expected_report.get("writeDialect"),
                "identify": expected_report.get("identify"),
                "pretty": expected_report.get("pretty"),
                "expectedReport": expected_report,
            },
            sort_keys=True,
        ),
        cwd=Path(__file__).resolve().parents[3],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if completed.returncode != 0:
        return None
    try:
        report = json.loads(completed.stdout)
    except json.JSONDecodeError:
        return None
    if (
        not isinstance(report, dict)
        or report.get("status")
        != "verified-sqlglot-source-normalization-replay"
        or not isinstance(report.get("policy"), str)
        or not isinstance(report.get("sqlglotVersion"), str)
        or not isinstance(report.get("canonicalTokenSha256"), str)
        or len(report["canonicalTokenSha256"]) != 64
        or not isinstance(report.get("normalizationReportSha256"), str)
        or len(report["normalizationReportSha256"]) != 64
        or not isinstance(report.get("tokenCount"), int)
        or report["tokenCount"] <= 0
    ):
        return None
    return report


def bind_pair_attested_tsql_date_days(
    source_metadata: dict[str, Any],
    ir_metadata: dict[str, Any],
    source_sql: tuple[str, str],
) -> tuple[tuple[str, str], tuple[dict[str, Any] | None, dict[str, Any] | None]] | None:
    """Bind SQLSolver's malformed ``N AS days`` to the exact IR pair input.

    This bridge is admitted only when the authoritative raw T-SQL-like pair,
    the reproducible SQLGlot SQLSolver normalization, and the Calcite export's
    own pair attestation all agree on every BETWEEN date/day-count site.
    """

    preprocessings = ir_metadata.get("frontendPairPreprocessing")
    if preprocessings is None:
        return source_sql, (None, None)
    if (
        not isinstance(preprocessings, list)
        or len(preprocessings) != 1
        or not isinstance(preprocessings[0], dict)
    ):
        return None
    attestation = preprocessings[0]
    if (
        attestation.get("kind") != "paired-tsql-between-date-day-unit"
        or attestation.get("predicateOnly") is not True
        or attestation.get("orderedQueryPairPreserved") is not True
        or str(source_metadata.get("readDialect") or "").casefold() != "tsql"
        or str(source_metadata.get("sourceDialect") or "").casefold()
        != "tsql_like"
        or ir_metadata.get("sourceBenchmark")
        != source_metadata.get("sourceBenchmark")
        or ir_metadata.get("sourceCase") != source_metadata.get("sourceCase")
    ):
        return None

    source_info = source_metadata.get("source")
    source_hashes = attestation.get("sourceSha256")
    frontend_hashes = attestation.get("frontendInputSha256")
    normalization = source_metadata.get("normalizationForSolverRun")
    if (
        not isinstance(source_info, dict)
        or not isinstance(source_info.get("source"), str)
        or source_info.get("case_id") != source_metadata.get("sourceCase")
        or not isinstance(source_hashes, dict)
        or not isinstance(frontend_hashes, dict)
        or not isinstance(normalization, dict)
    ):
        return None
    raw_root = (ROOT / source_info["source"] / source_info["case_id"]).resolve()
    try:
        raw_root.relative_to(ROOT.resolve())
    except ValueError:
        return None
    if not raw_root.is_dir():
        return None
    raw_candidates = sorted(path for path in raw_root.glob("*.sql") if path.is_file())
    raw_paths: list[Path] = []
    raw_sql: list[str] = []
    for side in ("before", "after"):
        expected_hash = source_hashes.get(side)
        if not isinstance(expected_hash, str) or len(expected_hash) != 64:
            return None
        matches = [
            path
            for path in raw_candidates
            if hashlib.sha256(path.read_bytes()).hexdigest() == expected_hash
        ]
        if len(matches) != 1:
            return None
        raw_paths.append(matches[0])
        raw_sql.append(matches[0].read_text())
    if raw_paths[0] == raw_paths[1]:
        return None

    if any("[" in mask_sql_regions(sql) or "]" in mask_sql_regions(sql) for sql in raw_sql):
        return None
    raw_matches = tuple(
        _unprotected_date_day_matches(_TSQL_DATE_DAY_SOURCE, sql)
        for sql in raw_sql
    )
    generated_matches = tuple(
        _unprotected_date_day_matches(_TSQL_DATE_DAY_SQLSOLVER, sql)
        for sql in source_sql
    )
    if any(not matches for matches in raw_matches + generated_matches):
        return None
    raw_signatures = tuple(_date_day_signature(matches) for matches in raw_matches)
    generated_signatures = tuple(
        _date_day_signature(matches) for matches in generated_matches
    )
    raw_units = tuple(
        [match.group("unit") is not None for match in matches]
        for matches in raw_matches
    )
    generated_aliases = tuple(
        [match.group("alias") is not None for match in matches]
        for matches in generated_matches
    )
    complete_raw_unit_sides = (
        all(raw_units[0]) and not any(raw_units[1]),
        all(raw_units[1]) and not any(raw_units[0]),
    )
    unit_side = 0 if complete_raw_unit_sides[0] else 1
    expected_multiset = [
        {
            "lowerDateLiteral": lower,
            "upperDateLiteral": upper,
            "days": days,
            "count": count,
        }
        for (lower, upper, days), count in sorted(raw_signatures[0].items())
    ]
    if (
        raw_signatures[0] != raw_signatures[1]
        or generated_signatures != raw_signatures
        or sum(complete_raw_unit_sides) != 1
        or any(
            lower != upper
            for signature in raw_signatures
            for lower, upper, _days in signature
        )
        or not all(generated_aliases[unit_side])
        or any(generated_aliases[1 - unit_side])
        or attestation.get("sourceSideWithDayUnit")
        != ("before" if unit_side == 0 else "after")
        or attestation.get("occurrencesPerSide") != len(raw_matches[0])
        or attestation.get("dateDayMultiset") != expected_multiset
    ):
        return None

    patched_raw = tuple(
        substitute_unprotected(
            _TSQL_DATE_DAY_SOURCE,
            _explicit_day_interval,
            sql,
            start_only=True,
        )
        for sql in raw_sql
    )
    for index, side in enumerate(("before", "after")):
        expected_frontend_hash = frontend_hashes.get(side)
        if (
            not isinstance(expected_frontend_hash, str)
            or hashlib.sha256(
                _ensure_sql_terminated(patched_raw[index]).encode()
            ).hexdigest()
            != expected_frontend_hash
        ):
            return None

    patched_generated = tuple(
        substitute_unprotected(
            _TSQL_DATE_DAY_SQLSOLVER,
            _explicit_day_interval,
            sql,
            start_only=True,
        )
        for sql in source_sql
    )
    reports: list[dict[str, Any]] = []
    for index, side in enumerate(("before", "after")):
        expected_report = normalization.get(side)
        if not isinstance(expected_report, dict):
            return None
        replay = attest_sqlglot_source_normalization_replay(
            raw_sql[index], source_sql[index], expected_report
        )
        if replay is None:
            return None
        reports.append(
            {
                "status": "verified-pair-attested-tsql-date-day-normalization",
                "rule": "tsql-between-date-day-to-explicit-interval",
                "sourceSide": side,
                "rawSourcePath": portable_path(raw_paths[index]),
                "rawSourceSha256": source_hashes[side],
                "sourceArtifactSqlSha256": sha256_text(
                    normalize_query_payload(source_sql[index])
                ),
                "boundSourceSqlSha256": sha256_text(
                    normalize_query_payload(patched_generated[index])
                ),
                "calciteFrontendInputSha256": frontend_hashes[side],
                "dateDayMultiset": expected_multiset,
                "pairAttestationSha256": sha256_text(
                    json.dumps(attestation, sort_keys=True, separators=(",", ":"))
                ),
                "sqlglotNormalizationReplay": replay,
                "sideConditions": {
                    "predicateOnly": True,
                    "sameCompleteDateDayMultisetOnBothSides": True,
                    "exactlyOneCompleteRawSideHasDayUnit": True,
                    "generatedAliasOccursOnlyOnThatSameSide": True,
                    "lowerAndUpperDateLiteralsEqualAtEverySite": True,
                    "noOutputAliasWasRemoved": True,
                },
            }
        )
    return (patched_generated[0], patched_generated[1]), (reports[0], reports[1])


_TYPED_REX_CLASSES = {
    "RexCall",
    "RexCorrelVariable",
    "RexFieldAccess",
    "RexInputRef",
    "RexLiteral",
    "RexOver",
    "RexSubQuery",
}


def _untyped_rex_shape(expression: RexExpr) -> tuple[Any, ...]:
    return (
        expression.kind,
        expression.value.upper() if expression.kind == "call" else expression.value,
        tuple(_untyped_rex_shape(argument) for argument in expression.args),
    )


def typed_rex_digest(payload: Any) -> str | None:
    """Read the exact digest carried by one typed Calcite Rex node.

    The rich IR is authoritative.  This accessor does not reconstruct SQL from
    source text and never invents a digest: it validates the typed envelope and
    returns its own ``text`` serialization.  For the closed Rex fragment parsed
    by this materializer, the parent serialization must also agree structurally
    with every typed operand.  Unsupported subqueries/windows remain visible as
    their exact digest and are subsequently rejected by the closed compiler.
    """

    if (
        not isinstance(payload, dict)
        or payload.get("class") not in _TYPED_REX_CLASSES
        or not isinstance(payload.get("text"), str)
        or not payload["text"]
        or not isinstance(payload.get("type"), str)
        or not isinstance(payload.get("fullType"), str)
        or not isinstance(payload.get("nullable"), bool)
        or not isinstance(payload.get("kind"), str)
    ):
        return None
    class_name = payload["class"]
    text = payload["text"]
    parsed = parse_rex_digest(text)

    if class_name == "RexInputRef":
        index = payload.get("index")
        if (
            not isinstance(index, int)
            or isinstance(index, bool)
            or text != f"${index}"
            or parsed is None
            or parsed.kind != "ref"
            or int(parsed.value) != index
        ):
            return None
        return text

    if class_name == "RexLiteral":
        literal_type = payload.get("literalTypeName")
        if not isinstance(literal_type, str):
            return None
        if parsed is not None and parsed.kind not in {"literal", "atom"}:
            # Calcite serializes interval-qualifier enum literals as
            # ``FLAG(YEAR)`` even though the rich node class remains
            # RexLiteral.  Preserve that exact opaque digest for the closed
            # compiler to reject; do not misclassify the whole IR pair as
            # unavailable merely because the generic Rex parser sees a call.
            literal_value = payload.get("literalValue2")
            if (
                literal_type != "SYMBOL"
                or not isinstance(literal_value, str)
                or text != f"FLAG({literal_value})"
            ):
                return None
        return text

    if class_name in {"RexCall", "RexSubQuery", "RexOver"}:
        operator = payload.get("operator")
        operands = payload.get("operands")
        if not isinstance(operator, str) or not isinstance(operands, list):
            return None
        operand_texts = [typed_rex_digest(operand) for operand in operands]
        if any(operand is None for operand in operand_texts):
            return None
        if parsed is not None:
            if (
                parsed.kind != "call"
                or parsed.value.upper() != operator.upper()
                or len(parsed.args) != len(operand_texts)
            ):
                return None
            parsed_operands = [
                parse_rex_digest(operand) for operand in operand_texts
            ]
            if any(operand is None for operand in parsed_operands) or any(
                _untyped_rex_shape(parent_operand)
                != _untyped_rex_shape(child_operand)
                for parent_operand, child_operand in zip(
                    parsed.args,
                    (
                        operand
                        for operand in parsed_operands
                        if operand is not None
                    ),
                )
            ):
                return None
        if class_name == "RexSubQuery" and not isinstance(
            payload.get("subqueryRel"), dict
        ):
            return None
        if class_name == "RexOver" and not isinstance(payload.get("window"), dict):
            return None
        return text

    # Correlation and field-access nodes occur only inside subquery digests.
    # Their exact serialization is intentionally opaque to the Cosette
    # compiler, but their rich envelope and nested reference must still exist.
    if class_name == "RexFieldAccess" and typed_rex_digest(
        payload.get("referenceExpr")
    ) is None:
        return None
    return text


_PARAMETERIZED_CALCITE_TYPE_FAMILIES = frozenset(
    {
        "BINARY",
        "CHAR",
        "DECIMAL",
        "NUMERIC",
        "TIME",
        "TIMESTAMP",
        "VARBINARY",
        "VARCHAR",
    }
)


def closed_calcite_type_envelope_agrees(
    type_name: Any,
    full_type: Any,
) -> bool:
    """Validate Calcite's redundant base/full aggregate result type fields."""

    if not isinstance(type_name, str) or not isinstance(full_type, str):
        return False
    declared = re.fullmatch(
        r"(?P<family>[A-Za-z_][A-Za-z0-9_]*)",
        type_name,
        flags=re.ASCII,
    )
    complete = re.fullmatch(
        r"(?P<family>[A-Za-z_][A-Za-z0-9_]*)"
        r"(?:\((?P<precision>[0-9]+)(?:, (?P<scale>[0-9]+))?\))?"
        r"(?P<notNull> NOT NULL)?",
        full_type,
        flags=re.ASCII,
    )
    if declared is None or complete is None:
        return False

    def canonical_family(value: str) -> str:
        upper = value.upper()
        return "INTEGER" if upper == "INT" else upper

    declared_family = canonical_family(declared.group("family"))
    complete_family = canonical_family(complete.group("family"))
    has_parameters = complete.group("precision") is not None
    return (
        declared_family == complete_family
        and (
            not has_parameters
            or declared_family in _PARAMETERIZED_CALCITE_TYPE_FAMILIES
        )
    )


def typed_aggregate_digest(payload: Any) -> str | None:
    if (
        not isinstance(payload, dict)
        or not isinstance(payload.get("text"), str)
        or not payload["text"]
        or not isinstance(payload.get("function"), str)
        or not isinstance(payload.get("kind"), str)
        or not isinstance(payload.get("type"), str)
        or not isinstance(payload.get("fullType"), str)
        or not isinstance(payload.get("argList"), list)
        or any(
            not isinstance(index, int) or isinstance(index, bool) or index < 0
            for index in payload["argList"]
        )
        or not isinstance(payload.get("distinct"), bool)
        or not isinstance(payload.get("approximate"), bool)
        or not isinstance(payload.get("ignoreNulls"), bool)
        or not isinstance(payload.get("filterArg"), int)
        or isinstance(payload.get("filterArg"), bool)
        or payload["filterArg"] < -1
        or not isinstance(payload.get("collation"), list)
    ):
        return None
    text = payload["text"]
    parsed = re.fullmatch(
        r"(?P<function>[A-Za-z_$][A-Za-z0-9_$]*)\("
        r"(?:(?P<distinct>DISTINCT)\s+)?"
        r"(?P<arguments>(?:\$[0-9]+(?:\s*,\s*\$[0-9]+)*)?)\)"
        r"(?:\s+FILTER\s+\$(?P<filter>[0-9]+))?",
        text,
        flags=re.ASCII | re.IGNORECASE,
    )
    if parsed is None:
        return None
    arguments_text = parsed.group("arguments")
    parsed_arguments = (
        [
            int(argument.strip()[1:])
            for argument in arguments_text.split(",")
        ]
        if arguments_text
        else []
    )
    parsed_filter = (
        int(parsed.group("filter"))
        if parsed.group("filter") is not None
        else -1
    )

    if (
        parsed.group("function").upper() != payload["function"].upper()
        or payload["kind"].upper() != payload["function"].upper()
        or parsed_arguments != payload["argList"]
        or (parsed.group("distinct") is not None) != payload["distinct"]
        or parsed_filter != payload["filterArg"]
        or not closed_calcite_type_envelope_agrees(
            payload["type"],
            payload["fullType"],
        )
        # These fields are carried by Calcite but are not implemented by the
        # closed Cosette aggregate compiler.  Keeping them merely in metadata
        # would let the compiler silently render a weaker call, so even an
        # internally consistent modifier-bearing envelope fails closed here.
        or payload["distinct"]
        or payload["filterArg"] != -1
        or payload["collation"]
        or payload["approximate"]
        or payload["ignoreNulls"]
    ):
        return None
    return text


def bind_calcite_rel_representation(
    relation: Any,
) -> tuple[dict[str, Any], dict[str, Any]] | None:
    """Create a checked legacy-digest view of the current typed Calcite IR.

    Cosette's closed compiler predates the typed ``*Rex`` field names.  The view
    aliases only exact machine-produced digest fields; it keeps the complete
    typed payload in place and rejects missing, conflicting, or malformed
    representations.  This is a serialization bridge, not a semantic rewrite.
    """

    if not isinstance(relation, dict):
        return None
    view = json.loads(json.dumps(relation))
    counts = {
        "conditions": 0,
        "projects": 0,
        "aggregateCalls": 0,
        "sliceBounds": 0,
        "valuesCells": 0,
    }

    def install(node: dict[str, Any], legacy: str, typed: str, value: Any) -> bool:
        if legacy in node and node[legacy] != value:
            return False
        node[legacy] = value
        return True

    def visit(node: Any) -> bool:
        if not isinstance(node, dict) or not isinstance(node.get("type"), str):
            return False
        inputs = node.get("inputs")
        if not isinstance(inputs, list) or any(not visit(child) for child in inputs):
            return False
        node_type = node["type"]

        if node_type in {"LogicalFilter", "LogicalJoin"}:
            digest = typed_rex_digest(node.get("conditionRex"))
            if digest is None or not install(node, "condition", "conditionRex", digest):
                return False
            counts["conditions"] += 1

        if node_type == "LogicalProject":
            rich = node.get("projectRex")
            if not isinstance(rich, list):
                return False
            digests = [typed_rex_digest(item) for item in rich]
            if any(item is None for item in digests) or not install(
                node, "projects", "projectRex", digests
            ):
                return False
            counts["projects"] += len(digests)

        if node_type == "LogicalAggregate":
            rich = node.get("aggCallDetails")
            if not isinstance(rich, list):
                return False
            digests = [typed_aggregate_digest(item) for item in rich]
            if any(item is None for item in digests) or not install(
                node, "aggCalls", "aggCallDetails", digests
            ):
                return False
            counts["aggregateCalls"] += len(digests)

        if node_type == "LogicalSort":
            for legacy, typed in (("fetch", "fetchRex"), ("offset", "offsetRex")):
                if typed not in node:
                    continue
                digest = typed_rex_digest(node[typed])
                if digest is None or not install(node, legacy, typed, digest):
                    return False
                counts["sliceBounds"] += 1

        if node_type == "LogicalValues":
            tuples = node.get("tuples")
            if not isinstance(tuples, list):
                return False
            for row in tuples:
                if not isinstance(row, list):
                    return False
                for cell in row:
                    if typed_rex_digest(cell) is None:
                        return False
                    counts["valuesCells"] += 1
        return True

    if not visit(view):
        return None
    raw_sha = sha256_text(
        json.dumps(relation, sort_keys=True, separators=(",", ":"))
    )
    view_sha = sha256_text(json.dumps(view, sort_keys=True, separators=(",", ":")))
    return view, {
        "status": "verified-typed-rex-digest-view",
        "policy": (
            "alias only exact typed conditionRex/projectRex/aggCallDetails/"
            "fetchRex/offsetRex text fields after typed-envelope validation; "
            "aggregate operator/kind/direct arguments/type envelopes must agree "
            "exactly and unsupported aggregate modifiers must be absent; retain "
            "the complete rich IR and reject conflicts"
        ),
        "typedRelSha256": raw_sha,
        "digestViewSha256": view_sha,
        "aliasedFieldCounts": counts,
    }


def load_calcite_ir_pair(
    source_metadata: dict[str, Any],
    source_sql: tuple[str, str],
    tables: list[Table],
) -> tuple[CalciteIrSource, CalciteIrSource] | None:
    benchmark = source_metadata.get("sourceBenchmark")
    case = source_metadata.get("sourceCase")
    if not isinstance(benchmark, str) or not isinstance(case, str):
        return None
    ir_root = (ROOT / "benchmarks/core/.generated/calcite-ir").resolve()
    directory = (ir_root / benchmark / case).resolve()
    try:
        directory.relative_to(ir_root)
    except ValueError:
        return None
    try:
        renames = authoritative_identifier_renames(source_metadata)
    except ValueError:
        return None
    ir_metadata_path = directory / "metadata.json"
    try:
        ir_metadata = (
            json.loads(ir_metadata_path.read_text())
            if ir_metadata_path.is_file()
            else {}
        )
    except (OSError, json.JSONDecodeError):
        return None
    if not isinstance(ir_metadata, dict):
        return None
    source_binding = bind_pair_attested_tsql_date_days(
        source_metadata,
        ir_metadata,
        source_sql,
    )
    if source_binding is None:
        return None
    bound_source_sql, source_normalizations = source_binding
    loaded: list[CalciteIrSource] = []
    for side, source_artifact_sql, expected_sql, source_normalization in zip(
        ("before", "after"),
        source_sql,
        bound_source_sql,
        source_normalizations,
    ):
        path = directory / f"{side}.calcite-ir.json"
        if not path.is_file():
            return None
        raw = path.read_bytes()
        payload = json.loads(raw)
        queries = payload.get("queries") if isinstance(payload, dict) else None
        if not isinstance(queries, list) or len(queries) != 1:
            return None
        query = queries[0]
        rel = query.get("rel") if isinstance(query, dict) else None
        embedded_sql = query.get("sql") if isinstance(query, dict) else None
        schema = payload.get("schema") if isinstance(payload, dict) else None
        representation = bind_calcite_rel_representation(rel)
        query_binding = (
            bind_calcite_query_sql(embedded_sql, expected_sql, renames)
            if isinstance(embedded_sql, str)
            else None
        )
        schema_binding = bind_calcite_schema(schema, tables, renames)
        if (
            representation is None
            or query_binding is None
            or schema_binding is None
        ):
            return None
        rel_view, representation_binding = representation
        source_artifact_sha = sha256_text(
            normalize_query_payload(source_artifact_sql)
        )
        bound_source_sha = query_binding["sourceSqlSha256"]
        if source_normalization is not None and (
            source_normalization.get("sourceArtifactSqlSha256")
            != source_artifact_sha
            or source_normalization.get("boundSourceSqlSha256")
            != bound_source_sha
        ):
            return None
        query_binding["sourceArtifactSqlSha256"] = source_artifact_sha
        query_binding["boundSourceSqlSha256"] = bound_source_sha
        query_binding["sourceSqlSha256"] = source_artifact_sha
        query_binding["sourceNormalization"] = source_normalization
        loaded.append(
            CalciteIrSource(
                rel=rel_view,
                path=path,
                sha256=hashlib.sha256(raw).hexdigest(),
                source_sql_sha256=source_artifact_sha,
                bound_source_sql_sha256=bound_source_sha,
                embedded_sql_sha256=query_binding["embeddedSqlSha256"],
                schema_sha256=sha256_text(
                    json.dumps(schema, sort_keys=True, separators=(",", ":"))
                ),
                authority_binding={
                    "query": query_binding,
                    "schema": schema_binding,
                },
                representation_binding=representation_binding,
            )
        )
    return loaded[0], loaded[1]


def ir_source_metadata(source: CalciteIrSource) -> dict[str, Any]:
    return {
        "path": portable_path(source.path),
        "sha256": source.sha256,
        "sourceSqlSha256": source.source_sql_sha256,
        "embeddedSqlSha256": source.embedded_sql_sha256,
        "normalizedSourceSqlMatchesEmbeddedIrSql": (
            source.source_sql_sha256 == source.embedded_sql_sha256
        ),
        "normalizedSourceSqlMatchesBoundIrSql": (
            source.bound_source_sql_sha256
            == source.authority_binding["query"]["boundEmbeddedSqlSha256"]
        ),
        "normalizedSourceArtifactSqlMatchesBoundIrSql": (
            source.source_sql_sha256
            == source.authority_binding["query"]["boundEmbeddedSqlSha256"]
        ),
        "normalizedBoundSourceSqlMatchesBoundIrSql": (
            source.bound_source_sql_sha256
            == source.authority_binding["query"]["boundEmbeddedSqlSha256"]
        ),
        "boundSourceSqlSha256": source.bound_source_sql_sha256,
        "embeddedSchemaSha256": source.schema_sha256,
        "embeddedSchemaMatchesMaterializedSchema": True,
        "authorityBinding": source.authority_binding,
        "representationBinding": source.representation_binding,
    }


def sha256_text(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def calcite_schema_matches_tables(schema: Any, tables: list[Table]) -> bool:
    return bind_calcite_schema(schema, tables, None) is not None


def output_type_signature(rel: dict[str, Any]) -> list[dict[str, Any]]:
    row_type = rel.get("rowType")
    if not isinstance(row_type, list):
        return []
    signature: list[dict[str, Any]] = []
    for field_entry in row_type:
        if not isinstance(field_entry, dict):
            return []
        # Keep every type modifier exported by Calcite, but not the presentation
        # name: external equivalence baselines compare ordered values, not labels.
        signature.append(
            {
                key: field_entry[key]
                for key in sorted(field_entry)
                if key != "name"
            }
        )
    return signature


def signature_types(signature: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return [
        {key: value for key, value in item.items() if key != "nullable"}
        for item in signature
    ]


def signature_nullability(signature: list[dict[str, Any]]) -> list[bool | None]:
    return [item.get("nullable") for item in signature]


def attest_postgres_aggregate_result_types(
    rel: dict[str, Any],
    *,
    read_dialect: Any,
) -> dict[str, Any]:
    """Check aggregate result types that the Cosette compiler can expose.

    The generated SQL is bound and interpreted as PostgreSQL by this
    materializer.  A Calcite tree is therefore not sufficient authority when
    its aggregate type disagrees with PostgreSQL's source-level contract.  In
    particular, PostgreSQL widens ``SUM(smallint|integer)`` to ``bigint`` and
    ``SUM(bigint)`` to ``numeric``.  Accepting Calcite's historical
    ``SUM(integer) -> integer`` inference would erase observable output typing
    and fixed-width overflow behavior before Cosette sees the query.

    The check is deliberately closed over the aggregate calls that the public
    Cosette compiler can otherwise render.  Its evidence is bound to the exact
    checked digest view; malformed or contradictory envelopes are rejected.
    """

    rel_sha256 = sha256_text(
        json.dumps(rel, sort_keys=True, separators=(",", ":"))
    )
    checked: list[dict[str, Any]] = []
    rejection: dict[str, Any] | None = None

    def reject(path: str, reason: str, **details: Any) -> bool:
        nonlocal rejection
        rejection = {"path": path, "reason": reason, **details}
        return False

    def visit(node: Any, path: str) -> bool:
        if not isinstance(node, dict):
            return reject(path, "relational node is not an object")
        inputs = node.get("inputs")
        if not isinstance(inputs, list):
            return reject(path, "relational node inputs are not a list")
        for index, child in enumerate(inputs):
            if not visit(child, f"{path}.inputs[{index}]"):
                return False
        if node.get("type") != "LogicalAggregate":
            return True

        details = node.get("aggCallDetails")
        group_indexes = parse_group_set(node.get("groupSet"))
        output_row = validated_row_type(node)
        if (
            not isinstance(details, list)
            or group_indexes is None
            or output_row is None
            or len(inputs) != 1
        ):
            return reject(path, "aggregate envelope is incomplete")
        input_row = validated_row_type(inputs[0])
        if input_row is None or len(output_row) != len(group_indexes) + len(details):
            return reject(path, "aggregate input/output arity is inconsistent")

        for index, detail in enumerate(details):
            call_path = f"{path}.aggCallDetails[{index}]"
            if not isinstance(detail, dict):
                return reject(call_path, "aggregate detail is not an object")
            function = detail.get("function")
            arguments = detail.get("argList")
            result_type = detail.get("type")
            if (
                not isinstance(function, str)
                or not isinstance(arguments, list)
                or not isinstance(result_type, str)
            ):
                return reject(call_path, "aggregate detail lacks typed fields")
            function = function.upper()
            if function.lower() not in COSETTE_SUPPORTED_AGGREGATES:
                continue
            if read_dialect != "postgres":
                return reject(
                    call_path,
                    "source query read dialect is not PostgreSQL",
                    readDialect=read_dialect,
                )
            if any(
                not isinstance(argument, int)
                or isinstance(argument, bool)
                or argument < 0
                or argument >= len(input_row)
                for argument in arguments
            ):
                return reject(call_path, "aggregate argument index is invalid")

            actual = canonical_type(result_type)
            output_actual = canonical_type(
                output_row[len(group_indexes) + index]["type"]
            )
            argument_types = [
                canonical_type(input_row[argument]["type"])
                for argument in arguments
            ]
            expected: str | None = None
            expected_family: str | None = None
            if function == "COUNT":
                if len(arguments) not in {0, 1}:
                    return reject(
                        call_path,
                        "COUNT arity is outside the closed surface",
                    )
                expected = "BIGINT"
            elif function == "SUM":
                if len(argument_types) != 1:
                    return reject(call_path, "SUM arity is outside the closed surface")
                if argument_types[0] in {"SMALLINT", "INTEGER"}:
                    expected = "BIGINT"
                elif argument_types[0] == "BIGINT":
                    expected_family = "NUMERIC"
                else:
                    # The compiler cannot render SUM over this input type, so it
                    # remains visible to that independent fail-closed gate.
                    continue
            elif function in {"MIN", "MAX"}:
                if len(argument_types) != 1:
                    return reject(
                        call_path,
                        f"{function} arity is outside the closed surface",
                    )
                expected = argument_types[0]

            result_matches = (
                actual == expected
                if expected is not None
                else actual.startswith("DECIMAL") or actual.startswith("NUMERIC")
            )
            if actual != output_actual:
                return reject(
                    call_path,
                    "aggregate detail and ordered output row type disagree",
                    detailType=actual,
                    outputType=output_actual,
                )
            if not result_matches:
                return reject(
                    call_path,
                    "Calcite aggregate result type disagrees with PostgreSQL",
                    function=function,
                    argumentTypes=argument_types,
                    calciteResultType=actual,
                    expectedResultType=expected,
                    expectedResultFamily=expected_family,
                )
            checked.append(
                {
                    "path": call_path,
                    "function": function,
                    "argumentTypes": argument_types,
                    "calciteResultType": actual,
                    "orderedOutputType": output_actual,
                    "postgresResultType": expected,
                    "postgresResultFamily": expected_family,
                }
            )
        return True

    accepted = visit(rel, "root")
    if not accepted:
        return {
            "status": "rejected",
            "policy": "exact PostgreSQL aggregate result typing for Cosette-renderable calls",
            "readDialect": read_dialect,
            "checkedRelSha256": rel_sha256,
            "checkedCalls": checked,
            "rejection": rejection,
        }
    if not checked:
        return {
            "status": "not-applicable",
            "policy": "no Cosette-renderable aggregate result type required checking",
            "readDialect": read_dialect,
            "checkedRelSha256": rel_sha256,
            "checkedCalls": [],
        }
    return {
        "status": "verified-postgresql-aggregate-result-types",
        "policy": "exact PostgreSQL aggregate result typing for Cosette-renderable calls",
        "readDialect": read_dialect,
        "checkedRelSha256": rel_sha256,
        "checkedCalls": checked,
    }


def attest_filter_equality_projection_substitution(
    left: dict[str, Any],
    right: dict[str, Any],
) -> dict[str, Any] | None:
    """Close a direct post-filter projection by a typed integer equality.

    The projection is evaluated only for rows on which the filter is TRUE, so
    the filtered field is non-NULL and equals the admitted literal there.  We
    normalize every ordered output expression after that substitution using
    the same checked Rex evaluator as the compiler.  Constant arithmetic must
    fold within range; any remaining checked operation must be byte-identical
    after substitution on both sides.  This is deliberately limited to one
    Project over one equality Filter over one base scan.
    """

    left_shape = filter_equality_projection_program(left)
    right_shape = filter_equality_projection_program(right)
    if left_shape is None or right_shape is None:
        return None
    (
        left_table,
        left_index,
        left_literal,
        left_fields,
        left_projects,
        left_outputs,
    ) = left_shape
    (
        right_table,
        right_index,
        right_literal,
        right_fields,
        right_projects,
        right_outputs,
    ) = right_shape
    if (
        left_table.lower() != right_table.lower()
        or left_index != right_index
        or left_literal != right_literal
        or len(left_fields) != len(right_fields)
        or len(left_projects) != len(right_projects)
        or [
            {
                key: value
                for key, value in field.items()
                if key not in {"name", "nullable"}
            }
            for field in left_fields
        ]
        != [
            {
                key: value
                for key, value in field.items()
                if key not in {"name", "nullable"}
            }
            for field in right_fields
        ]
        or [
            {
                key: value
                for key, value in output.items()
                if key not in {"name", "nullable"}
            }
            for output in left_outputs
        ]
        != [
            {
                key: value
                for key, value in output.items()
                if key not in {"name", "nullable"}
            }
            for output in right_outputs
        ]
    ):
        return None

    left_normalized = normalize_projection_after_filter_equality(
        left_fields,
        left_projects,
        left_outputs,
        left_index,
        left_literal,
    )
    right_normalized = normalize_projection_after_filter_equality(
        right_fields,
        right_projects,
        right_outputs,
        right_index,
        right_literal,
    )
    if left_normalized is None or left_normalized != right_normalized:
        return None
    return {
        "rule": "filter-equality-projection-substitution",
        "kind": "pair-safety",
        "sideConditions": {
            "sameBaseTable": left_table,
            "filter": f"field[{left_index}] = {left_literal}",
            "UNKNOWNRowsRejectedByWhere": True,
            "projectionEvaluatedOnlyAfterFilterAcceptance": True,
            "orderedProjectionTypesEqual": True,
            "orderedNormalizedProjectionExpressions": [
                item[0] for item in left_normalized
            ],
            "constantArithmeticCheckedWithinIntegerRange": True,
            "remainingCheckedOperationsIdenticalAfterSubstitution": True,
        },
    }


def filter_equality_projection_program(
    rel: dict[str, Any],
) -> tuple[
    str,
    int,
    str,
    list[dict[str, Any]],
    list[Any],
    list[dict[str, Any]],
] | None:
    if rel.get("type") != "LogicalProject":
        return None
    projects = rel.get("projects")
    outputs = validated_row_type(rel)
    inputs = rel.get("inputs")
    if (
        not isinstance(projects, list)
        or outputs is None
        or len(projects) != len(outputs)
        or not isinstance(inputs, list)
        or len(inputs) != 1
    ):
        return None
    filter_node = inputs[0]
    if not isinstance(filter_node, dict) or filter_node.get("type") != "LogicalFilter":
        return None
    filter_inputs = filter_node.get("inputs")
    if (
        not isinstance(filter_inputs, list)
        or len(filter_inputs) != 1
        or not is_plain_table_scan(filter_inputs[0])
    ):
        return None
    scan = filter_inputs[0]
    fields = validated_row_type(scan)
    condition = parse_rex_digest(filter_node.get("condition"))
    if (
        fields is None
        or condition is None
        or condition.kind != "call"
        or condition.value != "="
        or len(condition.args) != 2
    ):
        return None
    references = [argument for argument in condition.args if argument.kind == "ref"]
    literals = [argument for argument in condition.args if argument.kind == "literal"]
    if len(references) != 1 or len(literals) != 1:
        return None
    index = int(references[0].value)
    if index >= len(fields):
        return None
    field_type = canonical_type(fields[index]["type"])
    literal = literals[0]
    if (
        field_type not in {"INTEGER", "BIGINT"}
        or re.fullmatch(r"0|-?[1-9][0-9]*", literal.value) is None
        or (
            literal.type_name is not None
            and not compatible_calcite_type(literal.type_name, field_type)
        )
    ):
        return None
    value = int(literal.value)
    lower, upper = (
        (-(2**31), 2**31 - 1)
        if field_type == "INTEGER"
        else (-(2**63), 2**63 - 1)
    )
    table_path = scan.get("table")
    if not lower <= value <= upper or not isinstance(table_path, list) or not table_path:
        return None
    return (
        str(table_path[-1]),
        index,
        str(value),
        fields,
        projects,
        outputs,
    )


def normalize_projection_after_filter_equality(
    fields: list[dict[str, Any]],
    projects: list[Any],
    outputs: list[dict[str, Any]],
    filtered_index: int,
    literal: str,
) -> tuple[tuple[str, str, tuple[tuple[str, str], ...]], ...] | None:
    symbolic_fields = [
        IrField(f"field[{index}]", field["type"], field["nullable"])
        for index, field in enumerate(fields)
    ]
    symbolic_fields[filtered_index] = IrField(
        literal,
        fields[filtered_index]["type"],
        False,
        True,
    )
    normalized: list[tuple[str, str, tuple[tuple[str, str], ...]]] = []
    for project, output in zip(projects, outputs):
        attestations: list[dict[str, Any]] = []
        rendered = render_rex_value(project, symbolic_fields, attestations)
        if rendered is None or not compatible_calcite_type(
            rendered.type_name, output["type"]
        ):
            return None
        obligations = tuple(
            (
                str(item.get("rule") or ""),
                str(item.get("sideConditions", {}).get("operator") or ""),
            )
            for item in attestations
            if item.get("kind") == "pair-safety-obligation"
        )
        normalized.append(
            (
                rendered.expression,
                canonical_type(output["type"]),
                obligations,
            )
        )
    return tuple(normalized)


_FLAT_FROM_ITEM = re.compile(
    r"(?P<table>[A-Za-z_][A-Za-z0-9_.]*)\s+AS\s+(?P<alias>t[0-9]+)",
    flags=re.ASCII,
)
_FLAT_SIMPLE_TERM_TEXT = (
    r"(?:t[0-9]+\.[A-Za-z_][A-Za-z0-9_]*|'(?:''|[^'])*'|[+-]?[0-9]+)"
)
_FLAT_SIMPLE_EQUALITY = re.compile(
    rf"^\(\s*(?P<left>{_FLAT_SIMPLE_TERM_TEXT})\s*=\s*"
    rf"(?P<right>{_FLAT_SIMPLE_TERM_TEXT})\s*\)$",
    flags=re.ASCII,
)
_FLAT_SIMPLE_COMPARISON = re.compile(
    rf"^\(\s*(?P<left>{_FLAT_SIMPLE_TERM_TEXT})\s*"
    rf"(?P<operator>[<>])\s*(?P<right>{_FLAT_SIMPLE_TERM_TEXT})\s*\)$",
    flags=re.ASCII,
)
_FLAT_TERM_TOKEN = re.compile(
    r"t[0-9]+\.[A-Za-z_][A-Za-z0-9_]*|'(?:''|[^'])*'|"
    r"(?<![A-Za-z0-9_.])[+-]?[0-9]+(?![A-Za-z0-9_.])",
    flags=re.ASCII,
)
_FLAT_ALIAS_TOKEN = re.compile(r"\bt[0-9]+(?=\.)", flags=re.ASCII)
_FLAT_INFIX_ARITHMETIC = re.compile(r"\s[+*/-]\s", flags=re.ASCII)


def _flat_from_occurrences(plan: FlatCosettePlan) -> list[tuple[str, str]] | None:
    occurrences: list[tuple[str, str]] = []
    for item in plan.from_items:
        match = _FLAT_FROM_ITEM.fullmatch(item)
        if match is None:
            return None
        occurrences.append((match.group("table").lower(), match.group("alias")))
    if len({alias for _table, alias in occurrences}) != len(occurrences):
        return None
    return occurrences


def _rename_flat_aliases(text: str, aliases: dict[str, str]) -> str:
    return _FLAT_ALIAS_TOKEN.sub(
        lambda match: aliases.get(match.group(0), match.group(0)), text
    )


def _flat_literal(term: str) -> bool:
    return term.startswith("'") or re.fullmatch(r"[+-]?[0-9]+", term) is not None


def _replace_flat_terms(
    text: str,
    representatives: dict[str, str],
    *,
    preserve_checked_arithmetic: bool,
) -> str:
    # Equality-derived substitution is value preserving after WHERE admission,
    # but it must not be used to erase a checked operation: a rejected source
    # row can still expose PostgreSQL overflow depending on evaluation order.
    if preserve_checked_arithmetic and _FLAT_INFIX_ARITHMETIC.search(text):
        return text
    return _FLAT_TERM_TOKEN.sub(
        lambda match: representatives.get(match.group(0), match.group(0)), text
    )


def _reduce_flat_integer_bounds(predicates: list[str]) -> tuple[str, ...]:
    lower: dict[str, int] = {}
    upper: dict[str, int] = {}
    residual: set[str] = set()
    for predicate in predicates:
        comparison = _FLAT_SIMPLE_COMPARISON.fullmatch(predicate)
        if comparison is None:
            residual.add(predicate)
            continue
        left = comparison.group("left")
        right = comparison.group("right")
        operator = comparison.group("operator")
        if re.fullmatch(r"[+-]?[0-9]+", left) and not _flat_literal(right):
            left, right = right, left
            operator = ">" if operator == "<" else "<"
        if _flat_literal(left) or re.fullmatch(r"[+-]?[0-9]+", right) is None:
            residual.add(predicate)
            continue
        bound = int(right)
        if operator == ">":
            lower[left] = max(lower.get(left, bound), bound)
        else:
            upper[left] = min(upper.get(left, bound), bound)
    residual.update(f"({field} > {bound})" for field, bound in lower.items())
    residual.update(f"({field} < {bound})" for field, bound in upper.items())
    return tuple(sorted(residual))


def _canonical_flat_plan(
    plan: FlatCosettePlan,
    aliases: dict[str, str],
    *,
    preserve_predicate_order: bool,
) -> tuple[Any, ...] | None:
    occurrences = _flat_from_occurrences(plan)
    if occurrences is None:
        return None

    predicates = [_rename_flat_aliases(value, aliases) for value in plan.predicates]
    parents: dict[str, str] = {}
    equality_terms: set[str] = set()
    other_predicates: list[str] = []

    def find(value: str) -> str:
        parent = parents.setdefault(value, value)
        if parent != value:
            parents[value] = find(parent)
        return parents[value]

    def union(left: str, right: str) -> None:
        left_root = find(left)
        right_root = find(right)
        if left_root != right_root:
            first, second = sorted((left_root, right_root))
            parents[second] = first

    for predicate in predicates:
        equality = _FLAT_SIMPLE_EQUALITY.fullmatch(predicate)
        if equality is None:
            other_predicates.append(predicate)
            continue
        left = equality.group("left")
        right = equality.group("right")
        if _flat_literal(left) and _flat_literal(right):
            # Equal constants contribute TRUE; distinct constants require
            # type/collation reasoning outside this deliberately closed rule.
            if left != right:
                return None
            continue
        equality_terms.update((left, right))
        union(left, right)

    classes: dict[str, set[str]] = {}
    for term in equality_terms:
        classes.setdefault(find(term), set()).add(term)
    class_signature = tuple(
        sorted(tuple(sorted(members)) for members in classes.values())
    )
    representatives = {
        term: min(members)
        for members in classes.values()
        for term in members
    }

    normalized_predicates = [
        _replace_flat_terms(
            predicate,
            representatives,
            preserve_checked_arithmetic=True,
        )
        for predicate in other_predicates
    ]
    ordered_error_signature: tuple[str, ...] | None = None
    if preserve_predicate_order:
        ordered: list[str] = []
        for predicate in predicates:
            equality = _FLAT_SIMPLE_EQUALITY.fullmatch(predicate)
            if equality is None:
                ordered.append(predicate)
            else:
                left, right = sorted(
                    (equality.group("left"), equality.group("right"))
                )
                ordered.append(f"({left} = {right})")
        ordered_error_signature = tuple(ordered)
    predicate_signature: tuple[str, ...]
    if preserve_predicate_order:
        predicate_signature = tuple(normalized_predicates)
    else:
        # SQL Bool3 conjunction is idempotent and commutative for expressions
        # in this error-free fragment; WHERE observes only TRUE acceptance.
        predicate_signature = _reduce_flat_integer_bounds(normalized_predicates)

    output_signature = tuple(
        (
            _replace_flat_terms(
                _rename_flat_aliases(field_value.expression, aliases),
                representatives,
                preserve_checked_arithmetic=True,
            ),
            canonical_type(field_value.type_name),
        )
        for field_value in plan.fields
    )

    group_signature: tuple[str, ...] | None = None
    if plan.group_by is not None:
        groups = {
            _replace_flat_terms(
                _rename_flat_aliases(group, aliases),
                representatives,
                preserve_checked_arithmetic=True,
            )
            for group in plan.group_by
        }
        nonconstant_groups = {group for group in groups if not _flat_literal(group)}
        if nonconstant_groups:
            # A constant key cannot split a nonempty group and, because another
            # key remains, removing it does not turn empty-input GROUP BY into a
            # global aggregate.
            groups = nonconstant_groups
        group_signature = tuple(sorted(groups))

    return (
        tuple(sorted(table for table, _alias in occurrences)),
        class_signature,
        predicate_signature,
        ordered_error_signature,
        output_signature,
        group_signature,
    )


def attest_flat_inner_relational_equivalence(
    left: CompiledCosetteQuery,
    right: CompiledCosetteQuery,
) -> dict[str, Any] | None:
    """Recognize a small alias/order/equality-closure equivalence fragment.

    Both inputs were reconstructed from exact bound Calcite trees and contain
    only scans, inner products/joins, filters, projects and ordinary GROUP BY.
    We enumerate a type-preserving base-relation occurrence bijection, then
    compare outputs, grouping and TRUE-accepting conjuncts modulo simple
    equality closure.  No inequality implication, NULL-sensitive self-join
    elimination, outer join, set, order or slicing law is used here.
    """

    if left.flat_plan is None or right.flat_plan is None:
        return None
    left_occurrences = _flat_from_occurrences(left.flat_plan)
    right_occurrences = _flat_from_occurrences(right.flat_plan)
    if (
        left_occurrences is None
        or right_occurrences is None
        or len(left_occurrences) != len(right_occurrences)
    ):
        return None
    has_checked_arithmetic = any(
        item.get("kind") == "pair-safety-obligation"
        for item in left.attestations + right.attestations
    )
    if has_checked_arithmetic:
        # Flattening intentionally forgets whether a predicate came from a
        # join condition or from a filter above that join.  For PostgreSQL
        # checked arithmetic that distinction can change which candidate rows
        # evaluate the expression and therefore whether overflow is observed.
        # Textual predicate equality/order after flattening is not enough to
        # discharge that error-path obligation.
        return None
    left_aliases = {alias: alias for _table, alias in left_occurrences}
    left_fingerprint = _canonical_flat_plan(
        left.flat_plan,
        left_aliases,
        preserve_predicate_order=False,
    )
    if left_fingerprint is None:
        return None

    left_by_table: dict[str, list[str]] = {}
    right_by_table: dict[str, list[str]] = {}
    for table, alias in left_occurrences:
        left_by_table.setdefault(table, []).append(alias)
    for table, alias in right_occurrences:
        right_by_table.setdefault(table, []).append(alias)
    if {
        table: len(aliases) for table, aliases in left_by_table.items()
    } != {
        table: len(aliases) for table, aliases in right_by_table.items()
    }:
        return None
    if any(len(aliases) > 6 for aliases in left_by_table.values()):
        return None
    table_names = sorted(left_by_table)
    # Enumerate only within repeated occurrences of the same base table.  A
    # whole-plan n! enumeration is both unnecessary and disastrous for TPC-DS
    # joins whose relation names are almost all distinct.
    table_permutations = [
        tuple(itertools.permutations(left_by_table[table])) for table in table_names
    ]
    for choices in itertools.product(*table_permutations):
        alias_bijection = {
            right_alias: left_alias
            for table, left_aliases in zip(table_names, choices)
            for right_alias, left_alias in zip(right_by_table[table], left_aliases)
        }
        right_fingerprint = _canonical_flat_plan(
            right.flat_plan,
            alias_bijection,
            preserve_predicate_order=False,
        )
        if right_fingerprint != left_fingerprint:
            continue
        return {
            "rule": "flat-inner-relational-equivalence",
            "kind": "pair-safety",
            "sideConditions": {
                "baseRelationOccurrenceBijection": alias_bijection,
                "onlyInnerProductsFiltersProjectsAndOrdinaryGroups": True,
                "predicateLaw": (
                    "conjunction permutation/idempotence, simple equality closure, "
                    "and strict integer-bound subsumption"
                ),
                "whereObservation": "TRUE acceptance under SQL Bool3",
                "groupKeyOrderIgnored": True,
                "constantGroupKeyRemovedOnlyWithNonconstantKey": True,
                "nullSensitiveSelfJoinElimination": False,
                "inequalityImplicationUsed": "strict integer bounds on one field only",
                "checkedArithmeticErasedByEqualitySubstitution": False,
                "checkedArithmeticPresent": False,
            },
        }
    return None


def attest_lowered_pair_safety(
    left_rel: dict[str, Any],
    right_rel: dict[str, Any],
    left: CompiledCosetteQuery,
    right: CompiledCosetteQuery,
) -> dict[str, Any] | None:
    if left.sql == right.sql:
        paired_acceptance = next(
            (
                item
                for item in left.attestations
                if item.get("rule")
                == "paired-where-bool3-true-acceptance-closure"
                and item in right.attestations
            ),
            None,
        )
        if paired_acceptance is not None:
            return paired_acceptance
        return {
            "rule": "identical-lowered-query-error-and-null-closure",
            "kind": "pair-safety",
            "sideConditions": {
                "loweredSqlByteIdentical": True,
                "integerOverflowAndRuntimeErrorPathsIdentical": True,
                "threeValuedPredicateBehaviorIdentical": True,
            },
        }
    direct_substitution = attest_filter_equality_projection_substitution(
        left_rel, right_rel
    )
    if direct_substitution is not None:
        return direct_substitution
    # The relational fragments below may reorder or move predicates across
    # join/filter boundaries.  That is harmless for ordinary Bool3 acceptance
    # but not for PostgreSQL checked integer arithmetic: a moved predicate can
    # be evaluated on a different candidate-row set and expose a different
    # overflow outcome.  Only byte-identical lowered programs above close this
    # obligation.
    if any(
        item.get("kind") == "pair-safety-obligation"
        for item in left.attestations + right.attestations
    ):
        return None
    flat_attestation = attest_flat_inner_relational_equivalence(left, right)
    if flat_attestation is not None:
        return flat_attestation
    return None


class RexDigestParser:
    """Small parser for the closed Calcite Rex digest used by this adapter.

    This deliberately recognizes fewer expressions than Calcite.  Unsupported
    syntax is a failed lowering, never a textual best guess.
    """

    def __init__(self, text: str):
        self.text = text
        self.position = 0

    def parse(self) -> RexExpr | None:
        try:
            expression = self.parse_expression()
            self.skip_space()
            return expression if self.position == len(self.text) else None
        except (ValueError, IndexError):
            return None

    def parse_expression(self) -> RexExpr:
        self.skip_space()
        if self.position >= len(self.text):
            raise ValueError("missing Rex expression")
        char = self.text[self.position]
        if char == "$" and self.position + 1 < len(self.text) and self.text[
            self.position + 1
        ].isdigit():
            self.position += 1
            start = self.position
            while self.position < len(self.text) and self.text[self.position].isdigit():
                self.position += 1
            expression = RexExpr("ref", self.text[start : self.position])
        elif char == "'":
            expression = RexExpr("literal", self.parse_string_literal())
        elif char.isdigit() or (
            char in "+-"
            and self.position + 1 < len(self.text)
            and self.text[self.position + 1].isdigit()
        ):
            expression = RexExpr("literal", self.parse_numeric_literal())
        else:
            name = self.parse_name()
            self.skip_space()
            if self.position < len(self.text) and self.text[self.position] == "(":
                self.position += 1
                args: list[RexExpr] = []
                self.skip_space()
                if self.position < len(self.text) and self.text[self.position] != ")":
                    while True:
                        args.append(self.parse_expression())
                        self.skip_space()
                        if self.position < len(self.text) and self.text[self.position] == ",":
                            self.position += 1
                            continue
                        break
                if self.position >= len(self.text) or self.text[self.position] != ")":
                    raise ValueError("unterminated Rex call")
                self.position += 1
                expression = RexExpr("call", name, tuple(args))
            else:
                expression = RexExpr("atom", name)
        self.skip_space()
        if self.position < len(self.text) and self.text[self.position] == ":":
            self.position += 1
            type_name = self.parse_type_name()
            expression = RexExpr(
                expression.kind,
                expression.value,
                expression.args,
                type_name=type_name,
            )
        return expression

    def parse_string_literal(self) -> str:
        start = self.position
        self.position += 1
        while self.position < len(self.text):
            if self.text[self.position] != "'":
                self.position += 1
                continue
            self.position += 1
            if self.position < len(self.text) and self.text[self.position] == "'":
                self.position += 1
                continue
            return self.text[start : self.position]
        raise ValueError("unterminated Rex string")

    def parse_numeric_literal(self) -> str:
        start = self.position
        if self.text[self.position] in "+-":
            self.position += 1
        while self.position < len(self.text) and self.text[self.position].isdigit():
            self.position += 1
        if self.position < len(self.text) and self.text[self.position] == ".":
            self.position += 1
            while self.position < len(self.text) and self.text[self.position].isdigit():
                self.position += 1
        return self.text[start : self.position]

    def parse_name(self) -> str:
        start = self.position
        while self.position < len(self.text):
            char = self.text[self.position]
            if char in "(),:":
                break
            self.position += 1
        if self.position == start:
            raise ValueError("missing Rex call name")
        name = self.text[start : self.position].strip(ASCII_SQL_WHITESPACE)
        if not name:
            raise ValueError("missing Rex call name")
        return name

    def parse_type_name(self) -> str:
        start = self.position
        depth = 0
        while self.position < len(self.text):
            char = self.text[self.position]
            if char == "(" :
                depth += 1
            elif char == ")":
                if depth == 0:
                    break
                depth -= 1
            elif char == "," and depth == 0:
                break
            self.position += 1
        type_name = self.text[start : self.position].strip()
        if not type_name:
            raise ValueError("empty Rex type annotation")
        return type_name

    def skip_space(self) -> None:
        while (
            self.position < len(self.text)
            and self.text[self.position] in ASCII_SQL_WHITESPACE
        ):
            self.position += 1


def parse_rex_digest(text: Any) -> RexExpr | None:
    return RexDigestParser(text).parse() if isinstance(text, str) else None


def rex_digest(expression: RexExpr) -> str:
    """Serialize the closed Rex fragment parsed by :class:`RexDigestParser`."""

    if expression.kind == "ref":
        rendered = f"${expression.value}"
    elif expression.kind in {"literal", "atom"}:
        rendered = expression.value
    elif expression.kind == "call":
        rendered = (
            expression.value
            + "("
            + ", ".join(rex_digest(argument) for argument in expression.args)
            + ")"
        )
    else:
        raise ValueError(f"unknown Rex expression kind: {expression.kind}")
    if expression.type_name:
        rendered += f":{expression.type_name}"
    return rendered


def rex_call(operator: str, *arguments: RexExpr) -> RexExpr:
    return RexExpr("call", operator, tuple(arguments))


def rex_operator(expression: RexExpr, operator: str, arity: int | None = None) -> bool:
    return (
        expression.kind == "call"
        and expression.value.upper() == operator
        and (arity is None or len(expression.args) == arity)
    )


def rex_ref_index(expression: RexExpr) -> int | None:
    return int(expression.value) if expression.kind == "ref" else None


def rex_is_null_literal(expression: RexExpr) -> bool:
    return expression.kind == "atom" and expression.value.lower() == "null"


def rex_integer_literal(expression: RexExpr) -> int | None:
    if (
        expression.kind != "literal"
        or re.fullmatch(r"0|-?[1-9][0-9]*", expression.value) is None
    ):
        return None
    return int(expression.value)


def rex_same(left: RexExpr, right: RexExpr) -> bool:
    return rex_digest(left) == rex_digest(right)


def rex_flatten(expression: RexExpr, operator: str) -> list[RexExpr]:
    if rex_operator(expression, operator):
        result: list[RexExpr] = []
        for argument in expression.args:
            result.extend(rex_flatten(argument, operator))
        return result
    return [expression]


def rex_join(operator: str, expressions: list[RexExpr]) -> RexExpr:
    if not expressions:
        return RexExpr("atom", "true" if operator == "AND" else "false")
    result = expressions[0]
    for expression in expressions[1:]:
        result = rex_call(operator, result, expression)
    return result


def rex_is_simple_equality(expression: RexExpr) -> bool:
    if not rex_operator(expression, "=", 2):
        return False
    left, right = expression.args
    return (
        (left.kind == "ref" and right.kind in {"ref", "literal"})
        or (right.kind == "ref" and left.kind in {"ref", "literal"})
    )


def rex_error_free_comparison(expression: RexExpr) -> bool:
    if not rex_operator(expression, expression.value.upper(), 2) or expression.value.upper() not in {
        "=",
        "<",
        ">",
        "<>",
    }:
        return False
    return all(argument.kind in {"ref", "literal"} for argument in expression.args)


def rex_error_free_direct_boolean(expression: RexExpr) -> bool:
    """Recognize Bool3 formulas whose reassociation cannot expose an error.

    Calcite prints associative AND/OR calls with arbitrary arity.  Cosette's
    parser accepts the corresponding binary SQL syntax, but rebracketing is an
    admissible bridge only when every leaf is a direct, error-free comparison.
    In particular, arithmetic, casts, CASE, subqueries and NULL tests remain
    outside this closure even when Calcite nests them under AND/OR.
    """

    if expression.kind == "atom":
        return expression.value.lower() in {"true", "false"}
    if expression.kind != "call":
        return False
    operator = expression.value.upper()
    if operator in {"=", "<", ">", "<>"}:
        return rex_error_free_comparison(expression)
    if operator in {"AND", "OR"}:
        return len(expression.args) >= 2 and all(
            rex_error_free_direct_boolean(argument)
            for argument in expression.args
        )
    if operator == "NOT":
        return len(expression.args) == 1 and rex_error_free_direct_boolean(
            expression.args[0]
        )
    return False


def _rewrite_finite_exclusion_search(condition: str) -> tuple[str, bool]:
    """Lower Calcite's exact two-point exclusion Sarg to ordinary Bool3.

    ``Sarg[(-inf..a), (a..b), (b..+inf)]`` is the representation Calcite
    emits for ``NOT IN (a, b)`` with two non-NULL integer literals.  The three
    intervals are open at ``a`` and ``b``; no NULL-as-TRUE policy is admitted.
    """

    pattern = re.compile(
        r"SEARCH\(\$(?P<field>[0-9]+),\s*"
        r"Sarg\[\(-∞\.\.(?P<a>-?[0-9]+)\),\s*"
        r"\((?P<a2>-?[0-9]+)\.\.(?P<b>-?[0-9]+)\),\s*"
        r"\((?P<b2>-?[0-9]+)\.\.\+∞\)\]\)(?!\s*(?:;|NULL))"
    )
    changed = False

    def replace(match: re.Match[str]) -> str:
        nonlocal changed
        if (
            match.group("a") != match.group("a2")
            or match.group("b") != match.group("b2")
            or int(match.group("a")) >= int(match.group("b"))
        ):
            return match.group(0)
        changed = True
        field = match.group("field")
        return (
            f"NOT(OR(=(${field}, {match.group('a')}), "
            f"=(${field}, {match.group('b')})))"
        )

    return pattern.sub(replace, condition), changed


def _rex_scalar_type(
    expression: RexExpr,
    fields: list[dict[str, Any]],
) -> str | None:
    index = rex_ref_index(expression)
    if index is not None:
        return (
            canonical_type(fields[index]["type"])
            if index < len(fields)
            else None
        )
    if expression.kind == "literal":
        if expression.value.startswith("'"):
            return "VARCHAR"
        if rex_integer_literal(expression) is not None:
            return canonical_type(expression.type_name or "INTEGER")
    return None


def _normalize_error_free_boolean(
    expression: RexExpr,
    fields: list[dict[str, Any]],
) -> tuple[RexExpr, set[str]]:
    """Normalize only error-free Bool3 identities over refs and literals."""

    rules: set[str] = set()
    if expression.kind != "call":
        return expression, rules
    arguments: list[RexExpr] = []
    for argument in expression.args:
        normalized, child_rules = _normalize_error_free_boolean(argument, fields)
        arguments.append(normalized)
        rules.update(child_rules)
    expression = RexExpr(
        expression.kind,
        expression.value,
        tuple(arguments),
        expression.type_name,
    )

    if rex_operator(expression, "<>", 2) and rex_error_free_comparison(expression):
        rules.add("bool3-not-equal-lowering")
        return rex_call("NOT", rex_call("=", *expression.args)), rules

    if rex_operator(expression, "NOT", 1) and rex_operator(expression.args[0], "OR"):
        leaves = rex_flatten(expression.args[0], "OR")
        if leaves and all(rex_is_simple_equality(leaf) for leaf in leaves):
            rules.add("bool3-de-morgan-equality-lowering")
            return rex_join(
                "AND",
                [rex_call("NOT", leaf) for leaf in leaves],
            ), rules

    if rex_operator(expression, "OR"):
        leaves = rex_flatten(expression, "OR")
        if leaves and all(rex_is_simple_equality(leaf) for leaf in leaves):
            ordered = sorted({rex_digest(leaf): leaf for leaf in leaves}.items())
            normalized = rex_join("OR", [leaf for _, leaf in ordered])
            if not rex_same(normalized, expression):
                rules.add("bool3-error-free-or-commutation-idempotence")
                expression = normalized

    if rex_operator(expression, "OR", 2):
        left, right = expression.args
        trichotomy = (
            rex_operator(left, "<", 2)
            and rex_operator(right, ">", 2)
            and rex_same(left.args[0], right.args[0])
            and rex_same(left.args[1], right.args[1])
            and rex_error_free_comparison(left)
            and rex_error_free_comparison(right)
        ) or (
            rex_operator(left, ">", 2)
            and rex_operator(right, "<", 2)
            and rex_same(left.args[0], right.args[0])
            and rex_same(left.args[1], right.args[1])
            and rex_error_free_comparison(left)
            and rex_error_free_comparison(right)
        )
        # This bridge has no shared Calcite/Cosette/PostgreSQL contract for
        # floating/NaN ordering or string collation. Keep the law to the
        # fixed-width integer domains whose order is explicitly attested here.
        if trichotomy:
            operand_types = {
                _rex_scalar_type(argument, fields) for argument in left.args
            }
            trichotomy = (
                None not in operand_types
                and operand_types <= {"INTEGER", "BIGINT"}
            )
        if trichotomy:
            rules.add("bool3-total-order-trichotomy-lowering")
            return rex_call("NOT", rex_call("=", *left.args)), rules

    if (
        rex_operator(expression, "AND") or rex_operator(expression, "OR")
    ) and len(expression.args) != 2 and rex_error_free_direct_boolean(expression):
        # Preserve operand order.  SQL Bool3 AND/OR are associative, and the
        # direct-comparison gate above ensures that changing parentheses cannot
        # change which runtime error is observed.
        rules.add("bool3-error-free-associative-binarization")
        return rex_join(expression.value.upper(), list(expression.args)), rules
    return expression, rules


def _not_null_ref(expression: RexExpr) -> int | None:
    if not rex_operator(expression, "IS NOT NULL", 1):
        return None
    return rex_ref_index(expression.args[0])


def _comparison_direct_refs(expression: RexExpr) -> set[int]:
    if not rex_operator(expression, expression.value.upper(), 2) or expression.value.upper() not in {
        "=",
        "<",
        ">",
    }:
        return set()
    if not all(argument.kind in {"ref", "literal"} for argument in expression.args):
        return set()
    return {
        index
        for argument in expression.args
        if (index := rex_ref_index(argument)) is not None
    }


def _normalize_filter_null_acceptance(expression: RexExpr) -> tuple[RexExpr, set[str]]:
    rules: set[str] = set()
    if rex_operator(expression, "OR", 2):
        left, right = expression.args
        for null_side, not_null_side in ((left, right), (right, left)):
            if rex_operator(null_side, "IS NULL", 1):
                null_ref = rex_ref_index(null_side.args[0])
                not_null_ref = _not_null_ref(not_null_side)
                if null_ref is not None and null_ref == not_null_ref:
                    rules.add("bool3-null-partition-tautology")
                    return RexExpr("atom", "true"), rules

    if rex_operator(expression, "AND"):
        conjuncts = rex_flatten(expression, "AND")
        comparison_refs: set[int] = set()
        for conjunct in conjuncts:
            comparison_refs.update(_comparison_direct_refs(conjunct))
        retained = [
            conjunct
            for conjunct in conjuncts
            if (_not_null_ref(conjunct) not in comparison_refs)
            or _not_null_ref(conjunct) is None
        ]
        if len(retained) != len(conjuncts):
            rules.add("where-comparison-implies-not-null")
            return rex_join("AND", retained), rules

    # Calcite expands ``x IS NOT DISTINCT FROM nonnull_literal`` to the form
    # below.  In WHERE, both this form and ordinary equality accept exactly the
    # rows on which equality is TRUE; UNKNOWN rows are rejected by the filter.
    if rex_operator(expression, "OR", 2):
        for null_branch, equality_branch in (
            (expression.args[0], expression.args[1]),
            (expression.args[1], expression.args[0]),
        ):
            if not (
                rex_operator(null_branch, "AND", 2)
                and rex_operator(equality_branch, "IS TRUE", 1)
                and rex_operator(equality_branch.args[0], "=", 2)
            ):
                continue
            equality = equality_branch.args[0]
            null_tests = null_branch.args
            if not all(rex_operator(item, "IS NULL", 1) for item in null_tests):
                continue
            tested = [item.args[0] for item in null_tests]
            for ref_side, literal_side in (
                (equality.args[0], equality.args[1]),
                (equality.args[1], equality.args[0]),
            ):
                if (
                    ref_side.kind == "ref"
                    and literal_side.kind == "literal"
                    and any(rex_same(ref_side, item) for item in tested)
                    and any(rex_same(literal_side, item) for item in tested)
                ):
                    rules.add("where-nonnull-literal-not-distinct-lowering")
                    return equality, rules
    return expression, rules


def _case_parts(expression: RexExpr) -> tuple[list[tuple[RexExpr, RexExpr]], RexExpr] | None:
    if not rex_operator(expression, "CASE") or len(expression.args) < 3 or len(expression.args) % 2 == 0:
        return None
    return (
        list(zip(expression.args[0:-1:2], expression.args[1:-1:2])),
        expression.args[-1],
    )


def _integer_field(fields: list[dict[str, Any]], expression: RexExpr) -> bool:
    index = rex_ref_index(expression)
    return (
        index is not None
        and index < len(fields)
        and canonical_type(fields[index]["type"]) in {"INTEGER", "BIGINT"}
    )


def _normalize_case_equals_integer(
    case_expression: RexExpr,
    target: RexExpr,
    fields: list[dict[str, Any]],
) -> RexExpr | None:
    target_value = rex_integer_literal(target)
    parts = _case_parts(case_expression)
    if target_value is None or parts is None:
        return None
    branches, otherwise = parts

    # Closed searched-CASE over equality tests on one integer field.  Branch
    # keys are constants and therefore mutually exclusive; duplicate later
    # keys are unreachable.  The ELSE result must not match the target.
    reference: RexExpr | None = None
    seen_keys: set[int] = set()
    selected: list[RexExpr] = []
    for condition, result in branches:
        if not rex_operator(condition, "=", 2):
            break
        candidate_ref: RexExpr | None = None
        candidate_key: int | None = None
        for left, right in ((condition.args[0], condition.args[1]), (condition.args[1], condition.args[0])):
            if left.kind == "ref" and rex_integer_literal(right) is not None:
                candidate_ref, candidate_key = left, rex_integer_literal(right)
                break
        result_value = rex_integer_literal(result)
        if (
            candidate_ref is None
            or candidate_key is None
            or (result_value is None and not rex_is_null_literal(result))
            or not _integer_field(fields, candidate_ref)
            or (reference is not None and not rex_same(reference, candidate_ref))
        ):
            break
        reference = candidate_ref
        if candidate_key in seen_keys:
            continue
        seen_keys.add(candidate_key)
        if result_value == target_value:
            selected.append(condition)
    else:
        otherwise_value = rex_integer_literal(otherwise)
        if (
            (otherwise_value is not None or rex_is_null_literal(otherwise))
            and otherwise_value != target_value
            and selected
        ):
            return rex_join("OR", selected)

    # One-branch CASE whose ELSE is the integer field used by a strict bound.
    # If ``field = target`` implies that the WHEN condition is FALSE, the ELSE
    # equality already carries the otherwise-branch guard.
    if len(branches) != 1:
        return None
    condition, then_value = branches[0]
    if not rex_operator(condition, ">", 2):
        return None
    condition_ref, bound = condition.args
    bound_value = rex_integer_literal(bound)
    if (
        condition_ref.kind != "ref"
        or bound_value is None
        or not rex_same(otherwise, condition_ref)
        or target_value > bound_value
        or not _integer_field(fields, condition_ref)
        or not rex_error_free_comparison(condition)
        or then_value.kind not in {"ref", "literal"}
        or otherwise.kind not in {"ref", "literal"}
    ):
        return None
    return rex_call(
        "OR",
        rex_call("AND", condition, rex_call("=", then_value, target)),
        rex_call("=", otherwise, target),
    )


def _null_if_case_condition(expression: RexExpr) -> RexExpr | None:
    if not rex_operator(expression, "IS NULL", 1):
        return None
    parts = _case_parts(expression.args[0])
    if parts is None:
        return None
    branches, otherwise = parts
    if (
        len(branches) == 1
        and rex_is_null_literal(branches[0][1])
        and otherwise.kind == "literal"
        and not rex_is_null_literal(otherwise)
        and rex_error_free_comparison(branches[0][0])
    ):
        return branches[0][0]
    return None


def _normalize_filter_case_acceptance(
    expression: RexExpr,
    fields: list[dict[str, Any]],
) -> tuple[RexExpr, set[str]]:
    if rex_operator(expression, "CASE", 3):
        condition, when_true, when_false = expression.args
        if (
            when_true.kind == "atom"
            and when_true.value.lower() == "true"
            and when_false.kind == "atom"
            and when_false.value.lower() == "false"
            and rex_error_free_comparison(condition)
        ):
            return condition, {"where-boolean-case-acceptance-lowering"}

    if rex_operator(expression, "=", 2):
        for case_expression, target in (
            (expression.args[0], expression.args[1]),
            (expression.args[1], expression.args[0]),
        ):
            if rex_operator(case_expression, "CASE"):
                normalized = _normalize_case_equals_integer(
                    case_expression, target, fields
                )
                if normalized is not None:
                    return normalized, {"where-integer-case-acceptance-lowering"}

    if rex_operator(expression, "OR"):
        leaves = rex_flatten(expression, "OR")
        conditions = [_null_if_case_condition(leaf) for leaf in leaves]
        if conditions and all(condition is not None for condition in conditions):
            return rex_join(
                "OR", [condition for condition in conditions if condition is not None]
            ), {"where-null-producing-case-acceptance-lowering"}

    if rex_operator(expression, "IS TRUE", 1) and rex_operator(
        expression.args[0], "CASE", 3
    ):
        condition, then_value, otherwise = expression.args[0].args
        then_condition = _null_if_case_condition(then_value)
        otherwise_condition = _null_if_case_condition(otherwise)
        if (
            then_condition is not None
            and otherwise_condition is not None
            and rex_same(condition, then_condition)
        ):
            return rex_call(
                "OR", then_condition, otherwise_condition
            ), {"where-null-producing-case-acceptance-lowering"}
    return expression, set()


def normalize_filter_condition(
    condition: str,
    fields: list[dict[str, Any]],
) -> tuple[str, list[dict[str, Any]]]:
    condition, search_changed = _rewrite_finite_exclusion_search(condition)
    expression = parse_rex_digest(condition)
    if expression is None:
        return condition, []
    rules: set[str] = set()
    if search_changed:
        rules.add("finite-integer-exclusion-search-lowering")
    expression, boolean_rules = _normalize_error_free_boolean(expression, fields)
    rules.update(boolean_rules)
    expression, null_rules = _normalize_filter_null_acceptance(expression)
    rules.update(null_rules)
    expression, case_rules = _normalize_filter_case_acceptance(expression, fields)
    rules.update(case_rules)
    # CASE expansion may expose ordinary <>/NOT-OR identities.
    expression, final_boolean_rules = _normalize_error_free_boolean(expression, fields)
    rules.update(final_boolean_rules)
    if not rules:
        return condition, []
    return rex_digest(expression), [
        {
            "rule": rule,
            "kind": "semantic-preprocessing",
            "sideConditions": {
                "context": "LogicalFilter TRUE acceptance only",
                "postgresBool3UnknownRejected": True,
                "directComparisonsAreErrorFree": True,
                "noScalarOutputValueWasRewritten": True,
            },
        }
        for rule in sorted(rules)
    ]


def normalize_inner_join_condition(
    condition: str,
    fields: list[dict[str, Any]],
) -> tuple[str, list[dict[str, Any]]]:
    condition, search_changed = _rewrite_finite_exclusion_search(condition)
    expression = parse_rex_digest(condition)
    if expression is None:
        return condition, []
    expression, rules = _normalize_error_free_boolean(expression, fields)
    if search_changed:
        rules.add("finite-integer-exclusion-search-lowering")
    if not rules:
        return condition, []
    return rex_digest(expression), [
        {
            "rule": rule,
            "kind": "semantic-preprocessing",
            "sideConditions": {
                "context": "INNER JOIN condition TRUE matching only",
                "postgresBool3UnknownDoesNotMatch": True,
                "directComparisonsAreErrorFree": True,
                "noOuterJoinNullExtension": True,
            },
        }
        for rule in sorted(rules)
    ]


def _join_implied_nonnull_indexes(condition: Any, arity: int) -> set[int]:
    expression = parse_rex_digest(condition)
    if expression is None:
        return set()
    result: set[int] = set()
    for conjunct in rex_flatten(expression, "AND"):
        indexes = _comparison_direct_refs(conjunct)
        if indexes and all(index < arity for index in indexes):
            result.update(indexes)
    return result


def _not_null_conjunction_indexes(condition: Any) -> set[int] | None:
    expression = parse_rex_digest(condition)
    if expression is None:
        return None
    result: set[int] = set()
    for conjunct in rex_flatten(expression, "AND"):
        index = _not_null_ref(conjunct)
        if index is None:
            return None
        result.add(index)
    return result or None


def _strip_join_redundant_not_null_filters(
    relation: dict[str, Any],
    implied_output_indexes: set[int],
    path: str,
) -> tuple[dict[str, Any], list[dict[str, str]]]:
    node_type = relation.get("type")
    inputs = relation.get("inputs")
    if not isinstance(inputs, list) or len(inputs) != 1 or not isinstance(inputs[0], dict):
        return relation, []
    child = inputs[0]
    if node_type == "LogicalProject":
        projects = relation.get("projects")
        if not isinstance(projects, list):
            return relation, []
        parsed_projects = [parse_rex_digest(project) for project in projects]
        # A checked or otherwise computed Project is evaluated before the
        # parent join.  Removing its input filter could expose new overflow or
        # runtime-error rows even if the join later rejects NULL, so every
        # project expression must be a direct field reference.
        if any(
            project is None or rex_ref_index(project) is None
            for project in parsed_projects
        ):
            return relation, []
        mapped: set[int] = set()
        for index in implied_output_indexes:
            if index >= len(projects):
                return relation, []
            expression = parsed_projects[index]
            source_index = rex_ref_index(expression) if expression is not None else None
            if source_index is None:
                return relation, []
            mapped.add(source_index)
        normalized, sites = _strip_join_redundant_not_null_filters(
            child, mapped, f"{path}.inputs[0]"
        )
        if sites:
            relation["inputs"] = [normalized]
        return relation, sites
    if node_type == "LogicalFilter":
        tested = _not_null_conjunction_indexes(relation.get("condition"))
        if tested is not None and tested <= implied_output_indexes:
            return child, [
                {
                    "path": f"{path}.condition",
                    "rule": "inner-comparison-implies-input-not-null",
                    "beforeDigest": str(relation.get("condition")),
                    "afterDigest": "<elided: implied by INNER comparison>",
                }
            ]
        # Do not cross an unrelated filter: it may be errorful, and moving the
        # not-NULL gate below it would change which rows evaluate that filter.
        return relation, []
    return relation, []


def _direct_bound_output_indexes(relation: dict[str, Any]) -> set[int]:
    """Return outputs whose value is a direct base-scan field reference."""

    node_type = relation.get("type")
    inputs = relation.get("inputs")
    row_type = validated_row_type(relation)
    if row_type is None or not isinstance(inputs, list):
        return set()
    if node_type == "LogicalTableScan":
        return set(range(len(row_type)))
    if node_type in {"LogicalFilter", "LogicalSort"} and len(inputs) == 1 and isinstance(inputs[0], dict):
        return _direct_bound_output_indexes(inputs[0])
    if node_type == "LogicalProject" and len(inputs) == 1 and isinstance(inputs[0], dict):
        source = _direct_bound_output_indexes(inputs[0])
        projects = relation.get("projects")
        if not isinstance(projects, list) or len(projects) != len(row_type):
            return set()
        result: set[int] = set()
        for output_index, project in enumerate(projects):
            expression = parse_rex_digest(project)
            source_index = rex_ref_index(expression) if expression is not None else None
            if source_index is not None and source_index in source:
                result.add(output_index)
        return result
    if node_type == "LogicalJoin" and len(inputs) == 2 and all(
        isinstance(child, dict) for child in inputs
    ):
        left_type = validated_row_type(inputs[0])
        right_type = validated_row_type(inputs[1])
        if left_type is None or right_type is None:
            return set()
        left = _direct_bound_output_indexes(inputs[0])
        right = _direct_bound_output_indexes(inputs[1])
        return left | {len(left_type) + index for index in right}
    if node_type == "LogicalUnion" and inputs and all(
        isinstance(child, dict) for child in inputs
    ):
        direct_sets = [_direct_bound_output_indexes(child) for child in inputs]
        return set.intersection(*direct_sets) if direct_sets else set()
    return set()


def _risky_rex_inventory(relation: dict[str, Any]) -> list[dict[str, str]]:
    inventory: list[dict[str, str]] = []

    def expression_nodes(expression: RexExpr, path: str) -> None:
        if expression.kind == "atom":
            if expression.value.lower() == "null":
                inventory.append({"feature": "null", "path": path})
            elif expression.value.lower() in {"true", "false"}:
                inventory.append(
                    {"feature": "booleanTestOrLiteral", "path": path}
                )
        elif expression.kind == "call":
            operator = expression.value.upper()
            if operator == "CASE":
                inventory.append({"feature": "case", "path": path})
            if operator in {"IS NULL", "IS NOT NULL"}:
                inventory.append({"feature": "null", "path": path})
            if operator in {"IS TRUE", "IS NOT TRUE"}:
                inventory.append(
                    {"feature": "booleanTestOrLiteral", "path": path}
                )
            for index, argument in enumerate(expression.args):
                expression_nodes(argument, f"{path}.args[{index}]")

    def visit(node: dict[str, Any], path: str) -> None:
        for field_name in ("condition", "projects", "aggCalls"):
            values = node.get(field_name)
            if not isinstance(values, list):
                values = [values]
            for index, value in enumerate(values):
                expression = parse_rex_digest(value)
                if expression is not None:
                    suffix = f"[{index}]" if len(values) > 1 else ""
                    expression_nodes(expression, f"{path}.{field_name}{suffix}")
        for index, child in enumerate(node.get("inputs", []) or []):
            if isinstance(child, dict):
                visit(child, f"{path}.inputs[{index}]")

    visit(relation, "root")
    return inventory


def _true_requires_nonnull_refs(expression: RexExpr) -> set[int]:
    """Return refs guaranteed non-NULL whenever an error-free formula is TRUE."""

    if expression.kind != "call":
        return set()
    operator = expression.value.upper()
    if operator in {"=", "<", ">", "<>"} and rex_error_free_comparison(
        expression
    ):
        return {
            index
            for argument in expression.args
            if (index := rex_ref_index(argument)) is not None
        }
    if operator == "AND":
        return set().union(
            *(_true_requires_nonnull_refs(item) for item in expression.args)
        )
    if operator == "OR" and expression.args:
        requirements = [
            _true_requires_nonnull_refs(item) for item in expression.args
        ]
        return set.intersection(*requirements)
    if (
        operator == "NOT"
        and len(expression.args) == 1
        and expression.args[0].kind == "call"
        and expression.args[0].value.upper() in {"=", "<", ">", "<>"}
        and rex_error_free_comparison(expression.args[0])
    ):
        return _true_requires_nonnull_refs(expression.args[0])
    return set()


def strengthen_outer_join_under_null_rejecting_filter(
    relation: dict[str, Any],
) -> tuple[dict[str, Any], str] | None:
    """Turn an outer join into INNER when its WHERE rejects null extension."""

    if relation.get("type") != "LogicalFilter":
        return None
    filter_inputs = relation.get("inputs")
    if (
        not isinstance(filter_inputs, list)
        or len(filter_inputs) != 1
        or not isinstance(filter_inputs[0], dict)
        or filter_inputs[0].get("type") != "LogicalJoin"
    ):
        return None
    join = filter_inputs[0]
    join_type = str(join.get("joinType") or "").upper()
    join_inputs = join.get("inputs")
    if join_type not in {"LEFT", "RIGHT", "FULL"} or not (
        isinstance(join_inputs, list)
        and len(join_inputs) == 2
        and all(isinstance(item, dict) for item in join_inputs)
    ):
        return None
    left_row = validated_row_type(join_inputs[0])
    right_row = validated_row_type(join_inputs[1])
    filter_condition = relation.get("condition")
    join_condition = join.get("condition")
    if (
        left_row is None
        or right_row is None
        or not isinstance(filter_condition, str)
        or not isinstance(join_condition, str)
    ):
        return None
    filter_expression = parse_rex_digest(filter_condition)
    join_expression = parse_rex_digest(join_condition)
    if (
        filter_expression is None
        or join_expression is None
        or not rex_error_free_direct_boolean(filter_expression)
        or not rex_error_free_direct_boolean(join_expression)
    ):
        return None
    required = _true_requires_nonnull_refs(filter_expression)
    if any(index >= len(left_row) + len(right_row) for index in required):
        return None
    left_required = any(index < len(left_row) for index in required)
    right_required = any(
        len(left_row) <= index < len(left_row) + len(right_row)
        for index in required
    )
    rejects_all_null_extensions = (
        (join_type == "LEFT" and right_required)
        or (join_type == "RIGHT" and left_required)
        or (join_type == "FULL" and left_required and right_required)
    )
    if not rejects_all_null_extensions:
        return None
    lowered = json.loads(json.dumps(relation))
    lowered["inputs"][0]["joinType"] = "inner"
    return lowered, join_type


def _risky_rex_operator_counts(relation: dict[str, Any]) -> dict[str, int]:
    counts = {"case": 0, "null": 0, "booleanTestOrLiteral": 0}
    for item in _risky_rex_inventory(relation):
        counts[item["feature"]] += 1
    return counts


def preprocess_cosette_rel(
    relation: dict[str, Any],
    *,
    bag_observation: bool,
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    """Apply closed, IR-backed rewrites before the Cosette compiler.

    Every rewrite is individually SQL-semantics preserving in the stated
    observation context.  This function never consults case ids or source SQL
    text; exact Calcite nodes and row types are the sole authority.
    """

    root = json.loads(json.dumps(relation))
    original_risky_counts = _risky_rex_operator_counts(root)
    original_risky_inventory = _risky_rex_inventory(root)
    attestations: list[dict[str, Any]] = []
    rewrite_sites: list[dict[str, str]] = []

    def visit(
        node: dict[str, Any],
        path: str = "root",
        *,
        order_observed: bool = False,
    ) -> dict[str, Any]:
        node_type = node.get("type")
        child_order_observed = False
        if node_type in {"LogicalFilter", "LogicalProject"}:
            # These unary nodes preserve their input sequence.  A slice above
            # them can therefore observe an ORDER BY below them.
            child_order_observed = order_observed
        elif node_type == "LogicalSort":
            collation = node.get("collation")
            establishes_order = isinstance(collation, list) and bool(collation)
            has_slice = node.get("offset") is not None or node.get("fetch") is not None
            # A Sort with its own keys establishes a fresh order.  A keyless
            # OFFSET/FETCH instead consumes the child's order, as does an
            # order-sensitive ancestor reached through a keyless Sort.
            child_order_observed = (
                (order_observed or has_slice) and not establishes_order
            )
        inputs = node.get("inputs")
        if isinstance(inputs, list):
            node["inputs"] = [
                visit(
                    child,
                    f"{path}.inputs[{index}]",
                    order_observed=child_order_observed,
                )
                if isinstance(child, dict)
                else child
                for index, child in enumerate(inputs)
            ]

        if node.get("type") == "LogicalJoin" and str(
            node.get("joinType") or ""
        ).upper() == "INNER":
            join_inputs = node.get("inputs")
            if isinstance(join_inputs, list) and len(join_inputs) == 2:
                left_fields = validated_row_type(join_inputs[0])
                right_fields = validated_row_type(join_inputs[1])
                if left_fields is not None and right_fields is not None:
                    condition = node.get("condition")
                    if isinstance(condition, str):
                        normalized, local_attestations = normalize_inner_join_condition(
                            condition,
                            left_fields + right_fields,
                        )
                        if local_attestations:
                            node["condition"] = normalized
                            attestations.extend(local_attestations)
                            rewrite_sites.extend(
                                {
                                    "path": f"{path}.condition",
                                    "rule": item["rule"],
                                    "beforeDigest": condition,
                                    "afterDigest": normalized,
                                }
                                for item in local_attestations
                            )
                    implied = _join_implied_nonnull_indexes(
                        node.get("condition"), len(left_fields) + len(right_fields)
                    )
                    left_indexes = {index for index in implied if index < len(left_fields)}
                    right_indexes = {
                        index - len(left_fields)
                        for index in implied
                        if index >= len(left_fields)
                    }
                    left, left_sites = _strip_join_redundant_not_null_filters(
                        join_inputs[0], left_indexes, f"{path}.inputs[0]"
                    )
                    right, right_sites = _strip_join_redundant_not_null_filters(
                        join_inputs[1], right_indexes, f"{path}.inputs[1]"
                    )
                    removed_sites = left_sites + right_sites
                    if removed_sites:
                        node["inputs"] = [left, right]
                        rewrite_sites.extend(removed_sites)
                        attestations.append(
                            {
                                "rule": "inner-comparison-implies-input-not-null",
                                "kind": "semantic-preprocessing",
                                "sideConditions": {
                                    "joinType": "INNER",
                                    "removedFilterCount": len(removed_sites),
                                    "joinComparisonsUseDirectFields": True,
                                    "comparisonTRUEImpliesOperandsNonNULL": True,
                                    "comparisonExpressionsAreErrorFree": True,
                                },
                            }
                        )

        strengthened_outer = strengthen_outer_join_under_null_rejecting_filter(
            node
        )
        if strengthened_outer is not None:
            node, original_join_type = strengthened_outer
            attestations.append(
                {
                    "rule": "null-rejecting-filter-strengthens-outer-join",
                    "kind": "semantic-preprocessing",
                    "sideConditions": {
                        "originalJoinType": original_join_type,
                        "loweredJoinType": "INNER",
                        "filterContext": "WHERE TRUE acceptance",
                        "filterRejectsEveryNullExtendedRow": True,
                        "filterAndJoinConditionsUseOnlyDirectErrorFreeComparisons": True,
                        "outerJoinMatchRowsUnchanged": True,
                    },
                }
            )

        if node.get("type") == "LogicalFilter":
            filter_inputs = node.get("inputs")
            if (
                isinstance(filter_inputs, list)
                and len(filter_inputs) == 1
                and isinstance(filter_inputs[0], dict)
            ):
                fields = validated_row_type(filter_inputs[0])
                condition = node.get("condition")
                if fields is not None and isinstance(condition, str):
                    normalized, local_attestations = normalize_filter_condition(
                        condition, fields
                    )
                    if local_attestations:
                        node["condition"] = normalized
                        attestations.extend(local_attestations)
                        rewrite_sites.extend(
                            {
                                "path": f"{path}.condition",
                                "rule": item["rule"],
                                "beforeDigest": condition,
                                "afterDigest": normalized,
                            }
                            for item in local_attestations
                        )
                        expression = parse_rex_digest(normalized)
                        if (
                            expression is not None
                            and expression.kind == "atom"
                            and expression.value.lower() == "true"
                        ):
                            return filter_inputs[0]
                # Do not substitute an equality from a nested filter into an
                # outer filter. PostgreSQL may flatten the subquery and reorder
                # quals, so a checked expression rejected by the equality qual
                # can still be evaluated first and overflow. Projection-only
                # substitution remains handled by the dedicated pair attester.

        if (
            node.get("type") == "LogicalSort"
            and bag_observation
            and not order_observed
        ):
            sort_inputs = node.get("inputs")
            collation = node.get("collation")
            if (
                isinstance(sort_inputs, list)
                and len(sort_inputs) == 1
                and isinstance(sort_inputs[0], dict)
                and node.get("offset") is None
                and node.get("fetch") is None
                and isinstance(collation, list)
                and validated_row_type(node) == validated_row_type(sort_inputs[0])
            ):
                arity = len(validated_row_type(sort_inputs[0]) or [])
                sort_indexes = {
                    item.get("fieldIndex")
                    for item in collation
                    if isinstance(item, dict)
                }
                well_formed_keys = all(
                    isinstance(item, dict)
                    and isinstance(item.get("fieldIndex"), int)
                    and not isinstance(item.get("fieldIndex"), bool)
                    and 0 <= item["fieldIndex"] < arity
                    for item in collation
                )
                direct_bound_keys = sort_indexes <= _direct_bound_output_indexes(
                    sort_inputs[0]
                )
                child_row = validated_row_type(sort_inputs[0]) or []
                root_materialized_integer_keys = (
                    path == "root"
                    and well_formed_keys
                    and "LogicalAggregate"
                    in collect_rel_node_types(sort_inputs[0])
                    and all(
                        canonical_type(child_row[index]["type"])
                        in {"INTEGER", "BIGINT"}
                        for index in sort_indexes
                    )
                )
                if well_formed_keys and (
                    direct_bound_keys or root_materialized_integer_keys
                ):
                    rule = (
                        "bag-only-bound-sort-erasure"
                        if direct_bound_keys
                        else "bag-only-root-materialized-integer-sort-erasure"
                    )
                    attestations.append(
                        {
                            "rule": rule,
                            "kind": "semantic-preprocessing",
                            "sideConditions": {
                                "observation": "bag",
                                "orderNotConsumedByAncestor": True,
                                "offset": None,
                                "fetch": None,
                                "sortKeysAreDirectBaseScanFields": direct_bound_keys,
                                "rootSortKeysAreMaterializedFixedWidthIntegers": (
                                    root_materialized_integer_keys
                                ),
                                "keyExpressionsRemainEvaluatedInChild": True,
                                "rootInputContainsAggregate": (
                                    "LogicalAggregate"
                                    in collect_rel_node_types(sort_inputs[0])
                                ),
                                "rowTypeUnchanged": True,
                            },
                        }
                    )
                    return sort_inputs[0]
        return node

    normalized = visit(root)
    remaining_risky_counts = _risky_rex_operator_counts(normalized)
    remaining_risky_inventory = _risky_rex_inventory(normalized)
    if attestations and original_risky_counts != remaining_risky_counts:
        attestations.append(
            {
                "rule": "source-scalar-ir-rewrite-closure",
                "kind": "pair-safety",
                "sideConditions": {
                    "originalRiskyOperatorCounts": original_risky_counts,
                    "remainingRiskyOperatorCounts": remaining_risky_counts,
                    "originalRiskyNodes": original_risky_inventory,
                    "remainingRiskyNodes": remaining_risky_inventory,
                    "closedRewriteSites": rewrite_sites,
                    "sourceBoundExactCalciteTree": True,
                    "unhandledOperatorsRemainCompilerVisible": True,
                },
            }
        )
    return normalized, attestations


def _integer_ref_literal_equality(
    expression: RexExpr,
    fields: list[dict[str, Any]],
) -> tuple[int, int] | None:
    if not rex_operator(expression, "=", 2):
        return None
    left, right = expression.args
    if left.kind == "literal" and right.kind == "ref":
        left, right = right, left
    index = rex_ref_index(left)
    literal = rex_integer_literal(right)
    if (
        index is None
        or literal is None
        or index >= len(fields)
        or canonical_type(fields[index]["type"]) not in {"INTEGER", "BIGINT"}
    ):
        return None
    return index, literal


def _not_integer_equality(
    expression: RexExpr,
    fields: list[dict[str, Any]],
) -> tuple[int, int] | None:
    if not rex_operator(expression, "NOT", 1):
        return None
    return _integer_ref_literal_equality(expression.args[0], fields)


def _not_null_integer_ref(
    expression: RexExpr,
    fields: list[dict[str, Any]],
) -> int | None:
    if not rex_operator(expression, "IS NOT NULL", 1):
        return None
    index = rex_ref_index(expression.args[0])
    if (
        index is None
        or index >= len(fields)
        or canonical_type(fields[index]["type"]) not in {"INTEGER", "BIGINT"}
    ):
        return None
    return index


def _closed_nonnull_true_acceptance(
    expression: RexExpr,
    fields: list[dict[str, Any]],
) -> tuple[Any, ...] | None:
    """Canonicalize a tiny family of WHERE TRUE-acceptance identities.

    The result describes acceptance, not the complete Bool3 value.  For
    example UNKNOWN and FALSE are both rejected by WHERE.  Only fixed-width
    integer refs and non-NULL integer literals are admitted.
    """

    direct_nonnull = _not_null_integer_ref(expression, fields)
    if direct_nonnull is not None:
        return ("nonnull", direct_nonnull)

    if rex_operator(expression, "OR"):
        leaves = rex_flatten(expression, "OR")
        if len(leaves) == 2:
            excluded = [
                _not_integer_equality(leaf, fields) for leaf in leaves
            ]
            if (
                all(item is not None for item in excluded)
                and excluded[0][0] == excluded[1][0]
                and excluded[0][1] != excluded[1][1]
            ):
                return ("nonnull", excluded[0][0])

            nonnull_items = [
                _not_null_integer_ref(leaf, fields) for leaf in leaves
            ]
            for nonnull_position, nonnull_index in enumerate(nonnull_items):
                if nonnull_index is None:
                    continue
                other = _not_integer_equality(
                    leaves[1 - nonnull_position], fields
                )
                if other is not None and other[0] != nonnull_index:
                    return (
                        "or",
                        ("nonnull", nonnull_index),
                        ("not-equal", other[0], other[1]),
                    )

    if rex_operator(expression, "NOT", 1) and rex_operator(
        expression.args[0], "AND"
    ):
        equalities = [
            _integer_ref_literal_equality(item, fields)
            for item in rex_flatten(expression.args[0], "AND")
        ]
        if len(equalities) not in {2, 3} or any(
            item is None for item in equalities
        ):
            return None
        bound = [item for item in equalities if item is not None]
        contradictory: list[tuple[int, int, int]] = []
        for first in range(len(bound)):
            for second in range(first + 1, len(bound)):
                if (
                    bound[first][0] == bound[second][0]
                    and bound[first][1] != bound[second][1]
                ):
                    contradictory.append((first, second, bound[first][0]))
        if len(contradictory) != 1:
            return None
        first, second, contradiction_ref = contradictory[0]
        remaining = [
            item
            for index, item in enumerate(bound)
            if index not in {first, second}
        ]
        if not remaining:
            return ("nonnull", contradiction_ref)
        other_ref, other_literal = remaining[0]
        if other_ref == contradiction_ref:
            return None
        return (
            "or",
            ("nonnull", contradiction_ref),
            ("not-equal", other_ref, other_literal),
        )
    return None


def _single_filter_site(
    relation: dict[str, Any],
) -> tuple[tuple[int, ...], dict[str, Any]] | None:
    found: list[tuple[tuple[int, ...], dict[str, Any]]] = []

    def visit(node: dict[str, Any], path: tuple[int, ...]) -> None:
        if node.get("type") == "LogicalFilter":
            found.append((path, node))
        for index, child in enumerate(node.get("inputs", []) or []):
            if isinstance(child, dict):
                visit(child, path + (index,))

    visit(relation, ())
    return found[0] if len(found) == 1 else None


def _metadata_attests_not_null(
    metadata: dict[str, Any],
    table: str,
    column: str,
) -> bool:
    constraints = metadata.get("constraints")
    if not isinstance(constraints, list):
        return False
    expected = f"{table}__{column}".casefold()
    return any(
        isinstance(entry, dict)
        and isinstance(entry.get("not_null"), dict)
        and isinstance(entry["not_null"].get("value"), str)
        and entry["not_null"]["value"].casefold() == expected
        for entry in constraints
    )


def _direct_error_free_equality(
    expression: RexExpr,
    fields: list[dict[str, Any]],
) -> bool:
    if not rex_operator(expression, "=", 2) or not rex_error_free_comparison(
        expression
    ):
        return False
    left_type = _rex_scalar_type(expression.args[0], fields)
    right_type = _rex_scalar_type(expression.args[1], fields)
    return (
        left_type is not None
        and right_type is not None
        and compatible_calcite_type(left_type, right_type)
    )


def _nonnull_integer_contradiction(
    expression: RexExpr,
    fields: list[dict[str, Any]],
) -> tuple[int, tuple[int, int]] | None:
    if not (
        rex_operator(expression, "NOT", 1)
        and rex_operator(expression.args[0], "AND")
    ):
        return None
    leaves = rex_flatten(expression.args[0], "AND")
    if len(leaves) < 2 or not all(
        _direct_error_free_equality(leaf, fields) for leaf in leaves
    ):
        return None
    bindings = [
        binding
        for leaf in leaves
        if (binding := _integer_ref_literal_equality(leaf, fields)) is not None
    ]
    contradictions = {
        (left[0], *sorted((left[1], right[1])))
        for index, left in enumerate(bindings)
        for right in bindings[index + 1 :]
        if left[0] == right[0] and left[1] != right[1]
    }
    if len(contradictions) != 1:
        return None
    index, first, second = next(iter(contradictions))
    return index, (first, second)


def _remove_single_filter(
    relation: dict[str, Any],
    path: tuple[int, ...],
) -> dict[str, Any] | None:
    result = json.loads(json.dumps(relation))
    if not path:
        inputs = result.get("inputs")
        return inputs[0] if isinstance(inputs, list) and len(inputs) == 1 else None
    parent = result
    for index in path[:-1]:
        inputs = parent.get("inputs")
        if (
            not isinstance(inputs, list)
            or index >= len(inputs)
            or not isinstance(inputs[index], dict)
        ):
            return None
        parent = inputs[index]
    inputs = parent.get("inputs")
    target_index = path[-1]
    if (
        not isinstance(inputs, list)
        or target_index >= len(inputs)
        or not isinstance(inputs[target_index], dict)
    ):
        return None
    filter_node = inputs[target_index]
    filter_inputs = filter_node.get("inputs")
    if not isinstance(filter_inputs, list) or len(filter_inputs) != 1:
        return None
    inputs[target_index] = filter_inputs[0]
    return result


def preprocess_attested_nonnull_integer_contradiction_filter(
    relation: dict[str, Any],
    tables: list[Table],
    source_metadata: dict[str, Any],
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    """Erase one WHERE predicate proved TRUE by a NOT NULL contradiction.

    The admitted predicate is ``NOT`` of a conjunction containing two direct
    equalities from one fixed-width integer field to different integer literals.
    That field is independently bound to an authoritative source ``NOT NULL``
    constraint.  Every conjunct must be a direct, type-compatible equality, so
    evaluating or removing the predicate cannot expose or hide a runtime error.
    """

    site = _single_filter_site(relation)
    if site is None:
        return relation, []
    path, filter_node = site
    inputs = filter_node.get("inputs")
    if (
        not isinstance(inputs, list)
        or len(inputs) != 1
        or not isinstance(inputs[0], dict)
        or inputs[0].get("type") != "LogicalTableScan"
    ):
        return relation, []
    scan = inputs[0]
    table_path = scan.get("table")
    fields = validated_row_type(scan)
    condition = filter_node.get("condition")
    if (
        not isinstance(table_path, list)
        or len(table_path) != 1
        or not isinstance(table_path[0], str)
        or fields is None
        or not isinstance(condition, str)
    ):
        return relation, []
    table = find_table(tables, table_path[0])
    if table is None or len(table.columns) != len(fields):
        return relation, []
    if any(
        field["name"].casefold() != column.name.casefold()
        or not compatible_calcite_type(
            field["type"], calcite_schema_type_from_source(column.source_type)
        )
        for field, column in zip(fields, table.columns)
    ):
        return relation, []
    expression = parse_rex_digest(condition)
    contradiction = (
        _nonnull_integer_contradiction(expression, fields)
        if expression is not None
        else None
    )
    if contradiction is None:
        return relation, []
    field_index, literals = contradiction
    if field_index >= len(table.columns):
        return relation, []
    column = table.columns[field_index]
    if not _metadata_attests_not_null(
        source_metadata,
        table.name,
        column.name,
    ):
        return relation, []
    lowered = _remove_single_filter(relation, path)
    if lowered is None:
        return relation, []
    return lowered, [
        {
            "rule": "where-not-null-integer-contradiction-tautology",
            "kind": "semantic-preprocessing",
            "sideConditions": {
                "context": "one LogicalFilter directly over one TableScan",
                "sourceBoundExactCalciteTree": True,
                "authoritativeNotNullConstraint": {
                    "table": table.name,
                    "column": column.name,
                    "metadataPath": "sourceMetadata.constraints",
                },
                "fixedWidthIntegerType": fields[field_index]["type"],
                "distinctIntegerLiterals": list(literals),
                "allConjunctsDirectTypeCompatibleEqualities": True,
                "directComparisonsCannotRaise": True,
                "postgresBool3ConjunctionIsFalseForEverySourceRow": True,
                "postgresWhereConditionIsTrueForEverySourceRow": True,
                "noShortCircuitOrEvaluationOrderAssumption": True,
                "noJoinOrScalarOutputPredicateWasRewritten": True,
            },
        }
    ]


def _relation_with_filter_holes(relation: dict[str, Any]) -> dict[str, Any]:
    result = json.loads(json.dumps(relation))

    def visit(node: dict[str, Any]) -> None:
        if node.get("type") == "LogicalFilter":
            node["condition"] = "<paired-where-acceptance-hole>"
        for child in node.get("inputs", []) or []:
            if isinstance(child, dict):
                visit(child)

    visit(result)
    return result


def _source_rewrite_closure_evidence(
    original: dict[str, Any],
    remaining: dict[str, Any],
    rewrite_site: dict[str, str],
) -> dict[str, Any] | None:
    original_counts = _risky_rex_operator_counts(original)
    remaining_counts = _risky_rex_operator_counts(remaining)
    if original_counts == remaining_counts:
        return None
    return {
        "rule": "source-scalar-ir-rewrite-closure",
        "kind": "pair-safety",
        "sideConditions": {
            "originalRiskyOperatorCounts": original_counts,
            "remainingRiskyOperatorCounts": remaining_counts,
            "originalRiskyNodes": _risky_rex_inventory(original),
            "remainingRiskyNodes": _risky_rex_inventory(remaining),
            "closedRewriteSites": [rewrite_site],
            "sourceBoundExactCalciteTree": True,
            "unhandledOperatorsRemainCompilerVisible": True,
        },
    }


def preprocess_paired_where_true_acceptance(
    left: dict[str, Any],
    right: dict[str, Any],
) -> tuple[
    dict[str, Any],
    dict[str, Any],
    list[dict[str, Any]],
    list[dict[str, Any]],
]:
    """Close matched WHERE predicates modulo SQL Bool3 TRUE acceptance.

    This is intentionally a pair rule.  It never claims that FALSE and UNKNOWN
    are equal scalar values, and it never applies to JOIN conditions or SELECT
    outputs.  The complete relational trees must be byte-structurally equal
    after replacing exactly one corresponding filter condition with a hole.
    """

    left_site = _single_filter_site(left)
    right_site = _single_filter_site(right)
    if (
        left_site is None
        or right_site is None
        or left_site[0] != right_site[0]
        or _relation_with_filter_holes(left)
        != _relation_with_filter_holes(right)
    ):
        return left, right, [], []
    left_filter = left_site[1]
    right_filter = right_site[1]
    left_inputs = left_filter.get("inputs")
    right_inputs = right_filter.get("inputs")
    if (
        not isinstance(left_inputs, list)
        or len(left_inputs) != 1
        or not isinstance(left_inputs[0], dict)
        or not isinstance(right_inputs, list)
        or len(right_inputs) != 1
        or not isinstance(right_inputs[0], dict)
    ):
        return left, right, [], []
    left_fields = validated_row_type(left_inputs[0])
    right_fields = validated_row_type(right_inputs[0])
    left_condition = left_filter.get("condition")
    right_condition = right_filter.get("condition")
    if (
        left_fields is None
        or right_fields is None
        or left_fields != right_fields
        or not isinstance(left_condition, str)
        or not isinstance(right_condition, str)
    ):
        return left, right, [], []
    left_expression = parse_rex_digest(left_condition)
    right_expression = parse_rex_digest(right_condition)
    if left_expression is None or right_expression is None:
        return left, right, [], []
    canonical_left = _closed_nonnull_true_acceptance(
        left_expression, left_fields
    )
    canonical_right = _closed_nonnull_true_acceptance(
        right_expression, right_fields
    )
    if canonical_left is None or canonical_left != canonical_right:
        return left, right, [], []

    lowered_left = json.loads(json.dumps(left))
    lowered_right = json.loads(json.dumps(right))
    lowered_left_site = _single_filter_site(lowered_left)
    lowered_right_site = _single_filter_site(lowered_right)
    if lowered_left_site is None or lowered_right_site is None:
        return left, right, [], []
    lowered_left_site[1]["condition"] = "true"
    lowered_right_site[1]["condition"] = "true"
    dotted_path = "root" + "".join(
        f".inputs[{index}]" for index in left_site[0]
    ) + ".condition"
    pair_evidence = {
        "rule": "paired-where-bool3-true-acceptance-closure",
        "kind": "pair-safety",
        "sideConditions": {
            "context": "one corresponding LogicalFilter on each side",
            "leftOriginalCondition": left_condition,
            "rightOriginalCondition": right_condition,
            "canonicalTrueAcceptance": list(canonical_left),
            "completeTreesEqualAfterConditionHole": True,
            "postgresWhereRejectsFalseAndUnknown": True,
            "fixedWidthIntegerRefsAndNonNullLiteralsOnly": True,
            "directComparisonsCannotRaise": True,
            "cosetteDomainContainsNoNull": True,
            "canonicalConditionIsTrueOnEveryCosetteBinding": True,
            "noJoinOrScalarOutputPredicateWasRewritten": True,
        },
    }
    left_rewrite_site = {
        "path": dotted_path,
        "rule": pair_evidence["rule"],
        "beforeDigest": left_condition,
        "afterDigest": "true",
    }
    right_rewrite_site = {
        "path": dotted_path,
        "rule": pair_evidence["rule"],
        "beforeDigest": right_condition,
        "afterDigest": "true",
    }
    left_evidence = [pair_evidence]
    right_evidence = [pair_evidence]
    left_closure = _source_rewrite_closure_evidence(
        left, lowered_left, left_rewrite_site
    )
    right_closure = _source_rewrite_closure_evidence(
        right, lowered_right, right_rewrite_site
    )
    if left_closure is not None:
        left_evidence.append(left_closure)
    if right_closure is not None:
        right_evidence.append(right_closure)
    return lowered_left, lowered_right, left_evidence, right_evidence


def compile_cosette_candidate(
    rel: dict[str, Any],
    tables: list[Table],
    source_sql: str,
    ir_preprocessing: list[dict[str, Any]] | None = None,
) -> CompiledCosetteQuery | None:
    source_attestations = attest_source_scalar_normalization(
        source_sql,
        ir_preprocessing or [],
    )
    if source_attestations is None:
        return None
    special_compilers = (
        compile_union_all_candidate,
        compile_grouped_unused_left_join,
        compile_contradictory_intersect,
        compile_fetch_zero,
        compile_singleton_values_group,
    )
    for compiler in special_compilers:
        candidate = compiler(rel, tables, source_sql)
        if candidate is not None:
            return CompiledCosetteQuery(
                candidate.sql,
                source_attestations + candidate.attestations,
            )

    plan = compile_flat_rel(rel, tables, [0])
    if plan is None:
        return None
    sql = render_flat_plan(plan)
    if sql is None:
        return None
    nodes = sorted(collect_rel_node_types(rel))
    attestation = {
        "rule": "calcite-ir-relational-reserialization",
        "kind": "standard-syntax-lowering",
        "sideConditions": {
            "admittedRelNodes": nodes,
            "onlyClosedRexSurface": True,
            "orderedOutputTypesPreservedByPairGate": True,
            "orderingErased": False,
        },
    }
    return CompiledCosetteQuery(
        sql,
        [attestation] + source_attestations + plan.attestations,
        flat_plan=plan,
    )


def compile_union_all_candidate(
    rel: dict[str, Any],
    tables: list[Table],
    source_sql: str,
) -> CompiledCosetteQuery | None:
    """Reserialize a closed, error-free Project/TableScan UNION ALL tree.

    A Project above UNION ALL is distributed independently into each ordered
    branch.  This is exact for bag semantics, but only the deliberately small
    Project/inner-Join/TableScan fragment is admitted here: no DISTINCT set
    operation, filter, aggregate, ordering, VALUES, outer join, or nonconstant
    checked arithmetic is hidden by the bridge.  Although Cosette's parser
    accepts a branch-local WHERE, its public Rosette backend fails internally
    on that UNION shape (``rosSelectList``), so it is not advertised as a
    runnable compatibility lowering.
    """

    if attest_source_scalar_normalization(source_sql) is None:
        return None
    nodes = collect_rel_node_types(rel)
    if "LogicalUnion" not in nodes or not nodes <= {
        "LogicalUnion",
        "LogicalProject",
        "LogicalJoin",
        "LogicalTableScan",
    }:
        return None
    branches = compile_union_all_branches(rel, tables)
    root_row = validated_row_type(rel)
    if branches is None or len(branches) < 2 or root_row is None:
        return None
    rendered_branches: list[str] = []
    attestations: list[dict[str, Any]] = []
    for branch in branches:
        if (
            not plain_row_type_matches_fields(root_row, branch.fields)
            or any(
                item.get("kind") == "pair-safety-obligation"
                for item in branch.attestations
            )
        ):
            return None
        rendered = render_flat_plan(branch)
        if rendered is None:
            return None
        rendered_branches.append(rendered)
        attestations.extend(branch.attestations)
    return CompiledCosetteQuery(
        " UNION ALL ".join(rendered_branches),
        [
            {
                "rule": "calcite-ir-union-all-branch-reserialization",
                "kind": "standard-syntax-lowering",
                "sideConditions": {
                    "branchCount": len(branches),
                    "allSetOperatorsAreUnionAll": True,
                    "projectDistributedBranchWise": True,
                    "branchesContainOnlyProjectsInnerJoinsAndBaseScans": True,
                    "orderedOutputTypesPreserved": True,
                    "nonconstantCheckedArithmeticAbsent": True,
                    "branchOrderPreserved": True,
                    "duplicateEliminationIntroduced": False,
                },
            }
        ]
        + attestations,
    )


def plain_row_type_matches_fields(
    row_type: list[dict[str, Any]],
    fields: list[IrField],
) -> bool:
    """Require exact unmodified SQL types at a UNION branch boundary."""

    return len(row_type) == len(fields) and all(
        set(output) <= {"name", "type", "nullable"}
        and canonical_type(field.type_name) == canonical_type(output["type"])
        for field, output in zip(fields, row_type)
    )


def rebase_union_branch_aliases(
    plan: FlatCosettePlan,
    start: int,
) -> FlatCosettePlan | None:
    matches = [_FLAT_FROM_ITEM.fullmatch(item) for item in plan.from_items]
    if any(match is None for match in matches):
        return None
    present = [match for match in matches if match is not None]
    aliases = {
        match.group("alias"): f"t{start + index}"
        for index, match in enumerate(present)
    }
    return FlatCosettePlan(
        [
            f"{match.group('table')} AS {aliases[match.group('alias')]}"
            for match in present
        ],
        [_rename_flat_aliases(predicate, aliases) for predicate in plan.predicates],
        [
            IrField(
                _rename_flat_aliases(field.expression, aliases),
                field.type_name,
                field.nullable,
                field.constant,
            )
            for field in plan.fields
        ],
        group_by=(
            [_rename_flat_aliases(group, aliases) for group in plan.group_by]
            if plan.group_by is not None
            else None
        ),
        attestations=plan.attestations[:],
    )


def compile_union_all_branches(
    rel: dict[str, Any],
    tables: list[Table],
) -> list[FlatCosettePlan] | None:
    node_type = rel.get("type")
    inputs = rel.get("inputs")
    if not isinstance(node_type, str) or not isinstance(inputs, list):
        return None

    if node_type == "LogicalUnion":
        if (
            rel.get("all") is not True
            or rel.get("setOp") not in (None, "UNION")
            or len(inputs) < 2
        ):
            return None
        row_type = validated_row_type(rel)
        if row_type is None:
            return None
        branches: list[FlatCosettePlan] = []
        for child in inputs:
            if not isinstance(child, dict):
                return None
            child_branches = compile_union_all_branches(child, tables)
            if child_branches is None:
                return None
            for branch in child_branches:
                if not plain_row_type_matches_fields(row_type, branch.fields):
                    return None
            branches.extend(child_branches)
        return branches

    if (
        node_type == "LogicalJoin"
        and len(inputs) == 2
        and all(isinstance(child, dict) for child in inputs)
        and "LogicalUnion" in collect_rel_node_types(rel)
    ):
        left_input, right_input = inputs
        if str(rel.get("joinType") or "").upper() != "INNER":
            return None
        left_branches = compile_union_all_branches(left_input, tables)
        right_branches = compile_union_all_branches(right_input, tables)
        row_type = validated_row_type(rel)
        if left_branches is None or right_branches is None or row_type is None:
            return None
        joined: list[FlatCosettePlan] = []
        for left_branch in left_branches:
            for right_branch in right_branches:
                left = rebase_union_branch_aliases(left_branch, 0)
                if left is None:
                    return None
                left_occurrences = _flat_from_occurrences(left)
                if left_occurrences is None:
                    return None
                right = rebase_union_branch_aliases(
                    right_branch,
                    len(left_occurrences),
                )
                if right is None:
                    return None
                fields = left.fields + right.fields
                local_attestations: list[dict[str, Any]] = []
                conditions = render_rex_conjuncts(
                    rel.get("condition"),
                    fields,
                    local_attestations,
                )
                if conditions is None or not plain_row_type_matches_fields(
                    row_type, fields
                ):
                    return None
                predicates = left.predicates + right.predicates
                predicates.extend(
                    condition
                    for condition in conditions
                    if condition.lower() != "true"
                )
                joined.append(
                    FlatCosettePlan(
                        left.from_items + right.from_items,
                        predicates,
                        fields,
                        attestations=(
                            left.attestations
                            + right.attestations
                            + local_attestations
                        ),
                    )
                )
        return joined

    if node_type == "LogicalProject" and len(inputs) == 1 and isinstance(inputs[0], dict):
        child = inputs[0]
        if "LogicalUnion" in collect_rel_node_types(child):
            branches = compile_union_all_branches(child, tables)
            projects = rel.get("projects")
            row_type = validated_row_type(rel)
            if (
                branches is None
                or not isinstance(projects, list)
                or row_type is None
                or len(projects) != len(row_type)
            ):
                return None
            projected: list[FlatCosettePlan] = []
            for branch in branches:
                local_attestations: list[dict[str, Any]] = []
                fields: list[IrField] = []
                for digest, output in zip(projects, row_type):
                    field = render_rex_value(
                        digest,
                        branch.fields,
                        local_attestations,
                    )
                    if field is None or not compatible_calcite_type(
                        field.type_name, output["type"]
                    ):
                        return None
                    fields.append(
                        IrField(
                            field.expression,
                            output["type"],
                            output["nullable"],
                            field.constant,
                        )
                    )
                projected.append(
                    FlatCosettePlan(
                        branch.from_items[:],
                        branch.predicates[:],
                        fields,
                        group_by=(
                            branch.group_by[:]
                            if branch.group_by is not None
                            else None
                        ),
                        attestations=(
                            branch.attestations[:] + local_attestations
                        ),
                    )
                )
            return projected

    # A UNION branch is one independent SELECT scope.  Reset generated aliases
    # in every branch so equivalent branch-wise/project-distributed trees print
    # identically without relying on aliases from another SELECT scope.
    plan = compile_flat_rel(rel, tables, [0])
    return [plan] if plan is not None else None


def unprotected_constant_true_integer_case_matches(
    sql: str,
) -> list[re.Match[str]] | None:
    protected = protected_sql_regions(sql)
    if any(not region.terminated for region in protected):
        return None
    return [
        match
        for match in _CONSTANT_TRUE_INTEGER_CASE_PATTERN.finditer(sql)
        if not any(
            region.start <= match.start() < region.end
            for region in protected
        )
    ]


def attest_source_scalar_normalization(
    sql: str,
    ir_preprocessing: list[dict[str, Any]] | None = None,
) -> list[dict[str, Any]] | None:
    """Reject source-level scalar erasures unless their exact form is audited."""

    residual = list(sql)
    attestations: list[dict[str, Any]] = []
    constant_case_matches: list[re.Match[str]] = []
    closure = next(
        (
            item.get("sideConditions")
            for item in (ir_preprocessing or [])
            if item.get("rule") == "source-scalar-ir-rewrite-closure"
        ),
        None,
    )

    source_case_matches = unprotected_constant_true_integer_case_matches(sql)
    if source_case_matches is None:
        return None
    for match in source_case_matches:
        if match.group("left") != match.group("right"):
            return None
        constant_case_matches.append(match)

    residual_sql = "".join(residual)
    cast_spans = safe_integer_cast_spans(residual_sql)
    if cast_spans is None:
        return None
    for start, end, evidence in cast_spans:
        for index in range(start, end):
            residual[index] = " "
        attestations.append(evidence)

    scanned = mask_sql_regions("".join(residual))
    if re.search(
        r"\b(?:GROUPING\s+SETS|ROLLUP|CUBE)\b",
        scanned,
        flags=re.IGNORECASE,
    ):
        # The historical Calcite JSON profile exports only groupSet, not the
        # complete groupSets expansion. Reprinting it would silently collapse a
        # multi-set aggregate to one ordinary GROUP BY.
        return None
    if re.search(
        r"\b(?:FILTER\s*\(|WITHIN\s+GROUP\b)",
        scanned,
        flags=re.IGNORECASE,
    ) or re.search(
        r"\b(?:COUNT|SUM|MIN|MAX)\s*\(\s*DISTINCT\b",
        scanned,
        flags=re.IGNORECASE,
    ):
        return None
    has_case = re.search(r"\bCASE\b", scanned, flags=re.IGNORECASE) is not None
    has_null = re.search(r"\bNULL\b", scanned, flags=re.IGNORECASE) is not None
    has_boolean_literal = (
        re.search(r"\b(?:TRUE|FALSE)\b", scanned, flags=re.IGNORECASE) is not None
    )
    original_counts = (
        closure.get("originalRiskyOperatorCounts")
        if isinstance(closure, dict)
        else None
    )
    remaining_counts = (
        closure.get("remainingRiskyOperatorCounts")
        if isinstance(closure, dict)
        else None
    )
    original_nodes = closure.get("originalRiskyNodes") if isinstance(closure, dict) else None
    remaining_nodes = closure.get("remainingRiskyNodes") if isinstance(closure, dict) else None
    rewrite_sites = closure.get("closedRewriteSites") if isinstance(closure, dict) else None

    def source_feature_closed(feature: str, source_count: int) -> bool:
        if not (
            isinstance(original_nodes, list)
            and isinstance(remaining_nodes, list)
            and isinstance(rewrite_sites, list)
        ):
            return False
        feature_nodes = [
            item
            for item in original_nodes
            if isinstance(item, dict) and item.get("feature") == feature
        ]
        feature_remaining = [
            item
            for item in remaining_nodes
            if isinstance(item, dict) and item.get("feature") == feature
        ]
        every_node_has_closed_site = all(
            isinstance(node.get("path"), str)
            and any(
                isinstance(site, dict)
                and isinstance(site.get("path"), str)
                and isinstance(site.get("beforeDigest"), str)
                and isinstance(site.get("afterDigest"), str)
                and site["beforeDigest"] != site["afterDigest"]
                and node["path"].startswith(site["path"])
                for site in rewrite_sites
            )
            for node in feature_nodes
        )
        return (
            isinstance(original_counts, dict)
            and isinstance(remaining_counts, dict)
            and isinstance(original_counts.get(feature), int)
            and isinstance(remaining_counts.get(feature), int)
            and original_counts[feature] == source_count
            and remaining_counts[feature] == 0
            and len(feature_nodes) == original_counts[feature]
            and not feature_remaining
            and every_node_has_closed_site
            and closure.get("sourceBoundExactCalciteTree") is True
            and closure.get("unhandledOperatorsRemainCompilerVisible") is True
        )

    source_case_count = len(re.findall(r"\bCASE\b", scanned, flags=re.IGNORECASE))
    source_null_count = len(re.findall(r"\bNULL\b", scanned, flags=re.IGNORECASE))
    source_boolean_count = len(
        re.findall(r"\b(?:TRUE|FALSE)\b", scanned, flags=re.IGNORECASE)
    )
    # This is a source-to-IR occurrence closure, not a token-based waiver: all
    # source occurrences must be represented in the original exact Calcite IR,
    # and no corresponding risky operator may remain after preprocessing.
    if has_case and not source_feature_closed("case", source_case_count):
        return None
    if has_null and not source_feature_closed("null", source_null_count):
        return None
    if has_boolean_literal and not source_feature_closed(
        "booleanTestOrLiteral", source_boolean_count
    ):
        return None
    if constant_case_matches:
        if not isinstance(rewrite_sites, list):
            return None
        unused_sites = set(range(len(rewrite_sites)))
        closure_sha256 = sha256_text(
            json.dumps(closure, sort_keys=True, separators=(",", ":"))
        )
        for match in constant_case_matches:
            matched_index = next(
                (
                    index
                    for index in sorted(unused_sites)
                    if exact_constant_true_case_rex_rewrite(
                        match,
                        rewrite_sites[index],
                    )
                ),
                None,
            )
            if matched_index is None:
                return None
            unused_sites.remove(matched_index)
            site = rewrite_sites[matched_index]
            source_fragment = match.group(0)
            attestations.append(
                {
                    "rule": "constant-true-integer-case-selection",
                    "kind": "semantic-preprocessing",
                    "sideConditions": {
                        "literalPredicateOperands": [
                            match.group("left"),
                            match.group("right"),
                        ],
                        "predicateIsTrue": True,
                        "selectedIntegerBranch": match.group("then"),
                        "unselectedNullBranchNotEvaluated": True,
                        "exactSourceAndRexRewrite": True,
                        "sourceFragmentSha256": sha256_text(source_fragment),
                        "rexPath": site["path"],
                        "rexBeforeDigest": site["beforeDigest"],
                        "rexAfterDigest": site["afterDigest"],
                        "irRewriteClosureSha256": closure_sha256,
                    },
                }
            )
    if re.search(r"\bCAST\b", scanned, flags=re.IGNORECASE):
        return None
    if re.search(r"(?<![\w.])\d+\.\d+(?![\w.])", scanned):
        return None
    return attestations


def exact_constant_true_case_rex_rewrite(
    source_match: re.Match[str],
    rewrite_site: Any,
) -> bool:
    """Bind one audited source CASE occurrence to one exact Rex rewrite site."""

    if not (
        isinstance(rewrite_site, dict)
        and isinstance(rewrite_site.get("path"), str)
        and isinstance(rewrite_site.get("beforeDigest"), str)
        and isinstance(rewrite_site.get("afterDigest"), str)
    ):
        return False
    before = parse_rex_digest(rewrite_site["beforeDigest"])
    after = parse_rex_digest(rewrite_site["afterDigest"])
    if before is None or not rex_operator(before, "CASE", 3) or after is None:
        return False
    condition, selected, unselected = before.args
    if not rex_operator(condition, "=", 2) or not rex_is_null_literal(unselected):
        return False

    def source_literal_matches(source: str, expression: RexExpr) -> bool:
        if expression.kind != "literal":
            return False
        if source.startswith("'"):
            return expression.value == source
        try:
            return int(expression.value) == int(source)
        except ValueError:
            return False

    return (
        source_literal_matches(source_match.group("left"), condition.args[0])
        and source_literal_matches(source_match.group("right"), condition.args[1])
        and source_literal_matches(source_match.group("then"), selected)
        and rex_same(selected, after)
    )


def safe_integer_cast_spans(
    sql: str,
) -> list[tuple[int, int, dict[str, Any]]] | None:
    searchable = mask_sql_regions(sql)
    spans: list[tuple[int, int, dict[str, Any]]] = []
    for match in re.finditer(r"\bCAST\s*\(", searchable, flags=re.IGNORECASE):
        open_paren = searchable.find("(", match.start(), match.end())
        close_paren = find_matching_paren(sql, open_paren)
        if close_paren < 0:
            return None
        body = sql[open_paren + 1 : close_paren]
        as_position = find_top_level_keyword(body, "as")
        if as_position is None:
            return None
        expression = body[:as_position].strip()
        target = body[as_position + len("as") :].strip().upper()
        if target not in {"INT", "INTEGER"}:
            return None
        expression_mask = mask_sql_regions(expression)
        if (
            not expression
            or re.search(r"[^A-Za-z0-9_$().+*/\-\s]", expression_mask)
            or re.search(r"\b(?:NULL|TRUE|FALSE)\b", expression_mask, flags=re.IGNORECASE)
        ):
            return None
        spans.append(
            (
                match.start(),
                close_paren + 1,
                {
                    "rule": "source-integer-cast-bound-to-calcite-rex",
                    "kind": "semantic-preprocessing",
                    "sideConditions": {
                        "targetType": "INTEGER",
                        "sourceExpression": normalize_sql_layout(expression),
                        "calciteOutputTypeCheckedByCompiler": True,
                        "noStringDecimalBooleanOrNullOperand": True,
                    },
                },
            )
        )
    # A CAST token without a successfully parsed call must fail closed.
    if len(spans) != len(re.findall(r"\bCAST\s*\(", searchable, flags=re.IGNORECASE)):
        return None
    return spans


def collect_rel_node_types(rel: dict[str, Any]) -> set[str]:
    result: set[str] = set()

    def visit(node: Any) -> None:
        if not isinstance(node, dict):
            return
        node_type = node.get("type")
        if isinstance(node_type, str) and node_type.startswith("Logical"):
            result.add(node_type)
        inputs = node.get("inputs")
        if isinstance(inputs, list):
            for child in inputs:
                visit(child)

    visit(rel)
    return result


def compile_flat_rel(
    rel: dict[str, Any],
    tables: list[Table],
    alias_counter: list[int],
) -> FlatCosettePlan | None:
    node_type = rel.get("type")
    inputs = rel.get("inputs")
    if not isinstance(node_type, str) or not isinstance(inputs, list):
        return None

    if node_type == "LogicalTableScan":
        table_path = rel.get("table")
        row_type = validated_row_type(rel)
        if (
            not isinstance(table_path, list)
            or not table_path
            or row_type is None
        ):
            return None
        table_name = str(table_path[-1])
        table = find_table(tables, table_name)
        if table is None or len(table.columns) != len(row_type):
            return None
        alias = f"t{alias_counter[0]}"
        alias_counter[0] += 1
        fields: list[IrField] = []
        for source_column, calcite_column in zip(table.columns, row_type):
            if (
                source_column.name.lower() != calcite_column["name"].lower()
                or not compatible_calcite_type(
                    calcite_schema_type_from_source(source_column.source_type),
                    calcite_column["type"],
                )
            ):
                return None
            fields.append(
                IrField(
                    expression=f"{alias}.{source_column.name}",
                    type_name=calcite_column["type"],
                    nullable=calcite_column["nullable"],
                )
            )
        return FlatCosettePlan([f"{table.name} AS {alias}"], [], fields)

    if node_type == "LogicalJoin":
        if len(inputs) != 2 or str(rel.get("joinType") or "").upper() != "INNER":
            return None
        left = compile_flat_rel(inputs[0], tables, alias_counter)
        right = compile_flat_rel(inputs[1], tables, alias_counter)
        if (
            left is None
            or right is None
            or left.group_by is not None
            or right.group_by is not None
        ):
            return None
        fields = left.fields + right.fields
        local_attestations: list[dict[str, Any]] = []
        conditions = render_rex_conjuncts(
            rel.get("condition"), fields, local_attestations
        )
        if conditions is None:
            return None
        predicates = left.predicates + right.predicates
        predicates.extend(
            condition for condition in conditions if condition.lower() != "true"
        )
        if not row_types_match_fields(rel, fields):
            return None
        return FlatCosettePlan(
            left.from_items + right.from_items,
            predicates,
            fields,
            attestations=left.attestations + right.attestations + local_attestations,
        )

    if len(inputs) != 1 or not isinstance(inputs[0], dict):
        return None
    child = compile_flat_rel(inputs[0], tables, alias_counter)
    if child is None:
        return None

    if node_type == "LogicalFilter":
        if child.group_by is not None:
            return None
        local_attestations = []
        conditions = render_rex_conjuncts(
            rel.get("condition"), child.fields, local_attestations
        )
        if conditions is None:
            return None
        predicates = child.predicates[:]
        predicates.extend(
            condition for condition in conditions if condition.lower() != "true"
        )
        if not row_types_match_fields(rel, child.fields):
            return None
        child.predicates = predicates
        child.attestations.extend(local_attestations)
        return child

    if node_type == "LogicalProject":
        projects = rel.get("projects")
        row_type = validated_row_type(rel)
        if not isinstance(projects, list) or row_type is None or len(projects) != len(row_type):
            return None
        rendered: list[IrField] = []
        local_attestations: list[dict[str, Any]] = []
        for project, output in zip(projects, row_type):
            field_value = render_rex_value(project, child.fields, local_attestations)
            if field_value is None or not compatible_calcite_type(
                field_value.type_name, output["type"]
            ):
                return None
            rendered.append(
                IrField(
                    field_value.expression,
                    output["type"],
                    output["nullable"],
                    field_value.constant,
                )
            )
        child.fields = rendered
        child.attestations.extend(local_attestations)
        return child

    if node_type == "LogicalAggregate":
        if child.group_by is not None:
            return None
        group_sets = rel.get("groupSets")
        if group_sets is not None and group_sets != [rel.get("groupSet")]:
            return None
        group_indexes = parse_group_set(rel.get("groupSet"))
        agg_calls = rel.get("aggCalls")
        row_type = validated_row_type(rel)
        if group_indexes is None or not isinstance(agg_calls, list) or row_type is None:
            return None
        group_fields: list[IrField] = []
        retained_groups: list[str] = []
        dropped_constant_indexes: list[int] = []
        for index in group_indexes:
            if index >= len(child.fields):
                return None
            grouped = child.fields[index]
            group_fields.append(grouped)
            if grouped.constant:
                dropped_constant_indexes.append(index)
            else:
                retained_groups.append(grouped.expression)
        if dropped_constant_indexes and not retained_groups:
            # GROUP BY a constant is empty on empty input; a global aggregate is
            # not.  At least one nonconstant group must remain.
            return None
        aggregate_fields: list[IrField] = []
        aggregate_attestations: list[dict[str, Any]] = []
        for call in agg_calls:
            aggregate = render_aggregate_call(call, child.fields)
            if aggregate is None:
                return None
            aggregate_fields.append(aggregate)
        fields = group_fields + aggregate_fields
        if len(fields) != len(row_type):
            return None
        fields = [
            IrField(field_value.expression, output["type"], output["nullable"], field_value.constant)
            for field_value, output in zip(fields, row_type)
            if compatible_calcite_type(field_value.type_name, output["type"])
        ]
        if len(fields) != len(row_type):
            return None
        if dropped_constant_indexes:
            aggregate_attestations.append(
                {
                    "rule": "row-independent-group-key-elimination",
                    "kind": "semantic-preprocessing",
                    "sideConditions": {
                        "constantInputIndexes": dropped_constant_indexes,
                        "retainedNonconstantGroupKeys": retained_groups,
                        "nonemptyRetainedGroupSet": True,
                        "constantExpressionCannotRaise": True,
                    },
                }
            )
        child.fields = fields
        child.group_by = retained_groups
        child.attestations.extend(aggregate_attestations)
        return child
    return None


def validated_row_type(rel: dict[str, Any]) -> list[dict[str, Any]] | None:
    row_type = rel.get("rowType")
    if not isinstance(row_type, list):
        return None
    result: list[dict[str, Any]] = []
    for item in row_type:
        if (
            not isinstance(item, dict)
            or not isinstance(item.get("name"), str)
            or not isinstance(item.get("type"), str)
            or not isinstance(item.get("nullable"), bool)
        ):
            return None
        result.append(item)
    return result


def row_types_match_fields(rel: dict[str, Any], fields: list[IrField]) -> bool:
    row_type = validated_row_type(rel)
    return row_type is not None and len(row_type) == len(fields) and all(
        compatible_calcite_type(field_value.type_name, output["type"])
        for field_value, output in zip(fields, row_type)
    )


def canonical_type(type_name: str) -> str:
    normalized = re.sub(r"\s+", "", type_name).upper()
    if normalized in {"INT", "INTEGER"}:
        return "INTEGER"
    if normalized in {"BIGINT"}:
        return "BIGINT"
    if normalized.startswith("VARCHAR"):
        return normalized
    if normalized.startswith("CHAR"):
        return normalized
    return normalized


def compatible_calcite_type(actual: str, expected: str) -> bool:
    return canonical_type(actual) == canonical_type(expected)


def parse_group_set(value: Any) -> list[int] | None:
    if isinstance(value, list):
        return (
            list(value)
            if all(
                isinstance(index, int)
                and not isinstance(index, bool)
                and index >= 0
                for index in value
            )
            else None
        )
    if not isinstance(value, str):
        return None
    stripped = value.strip()
    if not stripped.startswith("{") or not stripped.endswith("}"):
        return None
    body = stripped[1:-1].strip()
    if not body:
        return []
    parts = [part.strip() for part in body.split(",")]
    return [int(part) for part in parts] if all(part.isdigit() for part in parts) else None


def render_rex_value(
    digest: Any,
    fields: list[IrField],
    attestations: list[dict[str, Any]],
) -> IrField | None:
    expression = parse_rex_digest(digest)
    return render_rex_expression(expression, fields, attestations) if expression else None


def render_rex_expression(
    expression: RexExpr,
    fields: list[IrField],
    attestations: list[dict[str, Any]],
) -> IrField | None:
    if expression.kind == "ref":
        index = int(expression.value)
        return fields[index] if index < len(fields) else None
    if expression.kind == "literal":
        type_name = expression.type_name
        if expression.value.startswith("'"):
            if type_name and canonical_type(type_name).startswith("DECIMAL"):
                return None
            return IrField(expression.value, type_name or "VARCHAR", False, True)
        if "." in expression.value:
            return None
        return IrField(expression.value, type_name or "INTEGER", False, True)
    if expression.kind == "atom":
        lowered = expression.value.lower()
        if lowered in {"true", "false"}:
            return IrField(lowered.upper(), "BOOLEAN", False, True)
        return None
    if expression.kind != "call":
        return None

    operator = expression.value.upper()
    rendered_args = [
        render_rex_expression(arg, fields, attestations) for arg in expression.args
    ]
    if any(arg is None for arg in rendered_args):
        return None
    args = [arg for arg in rendered_args if arg is not None]

    if operator == "CAST" and len(args) == 1 and expression.type_name:
        target = canonical_type(expression.type_name)
        source = canonical_type(args[0].type_name)
        if target != source or target not in {"INTEGER", "BIGINT"}:
            return None
        attestations.append(
            {
                "rule": "same-type-integer-cast-erasure",
                "kind": "semantic-preprocessing",
                "sideConditions": {
                    "sourceType": source,
                    "targetType": target,
                    "castIsValueAndErrorIdentity": True,
                },
            }
        )
        return args[0]

    if operator in {"+", "-", "*", "/"} and len(args) == 2:
        if not all(canonical_type(arg.type_name) in {"INTEGER", "BIGINT"} for arg in args):
            return None
        if args[0].constant and args[1].constant:
            folded = fold_integer_rex(operator, args[0], args[1])
            if folded is None:
                return None
            attestations.append(
                {
                    "rule": "checked-integer-literal-fold",
                    "kind": "semantic-preprocessing",
                    "sideConditions": {
                        "operator": operator,
                        "operands": [args[0].expression, args[1].expression],
                        "result": folded.expression,
                        "divisionExactAndNonzero": operator != "/" or True,
                        "resultWithinCalciteType": True,
                    },
                }
            )
            return folded
        if operator == "/":
            return None
        attestations.append(
            {
                "rule": "nonconstant-checked-integer-operation",
                "kind": "pair-safety-obligation",
                "sideConditions": {
                    "operator": operator,
                    "cosetteUsesUnboundedIntegers": True,
                    "requiresIdenticalLoweredPairForErrorClosure": True,
                },
            }
        )
        return IrField(
            f"({args[0].expression} {operator} {args[1].expression})",
            expression.type_name or args[0].type_name,
            args[0].nullable or args[1].nullable,
        )

    if operator in {"=", "<", ">"} and len(args) == 2:
        comparable = canonical_type(args[0].type_name)
        if (
            comparable != canonical_type(args[1].type_name)
            or not (
                comparable in {"INTEGER", "BIGINT"}
                or comparable.startswith("VARCHAR")
                or comparable.startswith("CHAR")
            )
        ):
            return None
        return IrField(
            f"({args[0].expression} {operator} {args[1].expression})",
            "BOOLEAN",
            args[0].nullable or args[1].nullable,
        )
    if operator in {"AND", "OR"} and len(args) == 2:
        if any(canonical_type(arg.type_name) != "BOOLEAN" for arg in args):
            return None
        return IrField(
            f"({args[0].expression} {operator} {args[1].expression})",
            "BOOLEAN",
            args[0].nullable or args[1].nullable,
        )
    if operator == "NOT" and len(args) == 1 and canonical_type(args[0].type_name) == "BOOLEAN":
        return IrField(f"NOT ({args[0].expression})", "BOOLEAN", args[0].nullable)
    return None


def fold_integer_rex(operator: str, left: IrField, right: IrField) -> IrField | None:
    try:
        left_value = int(left.expression)
        right_value = int(right.expression)
    except ValueError:
        return None
    if operator == "+":
        result = left_value + right_value
    elif operator == "-":
        result = left_value - right_value
    elif operator == "*":
        result = left_value * right_value
    elif right_value != 0 and left_value % right_value == 0:
        result = left_value // right_value
    else:
        return None
    target = canonical_type(left.type_name)
    lower, upper = (
        (-(2**31), 2**31 - 1) if target == "INTEGER" else (-(2**63), 2**63 - 1)
    )
    if not lower <= result <= upper:
        return None
    return IrField(str(result), target, False, True)


def render_rex_predicate(
    digest: Any,
    fields: list[IrField],
    attestations: list[dict[str, Any]],
) -> str | None:
    expression = parse_rex_digest(digest)
    if expression is None or not rex_predicate_is_admitted(expression):
        return None
    rendered = render_rex_expression(expression, fields, attestations)
    if rendered is None or canonical_type(rendered.type_name) != "BOOLEAN":
        return None
    return rendered.expression


def render_rex_conjuncts(
    digest: Any,
    fields: list[IrField],
    attestations: list[dict[str, Any]],
) -> list[str] | None:
    expression = parse_rex_digest(digest)
    if expression is None:
        return None
    pending = [expression]
    leaves: list[RexExpr] = []
    while pending:
        current = pending.pop(0)
        if current.kind == "call" and current.value.upper() == "AND" and len(current.args) == 2:
            pending[0:0] = list(current.args)
        else:
            leaves.append(current)
    result: list[str] = []
    for leaf in leaves:
        if not rex_predicate_is_admitted(leaf):
            return None
        rendered = render_rex_expression(leaf, fields, attestations)
        if rendered is None or canonical_type(rendered.type_name) != "BOOLEAN":
            return None
        result.append(rendered.expression)
    return result


def rex_predicate_is_admitted(expression: RexExpr) -> bool:
    if expression.kind == "atom":
        return expression.value.lower() in {"true", "false"}
    if expression.kind != "call":
        # In particular, a BOOLEAN input reference is not a predicate encoding:
        # Cosette declares the source column as int and has no attested 0/1
        # interpretation for PostgreSQL BOOLEAN/UNKNOWN.
        return False
    operator = expression.value.upper()
    if operator in {"=", "<", ">"}:
        return len(expression.args) == 2
    if operator in {"AND", "OR"}:
        return len(expression.args) == 2 and all(
            rex_predicate_is_admitted(argument) for argument in expression.args
        )
    if operator == "NOT":
        return len(expression.args) == 1 and rex_predicate_is_admitted(
            expression.args[0]
        )
    return False


def render_aggregate_call(digest: Any, fields: list[IrField]) -> IrField | None:
    expression = parse_rex_digest(digest)
    if expression is None or expression.kind != "call":
        return None
    operator = expression.value.upper()
    if operator.lower() not in COSETTE_SUPPORTED_AGGREGATES:
        return None
    # Calcite's aggregate digest serializes SQL COUNT(*) as COUNT(), while a
    # scalar Rex star (when present in older fixtures) is rendered below.
    if operator == "COUNT" and not expression.args:
        return IrField("COUNT(*)", "BIGINT", False)
    if len(expression.args) != 1:
        return None
    argument = expression.args[0]
    if argument.kind == "atom" and argument.value == "*" and operator == "COUNT":
        return IrField("COUNT(*)", "BIGINT", False)
    rendered = render_rex_expression(argument, fields, [])
    if rendered is None or not COSETTE_SIMPLE_COLUMN_PATH.fullmatch(rendered.expression):
        return None
    argument_type = canonical_type(rendered.type_name)
    if operator in {"SUM", "COUNT"} and argument_type not in {"INTEGER", "BIGINT"}:
        return None
    if operator in {"MAX", "MIN"} and not (
        argument_type in {"INTEGER", "BIGINT"}
        or argument_type.startswith("VARCHAR")
        or argument_type.startswith("CHAR")
    ):
        return None
    if operator == "COUNT":
        result_type = "BIGINT"
    elif operator == "SUM":
        # PostgreSQL widens SUM(INTEGER) to BIGINT and SUM(BIGINT) to NUMERIC.
        # The latter is outside Cosette's exact integer type surface and must
        # remain rejected rather than being silently rendered as BIGINT.
        if argument_type != "INTEGER":
            return None
        result_type = "BIGINT"
    else:
        result_type = rendered.type_name
    return IrField(f"{operator}({rendered.expression})", result_type, True)


def render_flat_plan(plan: FlatCosettePlan) -> str | None:
    if not plan.from_items or not plan.fields:
        return None
    select_items = [
        f"{field_value.expression} AS c{index}"
        for index, field_value in enumerate(plan.fields)
    ]
    sql = f"SELECT {', '.join(select_items)} FROM {', '.join(plan.from_items)}"
    if plan.predicates:
        sql += " WHERE " + " AND ".join(plan.predicates)
    if plan.group_by:
        sql += " GROUP BY " + ", ".join(plan.group_by)
    return sql


def compile_grouped_unused_left_join(
    rel: dict[str, Any],
    tables: list[Table],
    source_sql: str,
) -> CompiledCosetteQuery | None:
    if attest_source_scalar_normalization(source_sql) is None:
        return None
    if rel.get("type") != "LogicalAggregate" or rel.get("aggCalls") != []:
        return None
    group_indexes = parse_group_set(rel.get("groupSet"))
    inputs = rel.get("inputs")
    if group_indexes is None or not isinstance(inputs, list) or len(inputs) != 1:
        return None
    project = inputs[0]
    if not isinstance(project, dict) or project.get("type") != "LogicalProject":
        return None
    projects = project.get("projects")
    project_inputs = project.get("inputs")
    if (
        not isinstance(projects, list)
        or group_indexes != list(range(len(projects)))
        or not isinstance(project_inputs, list)
        or len(project_inputs) != 1
    ):
        return None
    references: list[int] = []
    for digest in projects:
        expression = parse_rex_digest(digest)
        if expression is None or expression.kind != "ref":
            return None
        references.append(int(expression.value))

    join_root = project_inputs[0]
    chain = inspect_safe_left_join_chain(join_root)
    if chain is None:
        return None
    leftmost, conditions, removed_join_count = chain
    left_plan = compile_flat_rel(leftmost, tables, [0])
    if left_plan is None or left_plan.group_by is not None:
        return None
    if any(index >= len(left_plan.fields) for index in references):
        return None
    output_row = validated_row_type(rel)
    if output_row is None or len(output_row) != len(references):
        return None
    selected: list[IrField] = []
    for index, output in zip(references, output_row):
        source = left_plan.fields[index]
        if not compatible_calcite_type(source.type_name, output["type"]):
            return None
        selected.append(
            IrField(source.expression, output["type"], output["nullable"])
        )
    left_plan.fields = selected
    left_plan.group_by = [field_value.expression for field_value in selected]
    sql = render_flat_plan(left_plan)
    if sql is None:
        return None
    return CompiledCosetteQuery(
        sql,
        [
            {
                "rule": "grouped-unobserved-left-join-elimination",
                "kind": "semantic-preprocessing",
                "sideConditions": {
                    "removedLeftJoinCount": removed_join_count,
                    "joinPredicates": conditions,
                    "joinPredicatesAreFieldEqualities": True,
                    "projectionUsesOnlyPreservedLeftInput": True,
                    "groupSetCoversEntireProjection": True,
                    "duplicateSensitivityEliminatedByGroup": True,
                    "rightInputsContainOnlyBaseScans": True,
                    "emptyLeftInputProducesNoGroupsOnBothSides": True,
                },
            }
        ],
    )


def inspect_safe_left_join_chain(
    node: Any,
) -> tuple[dict[str, Any], list[str], int] | None:
    if not isinstance(node, dict) or node.get("type") != "LogicalJoin":
        return None
    conditions: list[str] = []
    removed = 0
    current = node
    while current.get("type") == "LogicalJoin":
        if str(current.get("joinType") or "").upper() != "LEFT":
            return None
        inputs = current.get("inputs")
        if not isinstance(inputs, list) or len(inputs) != 2:
            return None
        left, right = inputs
        if not isinstance(left, dict) or not is_plain_table_scan(right):
            return None
        combined_row = validated_row_type(current)
        if combined_row is None:
            return None
        dummy_fields = [
            IrField(f"c{index}", item["type"], item["nullable"])
            for index, item in enumerate(combined_row)
        ]
        condition = parse_rex_digest(current.get("condition"))
        if not is_safe_field_equality(condition, dummy_fields):
            return None
        conditions.append(str(current.get("condition")))
        removed += 1
        current = left
    if not is_plain_table_scan(current):
        return None
    return current, list(reversed(conditions)), removed


def is_plain_table_scan(node: Any) -> bool:
    return (
        isinstance(node, dict)
        and node.get("type") == "LogicalTableScan"
        and node.get("inputs") == []
    )


def is_safe_field_equality(
    expression: RexExpr | None,
    fields: list[IrField],
) -> bool:
    if expression is None or expression.kind != "call" or expression.value != "=":
        return False
    if len(expression.args) != 2 or any(arg.kind != "ref" for arg in expression.args):
        return False
    indexes = [int(arg.value) for arg in expression.args]
    return all(index < len(fields) for index in indexes) and compatible_calcite_type(
        fields[indexes[0]].type_name,
        fields[indexes[1]].type_name,
    )


def compile_contradictory_intersect(
    rel: dict[str, Any],
    tables: list[Table],
    source_sql: str,
) -> CompiledCosetteQuery | None:
    if attest_source_scalar_normalization(source_sql) is None:
        return None
    if rel.get("type") != "LogicalIntersect":
        return None
    leaves = flatten_intersect_leaves(rel)
    if leaves is None or len(leaves) < 2:
        return None
    atoms = [extract_filtered_scan_atom(leaf) for leaf in leaves]
    if any(atom is None for atom in atoms):
        return None
    typed_atoms = [atom for atom in atoms if atom is not None]
    first_table, first_index, _first_value, first_scan = typed_atoms[0]
    if any(
        table_name.lower() != first_table.lower() or field_index != first_index
        for table_name, field_index, _value, _scan in typed_atoms
    ):
        return None
    values = {value for _table, _index, value, _scan in typed_atoms}
    if len(values) < 2:
        return None
    scan_plan = compile_flat_rel(first_scan, tables, [0])
    output_row = validated_row_type(rel)
    if (
        scan_plan is None
        or output_row is None
        or len(scan_plan.fields) != len(output_row)
        or not all(
            compatible_calcite_type(field_value.type_name, output["type"])
            for field_value, output in zip(scan_plan.fields, output_row)
        )
    ):
        return None
    scan_plan.fields = [
        IrField(field_value.expression, output["type"], output["nullable"])
        for field_value, output in zip(scan_plan.fields, output_row)
    ]
    scan_plan.predicates.append("(1 = 0)")
    sql = render_flat_plan(scan_plan)
    if sql is None:
        return None
    return CompiledCosetteQuery(
        sql,
        [
            {
                "rule": "contradictory-equality-intersect-to-typed-empty",
                "kind": "semantic-preprocessing",
                "sideConditions": {
                    "setOperator": "INTERSECT DISTINCT",
                    "sameBaseTable": first_table,
                    "sameFilteredFieldIndex": first_index,
                    "distinctEqualityLiterals": sorted(values),
                    "leafProjectionIsIdentity": True,
                    "predicateEvaluationCannotRaise": True,
                    "outputSignatureTakenFromCalciteRoot": True,
                    "resultIsEmptyForEveryInputIncludingEmptyInput": True,
                },
            }
        ],
    )


def flatten_intersect_leaves(rel: dict[str, Any]) -> list[dict[str, Any]] | None:
    if rel.get("type") != "LogicalIntersect" or rel.get("all") is not False:
        return [rel]
    inputs = rel.get("inputs")
    if not isinstance(inputs, list) or len(inputs) != 2:
        return None
    result: list[dict[str, Any]] = []
    for child in inputs:
        if not isinstance(child, dict):
            return None
        unwrapped = unwrap_identity_project(child)
        nested = flatten_intersect_leaves(unwrapped)
        if nested is None:
            return None
        result.extend(nested)
    return result


def unwrap_identity_project(node: dict[str, Any]) -> dict[str, Any]:
    current = node
    while current.get("type") == "LogicalProject":
        inputs = current.get("inputs")
        projects = current.get("projects")
        if not isinstance(inputs, list) or len(inputs) != 1 or not isinstance(projects, list):
            break
        if projects != [f"${index}" for index in range(len(projects))]:
            break
        child = inputs[0]
        if not isinstance(child, dict):
            break
        current = child
    return current


def extract_filtered_scan_atom(
    leaf: dict[str, Any],
) -> tuple[str, int, int, dict[str, Any]] | None:
    leaf = unwrap_identity_project(leaf)
    if leaf.get("type") != "LogicalFilter":
        return None
    inputs = leaf.get("inputs")
    if not isinstance(inputs, list) or len(inputs) != 1 or not is_plain_table_scan(inputs[0]):
        return None
    scan = inputs[0]
    expression = parse_rex_digest(leaf.get("condition"))
    if expression is None or expression.kind != "call" or expression.value != "=":
        return None
    if len(expression.args) != 2:
        return None
    reference = next((arg for arg in expression.args if arg.kind == "ref"), None)
    literal = next((arg for arg in expression.args if arg.kind == "literal"), None)
    if reference is None or literal is None or reference is literal:
        return None
    if re.fullmatch(r"0|-?[1-9]\d*", literal.value) is None:
        return None
    table_path = scan.get("table")
    row_type = validated_row_type(scan)
    index = int(reference.value)
    if (
        not isinstance(table_path, list)
        or not table_path
        or row_type is None
        or index >= len(row_type)
    ):
        return None
    field_type = canonical_type(row_type[index]["type"])
    if field_type not in {"INTEGER", "BIGINT"}:
        return None
    value = int(literal.value)
    lower, upper = (
        (-(2**31), 2**31 - 1)
        if field_type == "INTEGER"
        else (-(2**63), 2**63 - 1)
    )
    if not lower <= value <= upper:
        return None
    return str(table_path[-1]), index, value, scan


def compile_fetch_zero(
    rel: dict[str, Any],
    tables: list[Table],
    source_sql: str,
) -> CompiledCosetteQuery | None:
    if attest_source_scalar_normalization(source_sql) is None:
        return None
    if rel.get("type") != "LogicalSort" or str(rel.get("fetch")) != "0":
        return None
    if rel.get("offset") not in (None, "0") or not fetch_zero_subtree_is_error_free(rel):
        return None
    output_row = validated_row_type(rel)
    if output_row is None:
        return None
    typed_empty = typed_empty_plan_for_signature(output_row, tables)
    if typed_empty is None:
        return None
    sql = render_flat_plan(typed_empty)
    if sql is None:
        return None
    return CompiledCosetteQuery(
        sql,
        [
            {
                "rule": "error-free-fetch-zero-to-typed-empty",
                "kind": "semantic-preprocessing",
                "sideConditions": {
                    "fetchCount": 0,
                    "offset": rel.get("offset"),
                    "subtreeNodes": sorted(collect_rel_node_types(rel)),
                    "subtreeContainsOnlyScansDirectProjectsUnionAllAndSorts": True,
                    "sortKeysAreDirectFieldIndexes": True,
                    "subtreeEvaluationCannotRaise": True,
                    "outputSignatureTakenFromCalciteRoot": True,
                    "resultEmptyRegardlessOfInputCardinality": True,
                },
            }
        ],
    )


def fetch_zero_subtree_is_error_free(node: Any) -> bool:
    if not isinstance(node, dict):
        return False
    node_type = node.get("type")
    inputs = node.get("inputs")
    if not isinstance(inputs, list):
        return False
    if node_type == "LogicalTableScan":
        return inputs == []
    if node_type == "LogicalProject":
        projects = node.get("projects")
        if not isinstance(projects, list) or any(
            (expr := parse_rex_digest(project)) is None or expr.kind != "ref"
            for project in projects
        ):
            return False
    elif node_type == "LogicalUnion":
        if node.get("all") is not True:
            return False
    elif node_type == "LogicalSort":
        collation = node.get("collation")
        row_type = validated_row_type(node)
        fetch = node.get("fetch")
        offset = node.get("offset")
        if not isinstance(collation, list) or row_type is None:
            return False
        if any(
            value is not None
            and (
                not isinstance(value, str)
                or re.fullmatch(r"0|[1-9]\d*", value) is None
            )
            for value in (fetch, offset)
        ):
            return False
        if any(
            not isinstance(key, dict)
            or not isinstance(key.get("fieldIndex"), int)
            or key["fieldIndex"] >= len(row_type)
            for key in collation
        ):
            return False
    else:
        return False
    return all(fetch_zero_subtree_is_error_free(child) for child in inputs)


def typed_empty_plan_for_signature(
    output_row: list[dict[str, Any]],
    tables: list[Table],
) -> FlatCosettePlan | None:
    for table in tables:
        chosen: list[Column] = []
        used: set[int] = set()
        for output in output_row:
            match = next(
                (
                    (index, column)
                    for index, column in enumerate(table.columns)
                    if index not in used
                    and column.name.lower() == output["name"].lower()
                    and compatible_calcite_type(
                        calcite_schema_type_from_source(column.source_type),
                        output["type"],
                    )
                ),
                None,
            )
            if match is None:
                break
            index, column = match
            used.add(index)
            chosen.append(column)
        if len(chosen) != len(output_row):
            continue
        alias = "t0"
        fields = [
            IrField(f"{alias}.{column.name}", output["type"], output["nullable"])
            for column, output in zip(chosen, output_row)
        ]
        return FlatCosettePlan(
            [f"{table.name} AS {alias}"],
            ["(1 = 0)"],
            fields,
        )
    return None


def calcite_type_from_source(source_type: str) -> str:
    lowered = source_type.strip().lower()
    base = re.split(r"\s|\(", lowered, maxsplit=1)[0]
    if base == "bigint":
        return "BIGINT"
    if base in {"smallint", "tinyint"}:
        return "SMALLINT"
    if base in {"int", "integer"}:
        return "INTEGER"
    if base in {"char", "varchar", "text", "string"}:
        return "VARCHAR"
    if base in {"decimal", "numeric"}:
        return "DECIMAL"
    if base in {"float", "real", "double"}:
        return "FLOAT"
    if base == "date":
        return "DATE"
    if base.startswith("timestamp"):
        return "TIMESTAMP"
    # The pinned Calcite schema adapter currently exposes bare SQL TIME as ANY.
    # This is an exact frontend binding fact, not a Cosette sort claim.
    if base == "time":
        return "ANY"
    if base in {"bool", "boolean"}:
        return "BOOLEAN"
    return base.upper()


def calcite_schema_type_from_source(source_type: str) -> str:
    """Map parser-facing DDL to the current typed Calcite schema category.

    This is deliberately separate from the older Cosette-oriented helper above:
    schema authority must distinguish CHAR from VARCHAR and TIME from the
    legacy adapter's generic ANY category before either is collapsed to a
    public Cosette scalar sort.
    """

    lowered = source_type.strip().lower()
    base = re.split(r"\s|\(", lowered, maxsplit=1)[0]
    if base == "bigint":
        return "BIGINT"
    if base in {"smallint", "tinyint"}:
        return "SMALLINT"
    if base in {"int", "integer"}:
        return "INTEGER"
    if base == "char":
        return "CHAR"
    if base in {"varchar", "text", "string"}:
        return "VARCHAR"
    if base in {"decimal", "numeric"}:
        return "DECIMAL"
    if base in {"float", "double"}:
        return "DOUBLE"
    if base == "real":
        return "REAL"
    if base == "date":
        return "DATE"
    if base == "time":
        return "TIME"
    if base.startswith("timestamp") or base in {"datetime"}:
        return "TIMESTAMP"
    if base in {"bool", "boolean"}:
        return "BOOLEAN"
    return base.upper()


def compile_singleton_values_group(
    rel: dict[str, Any],
    tables: list[Table],
    source_sql: str,
) -> CompiledCosetteQuery | None:
    if attest_source_scalar_normalization(source_sql) is None:
        return None
    parsed = parse_singleton_values_group_query(source_sql, tables)
    if parsed is None or not ir_has_exact_singleton_values_group_shape(rel):
        return None
    sql = render_singleton_values_group_ast(parsed, rel)
    if sql is None:
        return None
    return CompiledCosetteQuery(
        sql,
        [
            {
                "rule": "singleton-values-constant-group-key-elimination",
                "kind": "semantic-preprocessing",
                "sideConditions": {
                    "sourceAstShape": "one base relation cross one one-cell VALUES relation",
                    "singletonLiteral": parsed.literal,
                    "removedGroupKey": parsed.values_alias_column,
                    "valuesColumnAbsentFromProjectionAndAggregates": True,
                    "retainedNonconstantGroupKeys": parsed.retained_group,
                    "calcitePlanHasOneInnerTrueJoinAndOneValuesLeaf": True,
                    "emptyBaseInputProducesNoGroupsOnBothSides": True,
                },
            }
        ],
    )


def parse_singleton_values_group_query(
    sql: str,
    tables: list[Table],
) -> SingletonValuesGroupAst | None:
    select_position = find_top_level_keyword(sql, "select")
    from_position = find_top_level_keyword(sql, "from")
    group_position = find_top_level_keyword(sql, "group by")
    if select_position != 0 or from_position is None or group_position is None:
        return None
    if any(
        find_top_level_keyword(sql, keyword, from_position + 4) is not None
        for keyword in ("where", "having", "order by", "limit", "offset", "fetch", "union")
    ):
        return None
    select_sql = sql[len("select") : from_position].strip()
    from_items = split_top_level_commas(sql[from_position + len("from") : group_position])
    group_items = [
        item.strip() for item in split_top_level_commas(sql[group_position + len("group by") :])
    ]
    if len(from_items) != 2 or len(group_items) < 2:
        return None
    base_match = re.fullmatch(
        r"\s*(?P<table>[A-Za-z_][A-Za-z0-9_]*)(?:\s+(?:AS\s+)?(?P<alias>[A-Za-z_][A-Za-z0-9_]*))?\s*",
        from_items[0],
        flags=re.IGNORECASE,
    )
    values_match = re.fullmatch(
        r"\s*\(\s*VALUES\s*\(\s*(?P<literal>[+-]?\d+|'(?:''|[^'])*')\s*\)\s*\)\s+"
        r"(?:AS\s+)?(?P<alias>[A-Za-z_][A-Za-z0-9_]*)\s*"
        r"\(\s*(?P<column>[A-Za-z_][A-Za-z0-9_]*)\s*\)\s*",
        from_items[1],
        flags=re.IGNORECASE,
    )
    if base_match is None or values_match is None:
        return None
    table = find_table(tables, base_match.group("table"))
    if table is None:
        return None
    alias = base_match.group("alias") or table.name
    values_column = f"{values_match.group('alias')}.{values_match.group('column')}"
    normalized_values_column = normalize_identifier_path(values_column)
    values_column_name = values_match.group("column")
    select_items = split_top_level_commas(select_sql)
    if any(
        normalized_values_column in normalize_identifier_path(item)
        or references_unqualified_identifier(item, values_column_name)
        for item in select_items
    ):
        return None
    if any(
        references_unqualified_identifier(item, values_column_name)
        for item in group_items
    ):
        return None
    retained = [
        item for item in group_items if normalize_identifier_path(item) != normalized_values_column
    ]
    if len(retained) != len(group_items) - 1 or not retained:
        return None
    return SingletonValuesGroupAst(
        select_items=[item.strip() for item in select_items],
        table=table,
        base_alias=alias,
        retained_group=retained,
        values_alias_column=values_column,
        literal=values_match.group("literal"),
    )


def render_singleton_values_group_ast(
    parsed: SingletonValuesGroupAst,
    rel: dict[str, Any],
) -> str | None:
    output_row = validated_row_type(rel)
    if output_row is None or len(output_row) != len(parsed.select_items):
        return None
    rendered_select: list[str] = []
    for index, (item, output) in enumerate(zip(parsed.select_items, output_row)):
        rendered = render_simple_source_projection(item, parsed)
        if rendered is None or not compatible_calcite_type(rendered.type_name, output["type"]):
            return None
        rendered_select.append(f"{rendered.expression} AS c{index}")
    rendered_group: list[str] = []
    for item in parsed.retained_group:
        rendered = render_simple_source_column(item, parsed)
        if rendered is None:
            return None
        rendered_group.append(rendered.expression)
    return (
        f"SELECT {', '.join(rendered_select)} FROM {parsed.table.name} AS t0 "
        f"GROUP BY {', '.join(rendered_group)}"
    )


def render_simple_source_projection(
    item: str,
    parsed: SingletonValuesGroupAst,
) -> IrField | None:
    aggregate = re.fullmatch(
        r"(?P<name>SUM|COUNT|MAX|MIN)\s*\(\s*(?P<argument>[^()]+)\s*\)",
        item,
        flags=re.IGNORECASE,
    )
    if aggregate is not None:
        argument = render_simple_source_column(aggregate.group("argument"), parsed)
        if argument is None:
            return None
        name = aggregate.group("name").upper()
        result_type = "BIGINT" if name == "COUNT" else argument.type_name
        return IrField(f"{name}({argument.expression})", result_type, True)
    return render_simple_source_column(item, parsed)


def render_simple_source_column(
    item: str,
    parsed: SingletonValuesGroupAst,
) -> IrField | None:
    match = re.fullmatch(
        r"(?:(?P<qualifier>[A-Za-z_][A-Za-z0-9_]*)\s*\.\s*)?"
        r"(?P<column>[A-Za-z_][A-Za-z0-9_]*)",
        item.strip(),
    )
    if match is None:
        return None
    qualifier = match.group("qualifier")
    if qualifier and qualifier.lower() not in {
        parsed.table.name.lower(),
        parsed.base_alias.lower(),
    }:
        return None
    column = next(
        (
            column
            for column in parsed.table.columns
            if column.name.lower() == match.group("column").lower()
        ),
        None,
    )
    if column is None:
        return None
    return IrField(
        f"t0.{column.name}",
        calcite_type_from_source(column.source_type),
        True,
    )


def normalize_identifier_path(value: str) -> str:
    return re.sub(r"\s+", "", value).lower()


def references_unqualified_identifier(sql_fragment: str, identifier: str) -> bool:
    scanned = mask_sql_regions(sql_fragment)
    identifier_bytes = r"A-Za-z0-9_$\x80-\U0010ffff"
    return re.search(
        rf"(?<![{identifier_bytes}.]){re.escape(identifier)}(?![{identifier_bytes}])",
        scanned,
        flags=re.IGNORECASE,
    ) is not None


def ir_has_exact_singleton_values_group_shape(rel: dict[str, Any]) -> bool:
    nodes: list[dict[str, Any]] = []

    def visit(node: Any) -> None:
        if not isinstance(node, dict):
            return
        nodes.append(node)
        for child in node.get("inputs", []):
            visit(child)

    visit(rel)
    values = [node for node in nodes if node.get("type") == "LogicalValues"]
    joins = [node for node in nodes if node.get("type") == "LogicalJoin"]
    aggregates = [node for node in nodes if node.get("type") == "LogicalAggregate"]
    if len(values) != 1 or len(joins) != 1 or len(aggregates) != 1:
        return False
    values_row = validated_row_type(values[0])
    join = joins[0]
    group_set = parse_group_set(aggregates[0].get("groupSet"))
    if (
        values_row is None
        or len(values_row) != 1
        or values_row[0]["nullable"]
        or str(join.get("joinType") or "").upper() != "INNER"
        or str(join.get("condition") or "").lower() != "true"
        or group_set is None
        or len(group_set) < 2
    ):
        return False
    tuples = values[0].get("tuples")
    # New Calcite IR exports exact tuples.  Older generated fixtures omitted the
    # field; in that case the independently parsed source AST above is authority
    # for the one-cell cardinality and literal.
    return tuples is None or (
        isinstance(tuples, list)
        and len(tuples) == 1
        and isinstance(tuples[0], list)
        and len(tuples[0]) == 1
    )


def parse_tables(schema_sql: str) -> list[Table]:
    parsed = parse_schema(
        schema_sql,
        clean_identifier=clean_cosette_table_name,
        parse_table=parse_cosette_table,
    )
    return [table for table in parsed if table is not None]


def find_table(tables: list[Table], name: str) -> Table | None:
    return next(
        (table for table in tables if table.name.lower() == name.lower()),
        None,
    )


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
    noninteger_int_columns: set[tuple[str, str, str]] = set()
    for table in tables:
        for column in table.columns:
            lowered = column.source_type.lower()
            if any(marker in lowered for marker in ("decimal", "numeric", "real", "float", "double")):
                decimal_columns.add((table.name.lower(), column.name.lower()))
            if any(marker in lowered for marker in ("date", "time", "bool")):
                noninteger_int_columns.add(
                    (table.name.lower(), column.name.lower(), column.source_type)
                )
    scanned = mask_sql_regions(f"{sql1}\n{sql2}").lower()
    for table, column in sorted(decimal_columns):
        if references_column(scanned, table, column):
            return [
                "This case references DECIMAL/FLOAT schema columns, but Cosette's public DSL materialization lowers them to int rather than preserving SQL numeric semantics."
            ]
    wildcard_projection = re.search(
        r"\bselect\s+(?:distinct\s+)?(?:[a-z_][a-z0-9_$]*\s*\.\s*)?\*",
        scanned,
        flags=re.IGNORECASE,
    ) is not None
    referenced_noninteger = sorted(
        {
            source_type
            for table, column, source_type in noninteger_int_columns
            if wildcard_projection or references_column(scanned, table, column)
        }
    )
    if referenced_noninteger:
        return [
            "This case observes DATE/TIME/BOOLEAN schema values that Cosette's public DSL represents with its generic int sort; exact PostgreSQL scalar semantics remain a pair-level obligation. Source types: "
            + ", ".join(referenced_noninteger)
            + "."
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
