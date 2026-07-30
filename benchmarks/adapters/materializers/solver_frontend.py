"""Solver-specific SQL materialization boundaries.

Calcite ingestion and external solvers are separate frontend boundaries.  A
benchmark's ingestion ``adapter`` therefore says nothing about whether a
solver-facing representation is safe.  This module implements explicit,
target-named policies and returns an auditable report for every transformation.

The SQLSolver policy is intentionally narrow.  In PostgreSQL, a quoted ASCII
lowercase identifier such as ``"lineitem"`` and the unquoted token
``lineitem`` denote the same identifier because unquoted identifiers fold to
lowercase.  Delimiter elision is consequently role-independent: it preserves
base names, qualifications, aliases, correlated bindings, output labels, and
ORDER BY alias references without rebuilding query scope.  Keywords and every
identifier whose spelling would change under folding are retained verbatim.
Since SQLSolver rewrites remaining double quotes as string quotes, any such
residual makes the solver representation unsupported rather than approximate.
"""

from __future__ import annotations

import hashlib
import re
from collections import Counter
from typing import Any

from materializer_sql import normalize_sql_layout, protected_sql_regions


SQLSOLVER_POSTGRES_IDENTIFIER_POLICY = (
    "postgres-simple-lowercase-identifier-delimiter-elision-v1"
)
SQLSOLVER_PREFLIGHT_POLICY = "sqlsolver-parser-validator-planner-v1"

# Conservative union of PostgreSQL/SQL-standard query keywords and tokens that
# SQLSolver's Calcite/MySQL-facing pipeline treats as reserved.  False positives
# only reduce coverage: a quoted spelling is retained and the case fails closed.
# False negatives would be unsound, so this intentionally includes non-reserved
# words accepted as identifiers by some source dialects.
SQLSOLVER_UNQUOTING_KEYWORDS = frozenset(
    """
    all analyse analyze and any array as asc asymmetric authorization between
    bigint binary both by case cast char character check coalesce collate column
    collation concurrently constraint count create cross current current_catalog current_date
    current_role current_schema current_time current_timestamp current_user data
    date dec decimal default deferrable desc distinct do else end except exists
    external extract false fetch filter float for foreign freeze from full grant greatest
    group grouping groups having ilike in index initially inner inout int integer
    intersect interval into is isnull join key keys last_value lateral leading left like
    limit localtime localtimestamp max method min natural nchar new none not notnull null
    nullif numeric offset old on only or order outer overlaps overlay percent_rank
    placing position precision primary range rank read reads real recursive ref
    references regexp returning right rollup row scope select session_user setof
    similar smallint some substring sum symmetric system system_user table tablesample then
    time timestamp to trailing treat trigger trim true union unique unknown unnest
    usage user using value values varchar variadic verbose when where window with
    within without bit boolean json json_array json_arrayagg json_exists json_object
    json_objectagg json_query json_scalar json_serialize json_table json_value least
    merge_action national normalize out xmlattributes xmlconcat xmlelement xmlexists
    xmlforest xmlnamespaces xmlparse xmlpi xmlroot xmlserialize xmltable
    """.split()
)

_LOWERCASE_IDENTIFIER = re.compile(r"[a-z_][a-z0-9_]*\Z", flags=re.ASCII)


class SolverFrontendConfigurationError(ValueError):
    """An explicit solver materialization policy is malformed or unknown."""


def solver_materialization_config(
    benchmark: dict[str, Any], target: str
) -> dict[str, Any] | None:
    """Return one explicit target policy without consulting ingestion adapter.

    Absence preserves the historical materialization byte-for-byte.  This makes
    policy rollout explicit and prevents a frontend repair for one corpus from
    silently rewriting unrelated generated benchmarks.
    """

    profiles = benchmark.get("solverMaterialization")
    if profiles is None:
        return None
    if not isinstance(profiles, dict):
        raise SolverFrontendConfigurationError(
            "solverMaterialization must be an object keyed by target"
        )
    profile = profiles.get(target)
    if profile is None:
        return None
    if not isinstance(profile, dict):
        raise SolverFrontendConfigurationError(
            f"solverMaterialization.{target} must be an object"
        )
    return profile


def materialize_sqlsolver_query(
    sql: str,
    *,
    read_dialect: str,
    policy: str,
) -> tuple[str, dict[str, Any]]:
    """Apply the closed SQLSolver query policy and return one-line SQL/report.

    Unsupported quoted identifiers are never renamed, deleted, case-folded, or
    converted into strings.  The returned SQL remains useful for target
    diagnostics, while ``semanticPreservation.established`` is the authoritative
    admission gate for solver execution.
    """

    if policy != SQLSOLVER_POSTGRES_IDENTIFIER_POLICY:
        raise SolverFrontendConfigurationError(
            f"unknown SQLSolver query policy: {policy!r}"
        )

    normalized_dialect = read_dialect.casefold().replace("_", "-")
    dialect_supported = normalized_dialect in {"postgres", "postgresql"}
    input_sha = _sha256(sql)
    transformed_counts: Counter[str] = Counter()
    residual_counts: Counter[tuple[str, str]] = Counter()
    pieces: list[str] = []
    cursor = 0

    for region in protected_sql_regions(sql):
        if region.kind != "double_quote":
            continue
        pieces.append(sql[cursor : region.start])
        original = sql[region.start : region.end]
        if not region.terminated:
            pieces.append(original)
            residual_counts[(original, "unterminated-double-quoted-region")] += 1
        else:
            identifier = original[1:-1].replace('""', '"')
            reason = _identifier_residual_reason(identifier, dialect_supported)
            if reason is None:
                pieces.append(identifier)
                transformed_counts[identifier] += 1
            else:
                pieces.append(original)
                residual_counts[(identifier, reason)] += 1
        cursor = region.end
    pieces.append(sql[cursor:])
    quote_lowered = "".join(pieces)
    one_line = normalize_sql_layout(quote_lowered, strip_trailing_semicolon=True) + "\n"

    transformations: list[dict[str, Any]] = []
    if transformed_counts:
        transformations.append(
            {
                "kind": "identifier-delimiter-elision",
                "rule": SQLSOLVER_POSTGRES_IDENTIFIER_POLICY,
                "occurrences": sum(transformed_counts.values()),
                "identifiers": [
                    {"identifier": name, "occurrences": transformed_counts[name]}
                    for name in sorted(transformed_counts)
                ],
                "contract": (
                    "For PostgreSQL input, remove delimiters only from complete "
                    "ASCII lowercase non-keyword identifiers. PostgreSQL's "
                    "unquoted folding therefore preserves the exact identifier "
                    "spelling in every syntactic role."
                ),
            }
        )
    if one_line != quote_lowered:
        transformations.append(
            {
                "kind": "protected-layout-normalization",
                "rule": "one-query-per-line-v1",
                "contract": (
                    "Remove comments, compact only unquoted SQL whitespace, and "
                    "remove one structural trailing semicolon; preserve all "
                    "bytes inside quoted and dollar-quoted regions."
                ),
                "inputSha256": _sha256(quote_lowered),
                "outputSha256": _sha256(one_line),
            }
        )

    residuals = [
        {"identifier": identifier, "reason": reason, "occurrences": count}
        for (identifier, reason), count in sorted(residual_counts.items())
    ]
    established = dialect_supported and not residuals
    report = {
        "target": "sqlsolver",
        "policy": policy,
        "readDialect": read_dialect,
        "inputSha256": input_sha,
        "outputSha256": _sha256(one_line),
        "status": (
            "semantics-preserving-normalization"
            if established
            else "unsupported-preservation-obligation"
        ),
        "transformations": transformations,
        "residualQuotedIdentifiers": residuals,
        "semanticPreservation": {
            "established": established,
            "identifierFolding": "postgres-unquoted-identifiers-fold-to-lowercase",
            "roleIndependent": True,
            "outputLabelsPreserved": True,
            "bindingSpellingPreserved": True,
            "unsupportedDisposition": (
                None
                if established
                else "Unsupport: retain residual quotes and do not submit to prover"
            ),
        },
    }
    return one_line, report


def pair_preservation_established(
    before_report: dict[str, Any], after_report: dict[str, Any]
) -> bool:
    """Whether both query sides satisfy their solver boundary contracts."""

    return all(
        report.get("semanticPreservation", {}).get("established") is True
        for report in (before_report, after_report)
    )


def _identifier_residual_reason(identifier: str, dialect_supported: bool) -> str | None:
    if not dialect_supported:
        return "dialect-has-no-attested-postgres-folding-contract"
    if _LOWERCASE_IDENTIFIER.fullmatch(identifier) is None:
        return "not-simple-ascii-lowercase-identifier"
    if identifier in SQLSOLVER_UNQUOTING_KEYWORDS:
        return "source-or-target-keyword"
    return None


def _sha256(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()
