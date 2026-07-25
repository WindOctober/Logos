#!/usr/bin/env python3
"""Generate the single indexed catalog for public Logos FormalSQL declarations.

The Rocq sources are authoritative.  This script extracts each complete public
``Lemma``, ``Theorem``, or ``Corollary`` sentence, assigns it to a semantic
domain at declaration granularity, and emits both the machine-readable
cross-index and focused Markdown documents.  ``--check`` fails when committed
catalog data has drifted.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
THEORIES = ROOT / "theories/FormalSQL"
CATALOG = THEORIES / "catalog"

DECLARATION = re.compile(
    r"(?m)^[ \t]*(Lemma|Theorem|Corollary)[ \t]+([A-Za-z_][A-Za-z0-9_']*)\b"
)
FORBIDDEN = re.compile(
    r"(?m)^[ \t]*(Axiom|Axioms|Parameter|Parameters|Conjecture|Admitted|admit)\b"
)
PROOF_TERMINATOR = re.compile(r"\b(Qed|Admitted|Defined|Abort)\.")
CASE_SPECIFIC_NAME = re.compile(
    r"(?:^|_)(?:q\d{2,}|calcite|wetune|tpcds|tpch|dsb|benchmark)(?:_|$)", re.I
)
CASE_SPECIFIC_STATEMENT = re.compile(
    r"(?:\b(?:calcite|wetune|tpc[-_]?ds|tpch|dsb|benchmark)[A-Za-z0-9_-]*\b"
    r"|\bq\d{2,}\b"
    r"|\b(?:source|target)_(?:query_expr|query_program|program)\b)",
    re.I,
)

# These are semantic cards plus the default source-module ownership needed to
# cover every authoritative theory exactly once.  Broad public modules are
# reassigned per declaration by ``declaration_domain`` below.  Agents search
# the cross-index and open only matching declarations, so coverage is not
# constrained by an arbitrary declaration-count ceiling.
DOMAINS: dict[str, dict[str, object]] = {
    "null-predicates.md": {
        "title": "NULL, Bool3, predicates, and CASE",
        "modules": ("TNullSyntax.v", "ScalarPredicateFacts.v"),
        "topics": ("null", "three-valued logic", "Bool3", "predicate", "CASE"),
        "route": "UNKNOWN/TRUE/FALSE, strict predicates, NULL tests, comparisons, CASE",
    },
    "query-syntax-bridges.md": {
        "title": "Query syntax and projection bridges",
        "modules": ("QueryTNullSyntax.v",),
        "topics": ("query syntax", "projection", "tuple", "TNull", "bridge"),
        "route": "query-level nullable syntax adapters, tuple projection, attribute lookup",
    },
    "numeric-primitives.md": {
        "title": "NUMERIC primitive semantics",
        "modules": ("NumericFacts.v",),
        "topics": ("numeric", "decimal", "typmod", "division", "AVG"),
        "route": "NUMERIC representation, precision/scale, division, rounding, AVG states",
    },
    "numeric-derived.md": {
        "title": "Derived numeric, integer, float, and cast facts",
        "modules": ("NumericDerivedFacts.v", "NumericRegroupFacts.v"),
        "topics": ("integer", "numeric", "float", "cast", "runtime safety"),
        "route": "INTEGER/BIGINT bounds, derived NUMERIC laws, floats, casts, overflow",
    },
    "bitwise.md": {
        "title": "Bitwise scalar and aggregate facts",
        "modules": ("BitwiseFacts.v",),
        "topics": ("bitwise", "integer", "aggregate", "shift"),
        "route": "integer bit operations, shifts, BIT_AND/BIT_OR aggregate laws",
    },
    "string-temporal.md": {
        "title": "String and temporal values",
        "modules": ("StringTemporalFacts.v",),
        "topics": ("string", "typmod", "collation", "date", "time", "timestamp"),
        "route": "CHAR/VARCHAR/TEXT, LIKE, substring, DATE/TIME/TIMESTAMP/TIMESTAMPTZ",
    },
    "relational-algebra.md": {
        "title": "Bags, occurrences, projection, and relational algebra",
        "modules": (
            "RelationalAlgebraFacts.v",
            "ProofAgentFacade.v",
        ),
        "topics": ("bag", "list", "occurrence", "projection", "join", "set operation"),
        "route": "bag/list abstraction, multiplicity, filter/project/join/set operators",
    },
    "ordered-observation.md": {
        "title": "Ordered observations and slicing",
        "modules": ("OrderedQueryFacts.v",),
        "topics": ("order by", "ordered observation", "offset", "fetch", "distinct"),
        "route": "exact order and multiplicity, ORDER BY, OFFSET/LIMIT/FETCH, DISTINCT",
    },
    "aggregate-grouping.md": {
        "title": "Aggregates, modifiers, grouping, and aggregate errors",
        "modules": (
            "AggregateRuntimeFacts.v",
            "GroupingRewriteFacts.v",
            "GroupedFilterOutcomeFacts.v",
        ),
        "topics": (
            "aggregate",
            "group by",
            "grouping sets",
            "distinct",
            "null",
            "runtime error",
        ),
        "route": "COUNT/SUM/MIN/MAX/AVG, ALL/DISTINCT, empty/all-NULL, grouping, and SINGLE_VALUE scalar-subquery cardinality",
    },
    "subquery-predicates.md": {
        "title": "Predicate subqueries and correlation",
        "modules": ("SubqueryFacts.v",),
        "topics": ("subquery", "EXISTS", "IN", "quantified predicate", "correlation"),
        "route": "EXISTS, IN, ANY/ALL-style quantified predicates, correlated query/formula goals; use aggregate/grouping for SINGLE_VALUE scalar cardinality",
    },
    "schema-integrity.md": {
        "title": "Schema conformance and integrity constraints",
        "modules": ("SchemaCardinality.v", "IntegrityFacts.v"),
        "topics": (
            "schema",
            "not null",
            "primary key",
            "unique",
            "foreign key",
            "check",
        ),
        "route": "typing/schema conformance, NOT NULL, PK/UNIQUE/FK/CHECK, unique indexes",
    },
    "cardinality-composition.md": {
        "title": "Query cardinality and compositional bounds",
        "modules": ("QueryCardinality.v", "CardinalityCombinators.v"),
        "topics": ("cardinality", "join", "filter", "group", "finite domain", "bound"),
        "route": "row-count bounds, functional joins, filters, groups, finite images",
    },
    "runtime-verification-rewrite.md": {
        "title": "Runtime outcomes, verification modes, and rewrite specifications",
        "modules": ("VerificationConditions.v",),
        "topics": (
            "runtime error",
            "outcome",
            "safe",
            "equivalence",
            "rewrite",
            "verification",
        ),
        "route": "success/error outcomes, safe vs error-preserving equivalence, rewrite contracts",
    },
}

# Routes are a deliberately small cross-index over the primary semantic cards.
# A declaration may occur in several routes, but its exact statement occurs in
# only one primary card.  This keeps bounded searches useful without copying
# large cards or introducing a second source of theorem statements.
ROUTES: dict[str, dict[str, str]] = {
    "facade": {
        "title": "high-level TNull proof facade",
        "description": "first-stop compositional wrappers over generated TNull query terms",
    },
    "outcome": {
        "title": "query outcome equivalence",
        "description": "error-preserving query-outcome bridges and congruences",
    },
    "grouping": {
        "title": "grouping and HAVING",
        "description": "group construction, grouped-key filters, and aggregate outcomes",
    },
    "runtime": {
        "title": "runtime safety and errors",
        "description": "runtime-error propagation, absence, success, and lifting",
    },
    "projection": {
        "title": "projection",
        "description": "row extensionality, project operators, and projection congruence",
    },
    "filter": {
        "title": "filters",
        "description": "WHERE/HAVING row filters and filter congruence",
    },
    "join": {
        "title": "joins",
        "description": "cross, inner, outer, semi, anti, and functional joins",
    },
    "bag": {
        "title": "bags and multiplicity",
        "description": "bag equality, occurrence, and list/bag transport",
    },
    "ordered": {
        "title": "ordered observations",
        "description": "ORDER BY, OFFSET/FETCH, windows, and order-sensitive equality",
    },
    "cardinality": {
        "title": "cardinality",
        "description": "row bounds, finite domains, and functional composition",
    },
    "schema": {
        "title": "schema and integrity",
        "description": "schema conformance, keys, and integrity facts",
    },
    "scalar": {
        "title": "scalar semantics",
        "description": "NULL/Bool3, numeric, string, temporal, and scalar subqueries",
    },
}

INDEX_PREVIEW_ROUTES = ("facade", "outcome", "grouping", "runtime")
INDEX_PREVIEW_PER_ROUTE = 5
MAX_INDEX_BYTES = 12 * 1024

# A domain anchor describes why the entry lives in its focused document without
# claiming every feature handled by that document.  Entry-specific aliases are
# added below from declaration-name tokens and exact FormalSQL constructors.
DOMAIN_ENTRY_TOPICS: dict[str, str] = {
    "null-predicates.md": "scalar predicate semantics",
    "query-syntax-bridges.md": "query syntax bridge",
    "numeric-primitives.md": "numeric semantics",
    "numeric-derived.md": "numeric and cast semantics",
    "bitwise.md": "bitwise semantics",
    "string-temporal.md": "string/temporal scalar semantics",
    "relational-algebra.md": "relational algebra",
    "ordered-observation.md": "ordered query semantics",
    "aggregate-grouping.md": "aggregate/grouping runtime semantics",
    "subquery-predicates.md": "predicate subquery semantics",
    "schema-integrity.md": "schema and integrity semantics",
    "cardinality-composition.md": "cardinality composition",
    "runtime-verification-rewrite.md": "verification and runtime semantics",
}

BAG_ALGEBRA_PREFIXES = (
    "query_bag_",
    "query_bags_",
    "query_set_union_",
    "query_distinct_",
    "query_duplicate_free_",
)

# These generic UNION composition laws state their bag premises through local
# definitions rather than a public ``bag_*`` identifier.  Keep their semantic
# route explicit so a harmless refactor of those definitions cannot make the
# retained duplicate-freedom interface disappear from bag navigation.
BAG_ALGEBRA_DECLARATIONS = {
    "query_expr_union_success_Forall",
    "query_set_union_disjoint_right",
    "query_set_union_duplicate_free",
}

QUERY_SYNTAX_DECLARATIONS = {
    "direct_projection_preserves_attr",
    "projection_preserves_attr",
    "select_list_directly_selects_attr",
    "select_list_has_unique_outputs",
}

GENERIC_OUTCOME_DECLARATIONS = {
    "outcome_equiv_eq_iff",
    "outcome_equiv_symmetric",
    "outcome_equiv_transitive",
    "successful_outcome_equiv_implies_outcome_equiv",
}

ROCQ_IDENTIFIER = re.compile(r"\b[A-Za-z_][A-Za-z0-9_']*\b")
CAMEL_BOUNDARY = re.compile(r"(?<=[a-z0-9])(?=[A-Z])")

# Order is intentional: high-value user-facing routes are retained before the
# compact alias cap.  These keys are semantic classifications, not substring
# matches over arbitrary binders or error constructors.
FEATURE_TOPIC_ALIASES: tuple[tuple[str, tuple[str, ...]], ...] = (
    (
        "scalar_subquery",
        (
            "scalar subquery",
            "SINGLE_VALUE",
            "scalar cardinality",
            "CardinalityViolation",
        ),
    ),
    ("scalar_subquery_bridge", ("scalar subquery",)),
    ("scalar_subquery_error_bridge", ("SINGLE_VALUE", "CardinalityViolation")),
    (
        "partial_functional_left_join",
        (
            "functional LEFT JOIN",
            "at-most-one match",
            "nullable unmatched key",
            "left multiplicity",
        ),
    ),
    (
        "outer_join",
        ("outer join", "LEFT OUTER JOIN", "RIGHT OUTER JOIN", "FULL OUTER JOIN"),
    ),
    ("semi_join", ("semi join", "EXISTS")),
    ("anti_join", ("anti join", "NOT EXISTS")),
    ("join", ("join",)),
    ("cross_join", ("cross product", "CROSS JOIN")),
    ("set_operation", ("set operation",)),
    ("set_union", ("UNION",)),
    ("set_intersection", ("INTERSECT",)),
    ("set_difference", ("EXCEPT",)),
    ("subquery", ("subquery",)),
    ("exists_predicate", ("EXISTS",)),
    ("in_predicate", ("IN",)),
    ("quantified_predicate", ("quantified predicate", "ANY/ALL")),
    ("correlation", ("correlated", "correlation")),
    ("grouping_sets", ("grouping sets",)),
    ("grouping", ("GROUP BY",)),
    ("aggregate", ("aggregate",)),
    ("distinct", ("DISTINCT", "duplicate elimination")),
    ("filter", ("filter", "WHERE")),
    ("projection", ("projection", "SELECT list")),
    ("row", ("row extensionality", "tuple equality")),
    ("order_by", ("ORDER BY", "ordered observation")),
    ("offset", ("OFFSET",)),
    ("fetch", ("FETCH", "LIMIT")),
    ("window", ("window", "PARTITION BY")),
    ("case", ("CASE", "conditional expression")),
    ("null", ("NULL", "UNKNOWN", "three-valued logic")),
    ("predicate", ("predicate", "Bool3")),
    ("numeric", ("NUMERIC", "DECIMAL")),
    ("typmod", ("typmod", "precision/scale")),
    ("int32", ("INTEGER", "int32")),
    ("int64", ("BIGINT", "int64")),
    ("float", ("floating point", "special value")),
    ("bitwise", ("bitwise",)),
    ("string", ("string", "VARCHAR")),
    ("collation", ("collation",)),
    ("temporal", ("temporal", "DATE", "TIME", "TIMESTAMP")),
    ("outcome", ("query outcome", "error-preserving outcome")),
    ("runtime", ("runtime outcome", "runtime safety", "error propagation")),
    ("schema", ("schema conformance", "typing")),
    ("integrity", ("integrity constraint", "key")),
    ("cardinality", ("cardinality",)),
    ("multiplicity", ("multiplicity",)),
    ("bag", ("bag semantics", "list/bag bridge")),
    ("non_equivalence", ("non-equivalence", "mismatch witness")),
    ("equivalence", ("equivalence", "congruence")),
)


def sentence_end(text: str, start: int) -> int:
    """Return the terminating Rocq sentence dot, respecting comments/strings."""
    comment_depth = 0
    in_string = False
    index = start
    while index < len(text):
        pair = text[index : index + 2]
        if comment_depth:
            if pair == "(*":
                comment_depth += 1
                index += 2
                continue
            if pair == "*)":
                comment_depth -= 1
                index += 2
                continue
            index += 1
            continue
        if in_string:
            if pair == '""':
                index += 2
                continue
            if text[index] == '"':
                in_string = False
            index += 1
            continue
        if pair == "(*":
            comment_depth = 1
            index += 2
            continue
        if text[index] == '"':
            in_string = True
            index += 1
            continue
        if text[index] == "." and (index + 1 == len(text) or text[index + 1].isspace()):
            return index
        index += 1
    raise ValueError("unterminated public Rocq declaration")


def extract_declarations(path: Path) -> list[dict[str, object]]:
    text = path.read_text(encoding="utf-8")
    forbidden = FORBIDDEN.search(text)
    if forbidden:
        line = text.count("\n", 0, forbidden.start()) + 1
        raise ValueError(f"{path.name}:{line}: forbidden trust-extending command")
    declarations: list[dict[str, object]] = []
    matches = list(DECLARATION.finditer(text))
    for position, match in enumerate(matches):
        start = match.start(1)
        end = sentence_end(text, match.end())
        next_start = (
            matches[position + 1].start(1) if position + 1 < len(matches) else len(text)
        )
        terminator = PROOF_TERMINATOR.search(text, end + 1, next_start)
        if terminator is None or terminator.group(1) != "Qed":
            line = text.count("\n", 0, start) + 1
            observed = terminator.group(1) if terminator else "no terminator"
            raise ValueError(
                f"{path.name}:{line}: public declaration {match.group(2)} ends with {observed}, not Qed"
            )
        statement = text[start : end + 1].rstrip()
        declarations.append(
            {
                "name": match.group(2),
                "kind": match.group(1),
                "source": path.relative_to(ROOT).as_posix(),
                "line": text.count("\n", 0, start) + 1,
                "statement": statement,
            }
        )
    return declarations


def identifier_tokens(identifier: str) -> frozenset[str]:
    """Split one Rocq identifier at semantic snake/camel boundaries."""
    tokens: set[str] = set()
    for snake_part in identifier.rstrip("'").split("_"):
        for part in CAMEL_BOUNDARY.split(snake_part):
            if part:
                tokens.add(part.casefold())
    return frozenset(tokens)


def semantic_features(
    domain_name: str, module: str, name: str, statement: str
) -> frozenset[str]:
    """Classify an entry without interpreting arbitrary binders as SQL syntax.

    Declaration names are tokenized, while the statement contributes only
    exact FormalSQL identifiers/constructors.  Thus a slice binder named
    ``count``, Rocq's ``exists`` tactic term, ``DataException``, and ``runtime``
    cannot accidentally advertise COUNT, EXISTS, EXCEPT, or TIME.
    """
    tokens = set(identifier_tokens(name))
    identifiers = set(ROCQ_IDENTIFIER.findall(statement))
    folded_identifiers = {identifier.casefold() for identifier in identifiers}
    normalized_name = name.casefold()
    features: set[str] = set()

    def has_identifier(*candidates: str) -> bool:
        return any(
            candidate.casefold() in folded_identifiers for candidate in candidates
        )

    def has_identifier_prefix(*prefixes: str) -> bool:
        folded_prefixes = tuple(prefix.casefold() for prefix in prefixes)
        return any(
            identifier.startswith(folded_prefixes) for identifier in folded_identifiers
        )

    if (
        domain_name == "null-predicates.md"
        or tokens
        & {
            "predicate",
            "bool3",
            "andb3",
            "orb3",
            "negb3",
        }
        or has_identifier("FExpr_Pred", "interp_predicate")
    ):
        features.add("predicate")
    if name == "formula_conj_acceptance_exact":
        features.add("predicate")
    if tokens & {"null", "nulls", "unknown", "unknown3"} or has_identifier("Unknown3"):
        features.add("null")
    if "case" in tokens or has_identifier("ScalarCase", "interp_case"):
        features.add("case")

    join_constructors = {
        "QueryJoinInner",
        "QueryJoinLeft",
        "QueryJoinRight",
        "QueryJoinFull",
        "QueryJoinSemi",
        "QueryJoinAnti",
        "QExpr_Join",
    }
    if "join" in tokens or identifiers & join_constructors:
        features.add("join")
    if name in {
        "eval_join_row_conditions_acceptance_exact",
        "eval_join_conditions_acceptance_exact",
        "project_join_sources_outcome_exact_map",
        "eval_join_bag_safe_of_acceptance_projection_exact",
    }:
        # These are the public exact-evaluation interfaces for join predicate
        # matrices and branch projection.  Keep their operational outcome and
        # safety routes stable even if their statements are later refactored
        # through transparent helper definitions.
        features.update(("join", "outcome", "runtime"))
    if name in {
        "project_join_sources_outcome_exact_map",
        "eval_join_bag_safe_of_acceptance_projection_exact",
    }:
        features.add("projection")
    if "cross" in tokens or has_identifier("QExpr_CrossJoin", "Q_Cross"):
        features.update(("join", "cross_join"))
    if identifiers & {"QueryJoinLeft", "QueryJoinRight", "QueryJoinFull"} or (
        "outer" in tokens and "join" in tokens
    ):
        features.update(("join", "outer_join"))
    if name in {
        "map_left_join_functional_permut",
        "tnull_map_left_join_functional_permut",
        "query_join_left_functional_projection_bag_on_representatives",
    }:
        features.add("partial_functional_left_join")
    if "QueryJoinSemi" in identifiers or ({"semi", "join"} <= tokens):
        features.update(("join", "semi_join"))
    if "QueryJoinAnti" in identifiers or ({"anti", "join"} <= tokens):
        features.update(("join", "anti_join"))
    if "QExpr_Join" in identifiers:
        # QExpr_Join is indexed by the closed six-way query_join_kind, so a law
        # quantified over its kind applies to every modeled outer/semi/anti arm.
        features.update(("join", "outer_join", "semi_join", "anti_join"))
    if "partial_functional_left_join" in features:
        # These three interfaces quantify over the LEFT arm specifically.  Do
        # not advertise the umbrella outer-join aliases (including FULL) merely
        # because the statement contains the QueryJoinLeft constructor.
        features.discard("outer_join")

    # SQL set-operation declarations use these exact syntax constructors or
    # the query_set_* semantic family.  Logical set union/intersection inside
    # a proof and DataException are intentionally not sufficient.
    if (
        normalized_name.startswith("query_set_")
        or has_identifier("QExpr_Set")
        or (
            has_identifier("query_set_bag")
            and bool(tokens & {"union", "inter", "intersection", "diff", "difference"})
        )
    ):
        features.add("set_operation")
        if identifiers & {"Union", "UnionMax"}:
            features.add("set_union")
        if "Inter" in identifiers:
            features.add("set_intersection")
        if "Diff" in identifiers:
            features.add("set_difference")
    if name in BAG_ALGEBRA_DECLARATIONS:
        features.update(("bag", "multiplicity"))

    if (
        domain_name == "aggregate-grouping.md"
        or "aggregate" in tokens
        or any(identifier.startswith("Aggregate") for identifier in identifiers)
    ):
        features.add("aggregate")
    if tokens & {"group", "groups", "grouping"} or has_identifier("QExpr_Group"):
        features.add("grouping")
    if name == "query_canonical_rows_length":
        # Canonicalization is the final list representation used by grouping
        # proofs; expose this generic length bridge on the grouping route even
        # though its primary semantic domain remains cardinality composition.
        features.add("grouping")
    if "grouping_sets" in normalized_name or has_identifier("QExpr_GroupingSets"):
        features.update(("grouping", "grouping_sets"))
    if tokens & {"count", "sum", "avg"} and module in {
        "AggregateRuntimeFacts.v",
        "NumericFacts.v",
        "BitwiseFacts.v",
    }:
        features.add("aggregate")
    if (
        "distinct" in tokens
        or "dedup" in tokens
        or has_identifier("QExpr_Distinct", "AggregateDistinct")
    ):
        features.add("distinct")

    if (
        tokens & {"filter", "where"}
        or has_identifier("QExpr_Filter", "eval_filter_rows_outcome")
        or name
        in {
            "formula_conj_acceptance_exact",
            "formula_exists_acceptance_exact",
            "formula_pred_acceptance_exact_safe",
            "interp_predicate_eq_true_is_true_acceptance",
            "tnull_join_condition_pred_acceptance_exact_safe",
        }
    ):
        features.add("filter")
    if tokens & {"project", "projection"} or has_identifier(
        "QExpr_Project", "QExpr_RowMap"
    ):
        features.add("projection")
    if module == "ProofAgentFacade.v" and name.startswith("tnull_row_eq_"):
        features.update(("row", "projection"))
    if name == "tnull_project_rows_select_columns_success":
        features.update(("projection", "runtime"))
    if name == "tnull_query_expr_project_select_columns_error_iff":
        features.update(("outcome", "projection", "runtime"))
    if "order_by" in normalized_name or has_identifier("QExpr_OrderBy"):
        features.add("order_by")
    if tokens & {"offset", "skipn"} or has_identifier("QExpr_Offset"):
        features.add("offset")
    if tokens & {"fetch", "limit", "firstn"} or has_identifier("QExpr_Fetch"):
        features.add("fetch")
    if (
        module == "OrderedQueryFacts.v"
        and bool(tokens & {"window", "rank", "partition"})
    ) or has_identifier("QExpr_Window", "QExpr_Rank"):
        features.add("window")

    if domain_name == "subquery-predicates.md":
        features.add("subquery")
    if "formula_exists" in normalized_name or has_identifier("FExpr_Exists"):
        features.update(("subquery", "exists_predicate"))
    if (
        domain_name == "subquery-predicates.md"
        and ("formula_in" in normalized_name or normalized_name.startswith("in_rows_"))
    ) or has_identifier("FExpr_In"):
        features.update(("subquery", "in_predicate"))
    if (
        domain_name == "subquery-predicates.md"
        and bool(tokens & {"quant", "quantified", "forall"})
    ) or has_identifier("FExpr_Quant"):
        features.update(("subquery", "quantified_predicate"))
    if tokens & {"correlated", "correlation"}:
        features.update(("subquery", "correlation"))
    if name in {
        "eval_formula_quant_error_iff",
        "eval_formula_quant_success_iff",
        "eval_formula_quant_subquery_congr",
    }:
        features.add("scalar_subquery_bridge")
    if name == "eval_formula_quant_error_iff":
        # This inversion exposes an error from the quantified child, including
        # the INTEGER SINGLE_VALUE wrapper's CardinalityViolation.
        features.add("scalar_subquery_error_bridge")

    single_value_identifiers = {
        identifier
        for identifier in folded_identifiers
        if identifier.startswith("single_value_int32")
        or identifier.startswith("aggregate_single_value_int32")
    }
    if (
        "single_value_int32" in normalized_name
        or single_value_identifiers
        or has_identifier("AggregateSingleValueInt32")
    ):
        features.update(
            ("scalar_subquery", "aggregate", "int32", "cardinality", "runtime")
        )

    numeric_identifiers = {
        identifier
        for identifier in identifiers
        if identifier.startswith(("numeric_", "Value_numeric", "ScalarNumeric"))
        or identifier
        in {"NumericFinite", "NumericNaN", "NumericPosInf", "NumericNegInf"}
    }
    if tokens & {"numeric", "decimal"} or numeric_identifiers:
        features.add("numeric")
    if tokens & {"typmod", "precision", "scale"} or has_identifier_prefix(
        "numeric_typmod", "string_typmod"
    ):
        features.add("typmod")
    if tokens & {"int32", "integer"} or has_identifier_prefix(
        "Value_int32", "ScalarInt32", "int32_"
    ):
        features.add("int32")
    if tokens & {"int64", "bigint"} or has_identifier_prefix(
        "Value_int64", "ScalarInt64", "int64_"
    ):
        features.add("int64")
    if (
        tokens
        & {
            "float",
            "float32",
            "float64",
            "nan",
            "infinity",
        }
        or ("double" in tokens and module == "NumericDerivedFacts.v")
        or has_identifier_prefix("Value_float", "Value_double", "float32_", "float64_")
    ):
        features.add("float")
    if tokens & {"bit", "bitwise", "shift"} or has_identifier_prefix("Bitwise"):
        features.add("bitwise")
    if tokens & {
        "string",
        "varchar",
        "char",
        "text",
        "like",
        "substring",
    } or has_identifier_prefix("Value_string", "String", "string_"):
        features.add("string")
    if "collation" in tokens:
        features.update(("string", "collation"))
    if tokens & {
        "date",
        "time",
        "timestamp",
        "timestamptz",
        "temporal",
        "interval",
    } or has_identifier_prefix(
        "Value_date", "Value_time", "Value_timestamp", "Date", "Time", "Timestamp"
    ):
        features.add("temporal")

    if tokens & {
        "runtime",
        "error",
        "safe",
        "outcome",
        "overflow",
        "failure",
    } or has_identifier("SqlError", "DataException", "CardinalityViolation"):
        features.add("runtime")
    if "outcome" in tokens or has_identifier(
        "TNullQueryExprOutcomeEq",
        "QueryExprOutcomeEquiv",
        "QueryExprGlobalOutcomeEquiv",
        "QueryExprGlobalTypedOutcomeEquiv",
        "eval_group_bag",
        "eval_group_bag_outcome",
    ):
        features.update(("outcome", "runtime"))
    if name == "tnull_eval_group_bag_direct_columns_true_no_error":
        features.update(("grouping", "outcome", "runtime"))
    if name == "query_expr_cross_join_union_right_equiv_safe":
        # The safe query-equivalence theorem is also a direct assembly route
        # for an error-preserving outcome goal via the standard implication.
        features.add("outcome")
    if tokens & {"schema", "conform", "typed", "attribute"} or has_identifier_prefix(
        "Schema", "schema_"
    ):
        features.add("schema")
    if (
        {"primary", "key"} <= tokens
        or {"foreign", "key"} <= tokens
        or ({"unique", "key"} <= tokens)
        or "unique_index" in normalized_name
        or "check_constraint" in normalized_name
    ):
        features.add("integrity")
    row_cardinality_modules = {
        "AggregateRuntimeFacts.v",
        "CardinalityCombinators.v",
        "IntegrityFacts.v",
        "OrderedQueryFacts.v",
        "QueryCardinality.v",
        "RelationalAlgebraFacts.v",
        "SchemaCardinality.v",
    }
    if domain_name == "cardinality-composition.md" or (
        module in row_cardinality_modules
        and (
            bool(tokens & {"length", "cardinal", "cardinality"})
            or "row_count" in normalized_name
        )
    ):
        features.add("cardinality")
    if tokens & {"occ", "occurrence", "occurrences", "multiplicity", "nodup"}:
        features.add("multiplicity")
    if normalized_name.startswith("list_support_rel_") or has_identifier(
        "list_support_rel"
    ):
        # These laws intentionally forget multiplicity and are consumed at a
        # later bag-reset boundary.  Route them as bag-support interfaces
        # without advertising multiplicity preservation.  Map-shaped variants
        # additionally belong to projection navigation.
        features.add("bag")
        if tokens & {"map", "unmap"}:
            features.add("projection")
    if tokens & {"bag", "bags", "permutation"} or has_identifier_prefix(
        "bag_", "rows_bag", "Febag", "Fecol"
    ):
        features.update(("bag", "multiplicity"))
    if is_non_equivalence_law(name):
        features.add("non_equivalence")
    elif tokens & {"equiv", "congr", "proper", "respect", "refl", "sym", "trans"}:
        features.add("equivalence")

    return frozenset(features)


def topics_for(domain_name: str, features: frozenset[str]) -> list[str]:
    topics = [DOMAIN_ENTRY_TOPICS[domain_name]]
    for feature, aliases in FEATURE_TOPIC_ALIASES:
        if feature in features:
            topics.extend(aliases)
    # Stable, case-insensitive de-duplication keeps aliases compact while the
    # semantic order above preserves all join-kind and scalar-cardinality routes.
    seen: set[str] = set()
    result: list[str] = []
    for topic in topics:
        key = topic.casefold()
        if key not in seen:
            seen.add(key)
            result.append(topic)
    return result[:20]


def declaration_domain(
    source_domain: str, module: str, name: str, features: frozenset[str]
) -> str:
    """Choose one primary card from declaration semantics, not just its file.

    Most fact modules are already focused.  The two intentionally broad public
    APIs are split here: ``ProofAgentFacade`` wraps several semantic layers,
    while ``OrderedQueryFacts`` also defines the generic query outcome API.
    The rules depend only on public declaration syntax and remain stable across
    generated benchmark instances.
    """
    ordered_features = {"order_by", "offset", "fetch", "window", "distinct"}
    relational_features = {"projection", "filter", "join", "bag", "multiplicity"}

    if module == "NumericRegroupFacts.v" and name.startswith(BAG_ALGEBRA_PREFIXES):
        return "relational-algebra.md"

    if name in QUERY_SYNTAX_DECLARATIONS or name.startswith(
        "query_expr_admissible_"
    ):
        return "query-syntax-bridges.md"

    if name in GENERIC_OUTCOME_DECLARATIONS:
        return "runtime-verification-rewrite.md"

    if module == "ProofAgentFacade.v":
        if "grouping" in features or name.startswith("tnull_eval_groups_"):
            return "aggregate-grouping.md"
        if name == "tnull_project_rows_select_columns_success":
            # This is the exact list-map law for one locally safe projection;
            # runtime is a useful cross-route, but the primary subject remains
            # relational projection rather than query-level error equivalence.
            return "relational-algebra.md"
        if features & {"outcome", "runtime"}:
            return "runtime-verification-rewrite.md"
        return "relational-algebra.md"

    if module == "OrderedQueryFacts.v":
        if name == "query_expr_union_success_Forall":
            # UNION is a bag-resetting set operator.  The declaration happens
            # to live beside ordered-query lifts, but its public contract is
            # multiplicity-preserving relational composition rather than an
            # ordered observation law.
            return "relational-algebra.md"
        if name in {
            "query_project_bag_congr",
            "query_project_success_bags_safe",
            "query_table_success_bags_functional",
        }:
            # These declarations expose multiplicity-preserving possible-bag
            # interfaces.  Their explicit local safety premises do not turn
            # the primary subject into generic runtime verification.
            return "relational-algebra.md"
        if features & ordered_features or "ordered" in identifier_tokens(name):
            return "ordered-observation.md"
        if "grouping" in features:
            return "aggregate-grouping.md"
        if features & {"outcome", "runtime", "equivalence"}:
            return "runtime-verification-rewrite.md"
        if features & relational_features:
            return "relational-algebra.md"
        return "ordered-observation.md"

    if module == "GroupedFilterOutcomeFacts.v" and name in {
        "formula_pred_acceptance_exact_safe",
        "eval_filter_rows_acceptance_exact",
        "filter_formula_observation_equiv_at_sym",
        "eval_filter_rows_ordered_outcome_congr_forward",
        "eval_filter_rows_ordered_outcome_congr",
        "query_expr_filter_outcome_congr_extensional_forward",
        "query_expr_filter_outcome_congr_extensional",
    }:
        # These declarations are source-adjacent to the grouped HAVING bridge,
        # but their public contracts are generic ordinary row-filter laws.
        return "relational-algebra.md"

    return source_domain


def semantic_routes(
    domain_name: str, module: str, name: str, features: frozenset[str]
) -> tuple[str, ...]:
    """Return deterministic cross-index routes for one declaration."""
    if "admissible" in identifier_tokens(name):
        # These general constructors remain inventoried in their primary card,
        # but the proof agent receives a concrete digest-bound admissibility
        # certificate in generated Queries.v.  Ranking constructors here would
        # invite needless per-case recomputation.
        return ()
    selected: set[str] = set()
    if name == "in_rows_acceptance_existsb":
        # This declaration is the deliberately small seam between SQL IN's
        # three-valued scalar semantics and a WHERE/semijoin Boolean keep
        # decision.  Make that cross-domain use explicit instead of leaving
        # it stranded in the scalar card.
        selected.update(("filter", "join"))
    if module == "ProofAgentFacade.v":
        selected.add("facade")
    if name.startswith("tnull_select_lookup_"):
        # These facade declarations expose FormalSQL projection's targeted
        # first-match cell interface even though their stable public names do
        # not repeat the implementation word "projection".
        selected.add("projection")
    if "outcome" in features:
        selected.add("outcome")
    if domain_name == "aggregate-grouping.md" or features & {
        "grouping",
        "grouping_sets",
        "scalar_subquery",
    }:
        selected.add("grouping")
    if domain_name == "runtime-verification-rewrite.md" or "runtime" in features:
        selected.add("runtime")
    if "projection" in features:
        selected.add("projection")
    if "filter" in features:
        selected.add("filter")
    if features & {"join", "cross_join", "outer_join", "semi_join", "anti_join"}:
        selected.add("join")
    if features & {"bag", "multiplicity"}:
        selected.add("bag")
    if domain_name == "ordered-observation.md" or features & {
        "order_by",
        "offset",
        "fetch",
        "window",
    }:
        selected.add("ordered")
    if "cardinality" in features:
        selected.add("cardinality")
    if domain_name == "schema-integrity.md" or features & {"schema", "integrity"}:
        selected.add("schema")
    if domain_name in {
        "null-predicates.md",
        "numeric-primitives.md",
        "numeric-derived.md",
        "bitwise.md",
        "string-temporal.md",
        "subquery-predicates.md",
    } or features & {
        "predicate",
        "null",
        "case",
        "numeric",
        "int32",
        "int64",
        "float",
        "bitwise",
        "string",
        "temporal",
        "subquery",
    }:
        selected.add("scalar")
    return tuple(route for route in ROUTES if route in selected)


ROUTE_PRIMARY_DOMAIN: dict[str, str] = {
    "outcome": "runtime-verification-rewrite.md",
    "grouping": "aggregate-grouping.md",
    "runtime": "runtime-verification-rewrite.md",
    "projection": "relational-algebra.md",
    "filter": "relational-algebra.md",
    "join": "relational-algebra.md",
    "bag": "relational-algebra.md",
    "ordered": "ordered-observation.md",
    "cardinality": "cardinality-composition.md",
    "schema": "schema-integrity.md",
}

# Lower rank is a better first read.  These are semantic name families, never
# benchmark or generated-schema identifiers.  They favor compositional query
# bridges over low-level implementation facts within the same source tier.
ROUTE_NAME_PRIORITY: dict[str, tuple[str, ...]] = {
    "facade": (
        "outcome_eq_of",
        "query_bag_eq",
        "having_key",
        "runtime_error_none",
        "total_functional",
        "bag_congr",
        "row_eq",
    ),
    "outcome": (
        "outcome_eq_of",
        "outcome_equiv_of",
        "outcome_equiv_congr",
        "bag_equiv_safe",
        "outcome_equiv",
    ),
    "grouping": (
        "having_key",
        "groups_true_outcome",
        "make_groups",
        "grouping_sets",
        "group_outcome",
        "grouping",
        "aggregate",
    ),
    "runtime": (
        "outcome_eq_of",
        "runtime_error_none",
        "runtime_error_congr",
        "safe_success",
        "runtime_safe",
        "_error_iff",
    ),
    "projection": (
        "direct_table_projection",
        "query_bag_eq",
        "bag_congr",
        "row_eq",
    ),
    "filter": (
        "having_key",
        "acceptance_exact",
        "bag_congr",
        "always_true",
        "filter",
        "sigma",
    ),
    "join": ("total_functional", "cross_join", "join"),
    "bag": (
        "query_bag_eq",
        "bag_congr",
        "bag_eq",
        "permut",
    ),
    "ordered": ("outcome_equiv", "order_by", "offset", "fetch", "ordered_rows"),
    "cardinality": ("int32", "length_le", "cardinality", "length"),
    "schema": ("primary_key", "unique", "foreign_key", "schema"),
    "scalar": ("outcome", "runtime", "congr", "iff"),
}

# A few cross-domain interfaces need to survive the small per-route retrieval
# quota.  The overrides are exact, generic declaration names: they describe
# reusable semantic interfaces, never a generated schema or benchmark shape.
EXACT_ROUTE_RANKS: dict[tuple[str, str], int] = {
    ("in_rows_acceptance_existsb", "filter"): 0,
    ("in_rows_acceptance_existsb", "join"): 0,
    ("in_rows_acceptance_existsb", "scalar"): 2,
    ("eval_grouping_sets_outcome_Forall2_congr", "outcome"): 0,
    ("eval_grouping_sets_outcome_Forall2_congr", "grouping"): 0,
    ("eval_grouping_sets_outcome_Forall2_congr", "runtime"): 0,
    ("eval_grouping_sets_success_fold_iff", "grouping"): 2,
    ("eval_grouping_sets_error_prefix_iff", "grouping"): 4,
    ("eval_grouping_sets_error_prefix_iff", "runtime"): 4,
    ("aggregate_distinct_input_Permutation_of_NoDup_support", "grouping"): 6,
    ("aggregate_distinct_input_Permutation_of_NoDup_support", "bag"): 8,
    ("partition_keys_Permutation_of_NoDup_support", "grouping"): 8,
    ("partition_keys_Permutation_of_NoDup_support", "bag"): 10,
    ("aggregate_input_values_preserves_Forall", "grouping"): 10,
    ("non_null_count_eq_length_of_Forall_nonnull", "grouping"): 12,
    ("non_null_count_eq_length_of_Forall_nonnull", "cardinality"): 8,
    ("query_bag_filter_union", "filter"): 4,
    ("query_bag_filter_union", "bag"): 12,
    ("query_bag_map_union", "bag"): 12,
    ("query_bag_map_congr", "bag"): 12,
    ("query_bag_filter_commute", "filter"): 6,
    ("query_bag_filter_commute", "bag"): 14,
    ("query_bag_filter_map_fusion", "filter"): 2,
    ("query_bag_filter_map_fusion", "bag"): 10,
    ("query_bag_map_pairwise_equiv_of_cardinal", "bag"): 18,
    ("query_bag_map_pairwise_equiv_of_cardinal", "cardinality"): 10,
    ("query_cross_join_bag_singleton_right_map", "join"): 10,
    ("query_cross_join_bag_singleton_right_map", "bag"): 14,
    ("eval_groups_success_Forall_projection", "grouping"): 6,
    ("eval_groups_success_Forall_projection", "projection"): 10,
    ("eval_group_bag_success_occurrence_property", "grouping"): 8,
    ("eval_group_bag_success_occurrence_property", "bag"): 12,
    ("query_make_groups_emit_NoDupA_of_key_reflection", "grouping"): 10,
    ("eval_group_bag_global_success_duplicate_free", "grouping"): 12,
    ("eval_group_bag_global_success_duplicate_free", "bag"): 14,
    ("eval_groups_having_key_conj_filter_exact", "grouping"): 6,
    ("eval_groups_having_key_conj_filter_exact", "filter"): 8,
    ("query_make_groups_filter_by_key_exact", "grouping"): 8,
    ("query_make_groups_filter_by_key_exact", "filter"): 10,
    ("bag_occurrences_disjoint_of_boolean_separator", "bag"): 12,
    ("bag_filter_congr_on_support", "bag"): 20,
    ("query_expr_filter_outcome_congr_extensional", "filter"): 0,
    ("query_expr_filter_outcome_congr_extensional", "outcome"): 10,
    ("query_expr_filter_outcome_congr_extensional", "runtime"): 10,
    ("interp_predicate_eq_true_is_true_acceptance", "filter"): 2,
    ("interp_predicate_eq_true_is_true_acceptance", "scalar"): 0,
    ("eval_filter_rows_ordered_outcome_congr", "filter"): 8,
    ("eval_filter_rows_ordered_outcome_congr", "outcome"): 16,
    ("eval_filter_rows_ordered_outcome_congr", "runtime"): 16,
    ("query_expr_project_success_Forall", "projection"): 8,
    ("tnull_projection_envs_eq_of_select_items", "facade"): 2,
    ("tnull_projection_envs_eq_of_select_items", "projection"): 0,
    ("query_expr_union_success_Forall", "bag"): 8,
    ("query_expr_cross_join_success_Forall", "join"): 8,
    ("query_expr_cross_join_success_Forall", "bag"): 10,
    (
        "tnull_closed_group_sum_numeric_dot_argument_observations_permutation_rows",
        "grouping",
    ): 0,
    ("tnull_closed_group_sum_numeric_dot_value_runtime_exact", "grouping"): 2,
    ("tnull_closed_group_sum_numeric_dot_value_runtime_exact", "runtime"): 8,
    (
        "query_make_groups_closed_sum_numeric_dot_outer_sum_value_runtime_exact",
        "grouping",
    ): 14,
    (
        "query_make_groups_closed_sum_numeric_dot_outer_sum_value_runtime_exact",
        "runtime",
    ): 18,
    ("query_expr_table_success_rows_absent_attribute", "schema"): 0,
    ("query_expr_table_success_rows_present_conform_attribute", "schema"): 2,
    ("query_same_rows_as_conforming_table_absent_attribute", "schema"): 4,
    ("query_same_rows_as_conforming_table_present_attribute", "schema"): 6,
    ("eval_join_row_conditions_acceptance_exact", "join"): 6,
    ("eval_join_row_conditions_acceptance_exact", "outcome"): 14,
    ("eval_join_row_conditions_acceptance_exact", "runtime"): 14,
    ("eval_join_conditions_acceptance_exact", "join"): 4,
    ("eval_join_conditions_acceptance_exact", "outcome"): 10,
    ("eval_join_conditions_acceptance_exact", "runtime"): 10,
    ("project_join_sources_outcome_exact_map", "join"): 4,
    ("project_join_sources_outcome_exact_map", "outcome"): 10,
    ("project_join_sources_outcome_exact_map", "runtime"): 10,
    ("project_join_sources_outcome_exact_map", "projection"): 4,
    ("eval_join_bag_safe_of_acceptance_projection_exact", "join"): 0,
    ("eval_join_bag_safe_of_acceptance_projection_exact", "outcome"): 2,
    ("eval_join_bag_safe_of_acceptance_projection_exact", "runtime"): 2,
    ("eval_join_bag_safe_of_acceptance_projection_exact", "projection"): 6,
    ("eval_join_bag_safe_of_acceptance_projection_exact", "bag"): 6,
    ("eval_group_bag_exact_rows_permut_equiv", "bag"): 18,
    ("eval_group_bag_exact_rows_permut_equiv", "grouping"): 8,
    ("eval_groups_acceptance_outcome_exact", "grouping"): 18,
    ("eval_groups_acceptance_outcome_exact", "outcome"): 20,
    ("eval_groups_acceptance_outcome_exact", "runtime"): 22,
    ("formula_conj_acceptance_exact", "scalar"): 20,
    ("group_filter_map_permutation", "grouping"): 14,
    ("map_left_join_functional_permut", "join"): 10,
    ("query_make_groups_permut_nonempty", "grouping"): 12,
    ("query_make_groups_projected_bag_eq_of_support_rel", "grouping"): 4,
    ("query_make_groups_projected_bag_eq_of_support_rel", "bag"): 6,
    ("query_canonical_rows_length", "grouping"): 16,
    ("query_expr_cross_join_outcome_equiv_congr", "join"): 22,
    ("query_expr_cross_join_union_right_equiv_safe", "join"): 20,
    ("query_expr_cross_join_union_right_equiv_safe", "outcome"): 22,
    ("query_expr_cross_join_union_right_outcome_equiv_safe", "join"): 20,
    ("query_expr_outcome_equiv_implies_success_bags", "bag"): 22,
    ("query_expr_filter_bag_closed_exact", "filter"): 2,
    ("query_expr_filter_bag_closed_exact", "bag"): 6,
    ("query_expr_project_bag_closed_safe", "projection"): 2,
    ("query_expr_project_bag_closed_safe", "bag"): 6,
    ("query_expr_project_outcome_equiv_congr_safe", "projection"): 22,
    ("query_project_success_bags_safe", "projection"): 6,
    ("query_table_success_bags_functional", "bag"): 22,
    ("tnull_direct_projection_alias_value", "projection"): 4,
    ("tnull_join_condition_pred_acceptance_exact_safe", "facade"): 0,
    ("tnull_join_condition_pred_acceptance_exact_safe", "runtime"): 4,
    ("tnull_join_condition_pred_acceptance_exact_safe", "filter"): 6,
    ("tnull_join_condition_pred_acceptance_exact_safe", "join"): 2,
    ("tnull_row_eq_refl", "facade"): 8,
    ("tnull_row_eq_refl", "projection"): 10,
    ("tnull_row_eq_sym", "facade"): 8,
    ("tnull_row_eq_sym", "projection"): 10,
    ("tnull_row_eq_trans", "facade"): 2,
    ("tnull_row_eq_trans", "projection"): 4,
    ("tnull_select_lookup_some_iff_projected_label", "facade"): 6,
    ("tnull_select_lookup_some_iff_projected_label", "projection"): 4,
    (
        "tnull_select_lookup_none_iff_projected_label_absent",
        "facade",
    ): 6,
    (
        "tnull_select_lookup_none_iff_projected_label_absent",
        "projection",
    ): 4,
    ("tnull_project_rows_select_columns_success", "facade"): 4,
    ("tnull_project_rows_select_columns_success", "runtime"): 8,
    ("tnull_project_rows_select_columns_success", "projection"): 2,
    ("tnull_query_expr_project_select_columns_error_iff", "facade"): 4,
    ("tnull_query_expr_project_select_columns_error_iff", "outcome"): 4,
    ("tnull_query_expr_project_select_columns_error_iff", "runtime"): 4,
    ("tnull_query_expr_project_select_columns_error_iff", "projection"): 6,
    ("tnull_select_lookup_retained", "facade"): 4,
    ("tnull_select_lookup_retained", "projection"): 2,
    ("tnull_select_lookup_direct_value", "facade"): 6,
    ("tnull_select_lookup_direct_value", "projection"): 4,
    ("tnull_select_lookup_constant_value", "facade"): 8,
    ("tnull_select_lookup_constant_value", "projection"): 6,
    ("tnull_select_lookup_direct_compose", "facade"): 2,
    ("tnull_select_lookup_direct_compose", "projection"): 2,
    ("tnull_select_lookup_constant_direct_compose", "facade"): 2,
    ("tnull_select_lookup_constant_direct_compose", "projection"): 2,
    ("eval_group_bag_true_projected_support_equiv", "grouping"): 4,
    ("eval_group_bag_true_projected_support_equiv", "outcome"): 8,
    (
        "query_expr_group_outcome_equiv_of_supported_child_outcomes",
        "grouping",
    ): 4,
    (
        "query_expr_group_outcome_equiv_of_supported_child_outcomes",
        "outcome",
    ): 4,
    (
        "tnull_eval_group_bag_direct_columns_true_equiv_of_projection_support",
        "grouping",
    ): 2,
    (
        "tnull_eval_group_bag_direct_columns_true_equiv_of_projection_support",
        "outcome",
    ): 4,
    ("tnull_eval_group_bag_direct_columns_true_no_error", "facade"): 2,
    ("tnull_eval_group_bag_direct_columns_true_no_error", "outcome"): 4,
    ("tnull_eval_group_bag_direct_columns_true_no_error", "grouping"): 2,
    ("tnull_eval_group_bag_direct_columns_true_no_error", "runtime"): 2,
    ("tnull_eval_group_bag_direct_columns_true_no_error", "bag"): 8,
    (
        "tnull_direct_columns_group_outcome_equiv_of_projected_support",
        "facade",
    ): 0,
    (
        "tnull_direct_columns_group_outcome_equiv_of_projected_support",
        "grouping",
    ): 0,
    (
        "tnull_direct_columns_group_outcome_equiv_of_projected_support",
        "outcome",
    ): 0,
    (
        "tnull_direct_columns_group_outcome_equiv_of_projected_support",
        "runtime",
    ): 4,
    ("tnull_direct_columns_group_projection_support_rel", "grouping"): 6,
    ("tnull_direct_columns_group_projection_support_rel", "projection"): 8,
    ("tnull_direct_columns_group_projection_support_rel", "bag"): 10,
    (
        "tnull_direct_columns_group_rows_bag_eq_of_projection_support",
        "grouping",
    ): 2,
    (
        "tnull_direct_columns_group_rows_bag_eq_of_projection_support",
        "projection",
    ): 16,
    (
        "tnull_direct_columns_group_rows_bag_eq_of_projection_support",
        "bag",
    ): 2,
    ("list_support_rel_compose", "bag"): 8,
    ("list_support_rel_map_transport", "projection"): 10,
    ("list_support_rel_map_transport", "bag"): 12,
    ("list_support_rel_map_iff", "projection"): 12,
    ("list_support_rel_map_iff", "bag"): 14,
    ("list_support_rel_unmap_left", "projection"): 14,
    ("list_support_rel_unmap_left", "bag"): 16,
    ("list_support_rel_map_left_with_witness", "projection"): 14,
    ("list_support_rel_map_left_with_witness", "bag"): 16,
    ("tnull_map_left_join_functional_permut", "facade"): 6,
    ("tnull_map_left_join_functional_permut", "join"): 8,
}


def route_rank(
    route: str,
    domain_name: str,
    module: str,
    kind: str,
    name: str,
) -> int:
    """Rank a declaration inside one semantic route using stable public shape."""
    exact_rank = EXACT_ROUTE_RANKS.get((name, route))
    if exact_rank is not None:
        return exact_rank
    if module == "ProofAgentFacade.v":
        rank = 16
    elif ROUTE_PRIMARY_DOMAIN.get(route) == domain_name:
        rank = 36
    else:
        rank = 52

    normalized = name.casefold()
    for priority, marker in enumerate(ROUTE_NAME_PRIORITY.get(route, ())):
        if marker in normalized:
            rank -= max(2, 14 - 2 * priority)
            break
    if kind == "Theorem":
        rank -= 2
    elif kind == "Corollary":
        rank -= 1
    return max(0, rank)


def ranked_entries_for_route(
    entries: list[dict[str, object]], route: str
) -> list[dict[str, object]]:
    return sorted(
        (entry for entry in entries if route in entry["routes"]),  # type: ignore[operator]
        key=lambda entry: (
            int(entry["routeRanks"][route]),  # type: ignore[index]
            str(entry["name"]).casefold(),
        ),
    )


def semantic_subject(domain_name: str, features: frozenset[str]) -> str:
    if "scalar_subquery" in features:
        return "SINGLE_VALUE scalar-subquery cardinality"
    if "scalar_subquery_bridge" in features:
        return "scalar-subquery quantified-comparison evaluation"
    join_kinds = [
        label
        for feature, label in (
            ("outer_join", "outer"),
            ("semi_join", "semi"),
            ("anti_join", "anti"),
        )
        if feature in features
    ]
    if join_kinds:
        return f"{'/'.join(join_kinds)}-join semantics"
    if "set_operation" in features:
        return "SQL bag/set operations"
    if "subquery" in features:
        return "predicate-subquery evaluation"
    if "join" in features:
        return "join cardinality" if "cardinality" in features else "join semantics"

    # Prefer the focused document's proof task over incidental constructors in
    # a declaration.  For example, nullable tuples in QueryCardinality do not
    # turn a row-count lemma into a NULL lemma, and aggregate transition types
    # in NumericFacts do not hide its numeric representation purpose.
    if domain_name == "aggregate-grouping.md":
        return (
            "aggregate grouping" if "grouping" in features else "aggregate evaluation"
        )
    if domain_name == "cardinality-composition.md":
        return "row cardinality and compositional bounds"
    if domain_name == "schema-integrity.md":
        return "schema and integrity reasoning"
    if domain_name == "relational-algebra.md":
        return "bag multiplicity" if "bag" in features else "relational algebra"
    if domain_name == "ordered-observation.md":
        if "window" in features:
            return "window/rank evaluation"
        if "order_by" in features:
            return "ordered query observation"
        if features & {"offset", "fetch"}:
            return "ordered slicing"
        return "ordered query equivalence"
    if domain_name == "query-syntax-bridges.md":
        return "projection and tuple-syntax bridging"
    if domain_name == "null-predicates.md":
        return (
            "SQL NULL and three-valued behavior"
            if "null" in features
            else "scalar-predicate semantics"
        )
    if domain_name == "bitwise.md":
        return "bitwise scalar and aggregate semantics"
    if domain_name in {"numeric-primitives.md", "numeric-derived.md"}:
        return (
            "numeric aggregate semantics"
            if "aggregate" in features
            else "typed numeric semantics"
        )
    if domain_name == "string-temporal.md":
        return "temporal semantics" if "temporal" in features else "string semantics"
    if domain_name == "runtime-verification-rewrite.md":
        return "SQL verification and runtime outcomes"
    return DOMAIN_ENTRY_TOPICS[domain_name]


def humanized_law_name(name: str) -> str:
    """Retain declaration-name order while making a fallback purpose readable."""
    words: list[str] = []
    for snake_part in name.rstrip("'").split("_"):
        words.extend(
            part.casefold() for part in CAMEL_BOUNDARY.split(snake_part) if part
        )
    replacements = {
        "iff": "if-and-only-if",
        "eq": "equality",
        "neq": "disequality",
        "le": "upper-bound",
        "lt": "strict-bound",
        "ge": "lower-bound",
        "gt": "strict-lower-bound",
        "congr": "congruence",
    }
    return " ".join(replacements.get(word, word) for word in words)


def is_non_equivalence_law(name: str) -> bool:
    normalized = name.casefold()
    return "not_equiv" in normalized or "non_equiv" in normalized


def summary_for(name: str, domain_name: str, features: frozenset[str]) -> str:
    subject = semantic_subject(domain_name, features)
    name_tokens = identifier_tokens(name)
    if name == "in_rows_acceptance_existsb":
        return (
            "Reduces only the TRUE-acceptance observation of SQL IN over a row "
            "bag to an ordinary Boolean existence test, retaining the underlying "
            "FALSE/UNKNOWN distinction."
        )
    if name == "eval_grouping_sets_outcome_Forall2_congr":
        return (
            "Lifts branchwise exact outcome agreement through an arbitrary "
            "ordered GROUPING SETS schedule without moving its first error."
        )
    if name == "eval_grouping_sets_success_fold_iff":
        return (
            "Characterizes every successful GROUPING SETS schedule as the "
            "ordered UNION ALL fold of one successful bag per branch."
        )
    if name == "eval_grouping_sets_error_prefix_iff":
        return (
            "Characterizes a GROUPING SETS error by an ordered prefix of "
            "successful branches followed by the exact failing branch."
        )
    if name == "aggregate_distinct_input_Permutation_of_NoDup_support":
        return (
            "Identifies DISTINCT aggregate selection, up to permutation, with "
            "any duplicate-free list having exactly the original value support."
        )
    if name == "partition_keys_Permutation_of_NoDup_support":
        return (
            "Identifies the keys materialized by generic partitioning with any "
            "duplicate-free same-support key representative, up to permutation."
        )
    if name == "aggregate_input_values_preserves_Forall":
        return (
            "Transports an arbitrary pointwise input property through ALL or "
            "DISTINCT aggregate input selection."
        )
    if name == "non_null_count_eq_length_of_Forall_nonnull":
        return (
            "Computes aggregate non-NULL count as the exact list length when "
            "every input value is proved non-NULL."
        )
    if name in {
        "query_bag_filter_union",
        "query_bag_map_union",
        "query_bag_map_congr",
        "query_bag_filter_commute",
        "query_bag_filter_map_fusion",
    }:
        return (
            "Exposes the named multiplicity-preserving finite-bag filter/map "
            "homomorphism under semantic predicate or row-map properness."
        )
    if name == "query_bag_map_pairwise_equiv_of_cardinal":
        return (
            "Equates two mapped bags of equal cardinality when every reached "
            "left mapped row is semantically equal to every reached right one."
        )
    if name == "query_cross_join_bag_singleton_right_map":
        return (
            "Normalizes a CROSS JOIN with one right bag occurrence to the "
            "corresponding multiplicity-preserving row map of the left bag."
        )
    if name == "query_make_groups_closed_sum_numeric_dot_outer_sum_value_runtime_exact":
        return (
            "Regroups closed-group SUM(NUMERIC column) values while preserving "
            "only the outer SUM value and its local runtime callback."
        )
    if name == "eval_join_row_conditions_acceptance_exact":
        return (
            "Characterizes one left row's complete join-condition evaluation as "
            "the successful Boolean acceptance map over right rows."
        )
    if name == "eval_join_conditions_acceptance_exact":
        return (
            "Lifts pairwise exact join acceptance to the complete row-major "
            "successful condition matrix, excluding condition errors."
        )
    if name == "project_join_sources_outcome_exact_map":
        return (
            "Lifts exact projection of every reached matched or padded join "
            "source to one ordered successful map over the source list."
        )
    if name == "eval_join_bag_safe_of_acceptance_projection_exact":
        return (
            "Combines total exact pair acceptance with exact matched/padded "
            "projection to construct a successful join bag and rule out every "
            "local join error for any modeled join kind."
        )
    if name == "tnull_join_condition_pred_acceptance_exact_safe":
        return (
            "Builds the generic exact join-acceptance contract for a runtime-safe "
            "TNull scalar predicate while preserving authoritative Bool3 semantics."
        )
    if name in {"tnull_row_eq_refl", "tnull_row_eq_sym", "tnull_row_eq_trans"}:
        return (
            "Exposes the displayed equivalence law for the facade's semantic "
            "TNull row equality without reopening ordered-set internals."
        )
    if name == "tnull_select_lookup_some_iff_projected_label":
        return (
            "Relates successful first-match SELECT lookup exactly to membership "
            "of the corresponding projected output label."
        )
    if name == "tnull_select_lookup_none_iff_projected_label_absent":
        return (
            "Relates failed first-match SELECT lookup exactly to Boolean absence "
            "of the corresponding projected output label."
        )
    if name == "tnull_project_rows_select_columns_success":
        return (
            "Computes direct-column projection of a row list as an exact ordered "
            "successful map, discharging all projection-local scalar errors."
        )
    if name == "tnull_query_expr_project_select_columns_error_iff":
        return (
            "Shows that a direct-column query projection has exactly its child's "
            "error observations and introduces no projection-local error."
        )
    if name == "tnull_eval_group_bag_direct_columns_true_no_error":
        return (
            "Rules out every local group-bag error for direct-column GROUP BY "
            "with TRUE HAVING, for any supplied successful child bag."
        )
    if name.startswith("list_support_rel_"):
        return (
            "Transports bidirectional row support through the displayed relation; "
            "it does not preserve duplicate multiplicity by itself."
        )
    if name == "formula_conj_acceptance_exact":
        return (
            "Composes exact TRUE-acceptance contracts through eager SQL AND "
            "or OR without identifying the underlying FALSE and UNKNOWN values."
        )
    if name == "formula_exists_acceptance_exact":
        return (
            "Builds an exact EXISTS acceptance contract from inhabited child "
            "successes that agree on emptiness and from explicit absence of errors."
        )
    if name == "eval_groups_true_outcome_exact":
        return (
            "Characterizes all-TRUE evaluation in each `group_env` exactly as "
            "the ordered projection map after all four per-group runtime checks, "
            "including as the group-processing component of a regrouping proof."
        )
    if name == "eval_groups_acceptance_outcome_exact":
        return (
            "Characterizes arbitrary exact HAVING acceptance in each `group_env` "
            "as the ordered projection map over `List.filter`, retaining duplicate "
            "groups and requiring scalar SELECT safety only for accepted groups."
        )
    if name == "bag_filter_congr_on_support":
        return (
            "Transports finite-bag filtering across bag-equal inputs when two "
            "predicates agree on semantic tuple occurrences in the left support."
        )
    if name == "tnull_direct_projection_alias_value":
        return (
            "Reads an aliased direct SELECT output exactly as its present source "
            "attribute under unique output aliases, preserving NULL values."
        )
    if name == "database_conforms_schema_primary_key":
        return (
            "Extracts a declared primary-key contract directly from database "
            "conformance and constraint membership for functional key reasoning."
        )
    if name == "database_conforms_schema_foreign_key_nonnull_referenced":
        return (
            "Provides the schema-side totality witness used by an outer join "
            "when every referencing foreign-key column is declared NOT NULL."
        )
    if name == "eval_group_bag_exact_rows_permut_equiv":
        return (
            "Lifts exact per-representative group evaluation through the "
            "quotient-saturated group-bag reset when emitted rows are semantic "
            "permutations, preserving key and processing errors."
        )
    if name == "query_make_groups_permut_nonempty":
        return (
            "Transports semantic row permutation to semantic group permutation "
            "for a nonempty grouping-term list."
        )
    if name == "group_filter_map_permutation":
        return (
            "Transports a semantic group permutation through an equality-respecting "
            "group filter and projection map while retaining occurrences."
        )
    if name == "query_make_groups_constant_nonempty_key":
        return (
            "Computes groups for one constant nonempty grouping key as no group "
            "on empty input or one reverse-ordered member list otherwise."
        )
    if name == "formula_pred_acceptance_exact_safe":
        return (
            "Builds an exact SQL TRUE-acceptance contract for an interpreted "
            "scalar predicate from explicit argument runtime safety."
        )
    if name == "eval_filter_rows_acceptance_exact":
        return (
            "Characterizes row-filter outcomes exactly as successful "
            "`List.filter` under per-row exact-acceptance/no-error contracts."
        )
    if name == "query_expr_outcome_equiv_implies_success_bags":
        return (
            "Projects fixed-environment error-preserving ordered equivalence to "
            "equality of possible successful bags, including the error-only case."
        )
    if name == "eval_query_expr_set_error_iff":
        return (
            "Characterizes a set-operation error as a left error or as a right "
            "error reached after one successful left observation."
        )
    if name == "eval_query_expr_cross_join_error_iff":
        return (
            "Characterizes a CROSS JOIN error with its exact left-to-right child "
            "evaluation schedule."
        )
    if name == "query_expr_set_outcome_equiv_congr":
        return (
            "Lifts two child outcome equivalences through a set-operation bag "
            "reset while preserving exact output schema and short-circuit errors."
        )
    if name == "query_expr_cross_join_outcome_equiv_congr":
        return (
            "Lifts two child outcome equivalences through CROSS JOIN's bag reset "
            "while preserving appended output schema, multiplicity, and errors."
        )
    if name == "query_project_success_bags_safe":
        return (
            "Characterizes the possible successful bags of a locally safe "
            "projection as a multiplicity-preserving bag map of child bags."
        )
    if name == "query_project_bag_congr":
        return "Transports input bag equality through the declared projection bag map."
    if name == "query_table_success_bags_functional":
        return "Shows that a base table has one possible successful bag modulo bag equality."
    if name == "query_cross_join_union_right_success_bags":
        return (
            "Distributes CROSS JOIN over right-hand UNION ALL at the possible-bag "
            "layer while preserving duplicate multiplicity."
        )
    if name in {
        "query_expr_cross_join_union_right_equiv_safe",
        "query_expr_cross_join_union_right_outcome_equiv_safe",
    }:
        return (
            "Assembles the right-hand CROSS JOIN/UNION ALL distribution law into "
            "a safe exact query equivalence with explicit runtime premises."
        )
    if name == "query_expr_project_outcome_equiv_congr_safe":
        return (
            "Lifts a fixed-environment child outcome equivalence through one "
            "locally safe projection."
        )
    if name.startswith("tnull_") and name.endswith("_eval_bag_congr"):
        return (
            "Lifts bag equality through the displayed TNull relational operator "
            "under its explicit evaluation premises."
        )
    if name.startswith("tnull_") and name.endswith("_runtime_error_congr"):
        return (
            "Lifts equality of child runtime errors through the displayed TNull "
            "relational operator."
        )
    if name.startswith("tnull_") and name.endswith("_runtime_error_none"):
        return (
            "Composes the displayed child and expression safety premises into "
            "absence of a TNull operator runtime error."
        )
    if name in {
        "map_left_join_functional_permut",
        "tnull_map_left_join_functional_permut",
    }:
        return (
            "Identifies a projected at-most-one LEFT JOIN with the mapped left "
            "input up to semantic permutation, retaining unmatched and duplicate "
            "left occurrences without a total-match premise."
        )
    if name in {"map_theta_join_total_functional", "map_left_join_total_functional"}:
        return (
            "Identifies the exact projected join list with the pointwise mapped "
            "left input under total and at-most-one matching."
        )
    if name == "eval_filter_rows_always_true_iff":
        return (
            "Characterizes successful filtering when every reached formula "
            "evaluation succeeds with SQL TRUE."
        )
    if name == "single_value_int32_runtime_error_none_iff":
        return "Characterizes SINGLE_VALUE safety exactly as at most one selected INT32 value."
    if "single_value_int32" in name and "cardinality" in name:
        return "Characterizes CardinalityViolation exactly as at least two selected INT32 values."
    if name == "aggregate_single_value_int32_selected_empty":
        return "Shows that empty selected input yields SQL NULL with no SINGLE_VALUE runtime error."
    if name == "aggregate_single_value_int32_selected_singleton":
        return "Shows that singleton selected input returns its INT32 value with no SINGLE_VALUE runtime error."
    if is_non_equivalence_law(name):
        if "runtime_error" in name:
            return "Derives query non-equivalence from the displayed modeled runtime error on the indicated side."
        if "mismatch" in name or "witness" in name:
            return "Derives query non-equivalence from the displayed projection/sort mismatch witness."
        return f"Derives non-equivalence from the displayed {subject} witness."
    if name.endswith("_refl"):
        return f"Establishes reflexivity for {subject}."
    if name.endswith(("_sym", "_symmetric")):
        return f"Reverses a proved {subject} relation."
    if name.endswith(("_trans", "_transitive")):
        return f"Composes two {subject} relations through an intermediate result."
    if "_iff" in name or name.endswith("iff"):
        return f"Gives necessary and sufficient conditions for {subject}."
    if "injective" in name:
        return f"Recovers source equality from the declared {subject} representation."
    if "length_le" in name or "length_bound" in name or "cardinal_le" in name:
        return f"Provides the stated reusable upper bound for {subject}."
    if "length" in name or "cardinal" in name:
        return f"Relates {subject} to the exact list length or bag cardinality shown below."
    if "congr" in name or "equiv" in name:
        return f"Transports or composes {subject} across the declared equivalence."
    if "runtime_error_none" in name or name.endswith("_safe"):
        return f"Establishes the explicit runtime-safety direction for {subject}."
    if "runtime_error" in name or "_error" in name or "failure" in name:
        return f"Exposes the modeled SQL error condition or propagation direction for {subject}."
    if name_tokens & {"null", "nulls", "unknown", "unknown3"}:
        return f"Makes the SQL NULL/UNKNOWN branch explicit for {subject}."
    if "success" in name:
        return f"Inverts or constructs the successful evaluation branch for {subject}."
    if "empty" in name:
        return f"States the exact empty-input or empty-result law for {subject}."
    if "permutation" in name:
        return f"Shows that the declared {subject} result is invariant under input permutation."
    if "nodup" in name.casefold():
        return f"Establishes the displayed duplicate-freedom property for {subject}."
    if "invariant" in name:
        return f"Preserves the declared {subject} result across the indicated transformation."
    if "preserve" in name:
        return f"Shows that the indicated operator preserves the displayed {subject} property."
    if "transport" in name:
        return f"Transports the displayed hypotheses and conclusion for {subject}."
    if "roundtrip" in name:
        return f"Proves the stated cast or representation round trip for {subject}."
    if "reduce_to" in name:
        return f"Reduces the composite {subject} condition to the displayed local condition."
    if "total" in name:
        return f"Establishes totality of the indicated {subject} operation under the shown premises."
    if "closed" in name or "closure" in name:
        return f"Establishes the displayed closure property for {subject}."
    if "_range" in name or "in_range" in name:
        return f"Connects the displayed range/representability premise to {subject}."
    if "_fold" in name or "transition" in name:
        return (
            f"Relates the fold or transition state to the displayed {subject} result."
        )
    if "_as_" in name or "representation" in name:
        return f"Bridges the two displayed representations of {subject}."
    if "membership" in name or "member" in name or "occ" in name:
        return f"Relates membership or occurrence evidence to {subject}."
    if "comm" in name:
        return f"Establishes commutativity for the declared {subject} operator."
    if "assoc" in name:
        return f"Establishes associativity for the declared {subject} operator."
    if "idempotent" in name:
        return f"Establishes idempotence for the declared {subject} operator."
    if "absorb" in name:
        return f"Establishes the displayed absorption law for {subject}."
    if "cancel" in name:
        return f"Establishes the displayed cancellation direction for {subject}."
    return (
        f"States the {humanized_law_name(name)} law for {subject}, "
        "in the exact direction displayed by the declaration."
    )


def applicability_for(name: str, domain_name: str, features: frozenset[str]) -> str:
    if name == "in_rows_acceptance_existsb":
        return (
            "Use after proving the per-candidate `Bool.is_true` decision.  The "
            "conclusion is suitable for WHERE or semijoin filtering only; it is "
            "not equality of the complete SQL Bool3 result."
        )
    if name in {
        "eval_grouping_sets_outcome_Forall2_congr",
        "eval_grouping_sets_success_fold_iff",
        "eval_grouping_sets_error_prefix_iff",
    }:
        return (
            "Use for arbitrary grouping-set lists in their original order.  "
            "Branch order is semantic for runtime errors and must not be replaced "
            "by a permutation premise."
        )
    if name in {
        "aggregate_distinct_input_Permutation_of_NoDup_support",
        "partition_keys_Permutation_of_NoDup_support",
    }:
        return (
            "Use only after supplying both duplicate-freedom and exact support "
            "equivalence; neither premise follows from cardinality alone."
        )
    if name == "aggregate_input_values_preserves_Forall":
        return (
            "Use for properties insensitive to occurrence removal; DISTINCT may "
            "discard duplicates but cannot introduce a new value."
        )
    if name == "non_null_count_eq_length_of_Forall_nonnull":
        return (
            "Use only with an explicit `Forall` non-NULL proof; SQL NULL inputs "
            "would otherwise be omitted by the count."
        )
    if name in {
        "query_bag_filter_union",
        "query_bag_map_union",
        "query_bag_map_congr",
        "query_bag_filter_commute",
        "query_bag_filter_map_fusion",
    }:
        return (
            "Use below the query evaluator after proving every displayed "
            "predicate/map respects semantic tuple equality; these laws preserve "
            "multiplicity but do not discharge expression runtime errors."
        )
    if name == "query_bag_map_pairwise_equiv_of_cardinal":
        return (
            "Use for constant-observation projections after equal bag cardinality "
            "and pairwise equality on actual representatives are established."
        )
    if name == "query_cross_join_bag_singleton_right_map":
        return (
            "Use only for a semantic singleton bag on the right; lift to a query "
            "outcome separately so child and projection errors remain observable."
        )
    subject = semantic_subject(domain_name, features)
    if name == "query_make_groups_closed_sum_numeric_dot_outer_sum_value_runtime_exact":
        return (
            "Use only for the displayed closed-group SUM(NUMERIC Dot) family. "
            "The conclusion covers the outer SUM value/local callback; it does "
            "not prove inner aggregate safety or a complete grouped-query outcome."
        )
    if name == "eval_join_row_conditions_acceptance_exact":
        return (
            "Use after establishing the exact acceptance contract for every "
            "right row that occurs in the displayed list; order and duplicates "
            "are retained by `map`."
        )
    if name == "eval_join_conditions_acceptance_exact":
        return (
            "Use after establishing exact acceptance for every reached left/right "
            "pair; the conclusion is the literal row-major matrix, not a bag."
        )
    if name == "project_join_sources_outcome_exact_map":
        return (
            "Use after proving exact successful projection only for sources in "
            "the reached source list; matched and both NULL-padded source forms "
            "must remain covered."
        )
    if name == "eval_join_bag_safe_of_acceptance_projection_exact":
        return (
            "Use to discharge local join success and no-error obligations after "
            "providing total pairwise acceptance and total source-projection "
            "contracts; child-query errors are outside this bag-local theorem."
        )
    if name == "tnull_join_condition_pred_acceptance_exact_safe":
        return (
            "Use for a `FExpr_Pred` join condition after proving its eager argument "
            "runtime-error classifier is `None`; FALSE and UNKNOWN remain distinct "
            "Bool3 results even though both reject the joined row."
        )
    if name in {"tnull_row_eq_refl", "tnull_row_eq_sym", "tnull_row_eq_trans"}:
        return (
            "Use to compose generated row correspondences through the facade's "
            "semantic equality; this is not Leibniz tuple equality."
        )
    if name == "tnull_select_lookup_some_iff_projected_label":
        return (
            "Use in either direction between first-match lookup and projected "
            "label presence; repeated aliases do not authorize choosing a later "
            "SELECT item."
        )
    if name == "tnull_select_lookup_none_iff_projected_label_absent":
        return (
            "Use in either direction to prove concrete lookup failure or output "
            "label absence without unfolding projection-label construction."
        )
    if name == "tnull_project_rows_select_columns_success":
        return (
            "Use only for `SelectColumns`; it proves projection-local safety and "
            "the exact ordered row map, independently of any child-query outcome."
        )
    if name == "tnull_query_expr_project_select_columns_error_iff":
        return (
            "Use to move an error observation across a `SelectColumns` query "
            "projection in either direction; no child error is discarded."
        )
    if name == "tnull_eval_group_bag_direct_columns_true_no_error":
        return (
            "Use after a child bag has been supplied to discharge only the local "
            "direct-column grouping error branch; it does not prove child safety "
            "or equivalence of successful group bags."
        )
    if name.startswith("list_support_rel_"):
        return (
            "Use to connect row-existence witnesses across relational stages; "
            "do not treat the conclusion as bag equality or multiplicity preservation."
        )
    if name == "formula_conj_acceptance_exact":
        return (
            "Use after proving exact acceptance for both eager children; the "
            "conclusion combines only their `Bool.is_true` decisions, not their "
            "underlying SQL FALSE/UNKNOWN values."
        )
    if name == "formula_exists_acceptance_exact":
        return (
            "Use at one fixed, possibly correlated environment after providing "
            "a child success, agreement of every child success on emptiness, and "
            "absence of every child SQL error."
        )
    if name == "eval_groups_true_outcome_exact":
        return (
            "Use when every reached HAVING decision is exactly TRUE and each of "
            "the four displayed per-group checks is safe; the conclusion is an "
            "ordered map and keeps duplicate group occurrences."
        )
    if name == "eval_groups_acceptance_outcome_exact":
        return (
            "Use after choosing a Boolean `keep` for every reached group and "
            "proving exact HAVING acceptance plus eager aggregate safety; the "
            "result is literally `map projection (filter keep groups)`."
        )
    if name == "bag_filter_congr_on_support":
        return (
            "Use when an environment-dependent row predicate has been proved "
            "equal to another predicate only on represented input rows; input "
            "bags need be semantically bag-equal, not Leibniz-equal."
        )
    if name == "tnull_direct_projection_alias_value":
        return (
            "Use to reduce `dot` at a renamed projection output after proving "
            "the literal direct SELECT item, unique output aliases, and source "
            "attribute presence in the input row."
        )
    if name == "database_conforms_schema_primary_key":
        return (
            "Use after selecting one declared table constraint and computing its "
            "primary-key field; it avoids manually replaying the table-conformance "
            "extraction chain."
        )
    if name == "database_conforms_schema_foreign_key_nonnull_referenced":
        return (
            "Use before analyzing an outer join's unmatched branch when the "
            "referencing row belongs to the constrained table and the declared "
            "NOT NULL set covers every foreign-key source column."
        )
    if name == "eval_group_bag_exact_rows_permut_equiv":
        return (
            "Use at a `QExpr_Group` bag reset after characterizing `eval_groups` "
            "for every legal representative and proving the two emitted row "
            "functions permutation-equivalent."
        )
    if name == "query_make_groups_permut_nonempty":
        return (
            "Use when two input row lists represent the same bag and grouping "
            "terms are nonempty; the result compares whole groups semantically."
        )
    if name == "group_filter_map_permutation":
        return (
            "Use after proving both the retained-group decision and emitted row "
            "respect semantic group equality; it composes directly with exact "
            "HAVING acceptance."
        )
    if name == "query_make_groups_constant_nonempty_key":
        return (
            "Use only with a nonempty grouping-term list and one proved key for "
            "every row; retain the literal `rev rows` and prove key runtime safety "
            "separately."
        )
    if name == "formula_pred_acceptance_exact_safe":
        return (
            "Use for `FExpr_Pred` only after proving its authoritative "
            "`first_runtime_error` classifier is `None`; the decision is "
            "`Bool.is_true`, not an equality between SQL FALSE and UNKNOWN."
        )
    if name == "eval_filter_rows_acceptance_exact":
        return (
            "Use after proving `formula_acceptance_exact_at` for every input "
            "occurrence; the result preserves list order and duplicates and "
            "the premise excludes formula errors."
        )
    if name == "query_expr_outcome_equiv_implies_success_bags":
        return (
            "Use to forget successful row order at one environment; the theorem "
            "deliberately drops error observations, so retain a separate error "
            "proof when rebuilding parent outcome equivalence."
        )
    if name in {
        "eval_query_expr_cross_join_error_iff",
        "eval_query_expr_set_error_iff",
    }:
        return (
            "Use to invert or construct the exact parent error schedule; a "
            "right-child error is observable only with the displayed left-success "
            "witness."
        )
    if name == "query_expr_set_outcome_equiv_congr":
        return (
            "Use to lift two local child outcome equivalences through any modeled "
            "set operation; no safety or success premise is required, and sort "
            "mismatch behavior remains authoritative."
        )
    if name == "query_expr_cross_join_outcome_equiv_congr":
        return (
            "Use to lift two local child outcome equivalences through CROSS JOIN; "
            "no safety or success premise is required."
        )
    if name == "query_project_success_bags_safe":
        return (
            "Use after proving scalar SELECT evaluation safe for every row; this "
            "is an exact possible-bag characterization, not an ordered-row result."
        )
    if name == "query_project_bag_congr":
        return "Use to map an existing input `bag_eq` through one fixed projection."
    if name == "query_table_success_bags_functional":
        return "Use as the generic base case for possible-bag functionality of a table."
    if name == "query_cross_join_union_right_success_bags":
        return (
            "Use for right-hand UNION ALL distribution only after proving both "
            "displayed sort equalities and possible-bag functionality of the "
            "duplicated left child."
        )
    if name in {
        "query_expr_cross_join_union_right_equiv_safe",
        "query_expr_cross_join_union_right_outcome_equiv_safe",
    }:
        return (
            "Use after the two sort equalities, duplicated-left functionality, "
            "complete source/target safety, and source-success premises are all "
            "available."
        )
    if name == "query_expr_project_outcome_equiv_congr_safe":
        return (
            "Use to lift a child outcome equivalence at the same environment "
            "through the same SELECT list after proving per-row local safety."
        )
    if name.startswith("tnull_") and name.endswith("_eval_bag_congr"):
        return (
            "Use to transport an already proved child bag equality through this "
            "operator; retain every displayed evaluator premise."
        )
    if name.startswith("tnull_") and name.endswith("_runtime_error_congr"):
        return (
            "Use to transport child runtime-error equality through this operator; "
            "this is not a proof that either side is safe."
        )
    if name.startswith("tnull_") and name.endswith("_runtime_error_none"):
        return (
            "Use to compose explicit no-error premises for this operator; do not "
            "infer a premise merely from successful bag equality."
        )
    if name in {
        "map_left_join_functional_permut",
        "tnull_map_left_join_functional_permut",
    }:
        return (
            "Use when each left occurrence has zero or one accepted right "
            "occurrence and matched and padded rows project to the same direct "
            "left result; semantic permutation preserves duplicate left rows."
        )
    if name in {"map_theta_join_total_functional", "map_left_join_total_functional"}:
        return (
            "Use to replace a projected total-functional join by the exact mapped "
            "left list; duplicate left occurrences and list order are preserved."
        )
    if name == "eval_filter_rows_always_true_iff":
        return (
            "Use only after proving every reached predicate outcome is exactly "
            "`SqlSuccess true3`; errors and UNKNOWN are not covered."
        )
    if "scalar_subquery" in features:
        return (
            "Use after lowering a supported one-column INT32 scalar comparison through "
            "SINGLE_VALUE, to prove empty/singleton safety or the many-row "
            "CardinalityViolation branch."
        )
    if "scalar_subquery_bridge" in features:
        return (
            "Use after the restricted scalar-subquery child has been lowered, to "
            "invert/transport the surrounding quantified comparison without "
            "changing its SQL NULL or error outcome."
        )
    if features & {"outer_join", "semi_join", "anti_join"}:
        return (
            f"Use for goals whose exact QueryJoin kind selects the stated {subject} "
            "branch; do not transfer a branch conclusion to another join kind."
        )
    if is_non_equivalence_law(name):
        return (
            f"Use to close a non-equivalence goal after supplying the exact error or "
            f"mismatch witness required by `{name}`; it does not assume equivalence."
        )
    if "_iff" in name or name.endswith("iff"):
        return f"Use in either direction to invert or construct a goal about {subject}."
    if "equivalence" in features:
        return (
            f"Use to orient, transport, or compose a semantic relation about {subject}."
        )
    if "cardinality" in features or "multiplicity" in features:
        return f"Use when moving from the modeled operator result to a bound, length, or occurrence fact about {subject}."
    if "runtime" in features:
        return f"Use at the successful-outcome/runtime-error boundary for {subject}."
    return (
        f"Use when the goal or a hypothesis matches the `{name}` direction for "
        f"{subject}; do not reverse or strengthen the displayed conclusion."
    )


def has_top_level_implication(statement: str) -> bool:
    """Recognize a proposition premise, excluding `<->` and binder function types."""
    depth = 0
    opening = "([{"
    closing = ")]}"
    for index, character in enumerate(statement[:-1]):
        if character in opening:
            depth += 1
            continue
        if character in closing:
            depth = max(0, depth - 1)
            continue
        if (
            depth == 0
            and statement[index : index + 2] == "->"
            and (index == 0 or statement[index - 1] != "<")
        ):
            return True
    return False


def premises_for(name: str, statement: str, features: frozenset[str]) -> str:
    if name == "eval_join_row_conditions_acceptance_exact":
        return (
            "Supply `join_condition_acceptance_exact_at` for every right-row "
            "occurrence; the conclusion retains list order and duplicate flags."
        )
    if name == "eval_join_conditions_acceptance_exact":
        return (
            "Supply `join_condition_acceptance_exact_at` for every reached pair "
            "from both input lists; the resulting matrix remains row-major."
        )
    if name == "project_join_sources_outcome_exact_map":
        return (
            "Supply exact successful projection for every source occurring in "
            "the source list; do not omit matched, left-padded, or right-padded "
            "constructors that can be reached."
        )
    if name == "eval_join_bag_safe_of_acceptance_projection_exact":
        return (
            "Both universal contracts are mandatory: exact acceptance for every "
            "left/right pair and exact successful projection for every possible "
            "join source.  The conclusion is bag-local and does not establish "
            "child-query safety."
        )
    if name == "tnull_join_condition_pred_acceptance_exact_safe":
        return (
            "Retain the displayed `first_runtime_error ... arguments = None` "
            "premise at the exact joined-row environment; do not replace the "
            "authoritative predicate interpreter or identify FALSE with UNKNOWN."
        )
    if name == "tnull_row_eq_refl":
        return "No premises beyond the displayed row."
    if name == "tnull_row_eq_sym":
        return (
            "Supply the displayed semantic TNull row equality in the forward direction."
        )
    if name == "tnull_row_eq_trans":
        return (
            "Supply both displayed semantic TNull row equalities through the same "
            "intermediate row; do not replace them by Leibniz equality."
        )
    if name in {
        "tnull_select_lookup_some_iff_projected_label",
        "tnull_select_lookup_none_iff_projected_label_absent",
    }:
        return (
            "No alias-uniqueness premise is required: the statement follows the "
            "authoritative first-match SELECT lookup and exact projected-label "
            "membership test."
        )
    if name == "tnull_project_rows_select_columns_success":
        return (
            "The SELECT list must have the displayed direct-column form; the exact "
            "ordered map conclusion does not cover arbitrary scalar expressions."
        )
    if name == "tnull_query_expr_project_select_columns_error_iff":
        return (
            "The projection must have the displayed direct-column form.  Preserve "
            "the exact child error and fixed database/environment in both directions."
        )
    if name == "tnull_eval_group_bag_direct_columns_true_no_error":
        return (
            "Keep all three displayed restrictions: direct-column SELECT, matching "
            "direct grouping keys, and TRUE HAVING.  The theorem starts after a "
            "child input bag is supplied and does not erase child-query errors."
        )
    if name == "formula_conj_acceptance_exact":
        return (
            "Both displayed child exact-acceptance contracts are mandatory "
            "because FormalSQL evaluates the right child eagerly for both AND and OR."
        )
    if name == "formula_exists_acceptance_exact":
        return (
            "Retain child-success inhabitation, universal agreement on "
            "`rows_empty_decision`, the fixed environment, and exclusion of every error."
        )
    if name == "eval_groups_true_outcome_exact":
        return (
            "For every reached group retain SELECT aggregate safety, HAVING "
            "aggregate safety, exact TRUE acceptance, and scalar SELECT safety; "
            "do not replace the resulting list map by a bag or set."
        )
    if name == "eval_groups_acceptance_outcome_exact":
        return (
            "For every reached group retain SELECT and HAVING aggregate safety "
            "and exact acceptance/no-error evidence; scalar SELECT safety is "
            "mandatory exactly when `keep group = true`."
        )
    if name == "bag_filter_congr_on_support":
        return (
            "Retain input `bag_eq`, positive left multiplicity, semantic tuple "
            "equality, and cross-predicate agreement; no equality is required "
            "outside the represented left support."
        )
    if name == "tnull_direct_projection_alias_value":
        return (
            "The displayed direct `source -> target` item and output uniqueness "
            "are mandatory; source presence prevents lookup from falling through "
            "to the outer environment."
        )
    if name == "database_conforms_schema_primary_key":
        return (
            "Retain database conformance, membership of the exact table constraint, "
            "and its exact `constraint_primary_key = Some key` metadata equation."
        )
    if name == "database_conforms_schema_foreign_key_nonnull_referenced":
        return (
            "Retain exact constraint and row membership, foreign-key membership, "
            "and inclusion of all referencing columns in the NOT NULL declaration; "
            "nullable MATCH SIMPLE keys are deliberately excluded."
        )
    if name == "eval_group_bag_exact_rows_permut_equiv":
        return (
            "Both exact contracts quantify over every bag representative and "
            "include group-key safety; the cross-representative output permutation "
            "premise may not be weakened to support equality."
        )
    if name == "query_make_groups_permut_nonempty":
        return (
            "The nonempty grouping-term premise is mandatory because the global "
            "empty grouping set has distinct empty-input semantics."
        )
    if name == "group_filter_map_permutation":
        return (
            "Supply semantic-equality compatibility for both `keep` and `emit`; "
            "the conclusion is occurrence-preserving permutation, not set equality."
        )
    if name == "query_make_groups_constant_nonempty_key":
        return (
            "The grouping terms must be nonempty and every input row must have "
            "the displayed key; the nonempty result is exactly `[rev rows]`."
        )
    if name == "formula_pred_acceptance_exact_safe":
        return (
            "The displayed `first_runtime_error ... arguments = None` premise "
            "is mandatory; retain the authoritative predicate interpreter and "
            "use `Bool.is_true` only for filter acceptance."
        )
    if name == "eval_filter_rows_acceptance_exact":
        return (
            "Supply the displayed per-row `formula_acceptance_exact_at` "
            "contract, including its successful observation and no-error "
            "components; do not replace `List.filter` by a set abstraction."
        )
    if name == "query_expr_outcome_equiv_implies_success_bags":
        return (
            "Supply the exact fixed-environment child outcome equivalence; this "
            "conclusion preserves successful multiplicity but intentionally does "
            "not carry the error relation."
        )
    if name in {
        "eval_query_expr_cross_join_error_iff",
        "eval_query_expr_set_error_iff",
    }:
        return (
            "Retain the existential successful left observation in the right-error "
            "arm; right errors do not bypass a left error-only execution."
        )
    if name == "query_expr_set_outcome_equiv_congr":
        return (
            "Supply both displayed child outcome equivalences.  Do not assume set "
            "sort compatibility: matching sort-mismatch outcomes are preserved."
        )
    if name == "query_expr_cross_join_outcome_equiv_congr":
        return (
            "Supply both displayed child outcome equivalences; no runtime-safety "
            "or successful-outcome premise may be silently added or inferred."
        )
    if name == "query_project_success_bags_safe":
        return (
            "Prove the displayed SELECT-list runtime-error equation for every row; "
            "respect `bag_eq` and duplicate multiplicity in both directions."
        )
    if name == "query_project_bag_congr":
        return "Supply the displayed input `bag_eq`; the environment and SELECT list stay fixed."
    if name == "query_table_success_bags_functional":
        return "Supply two possible successful bags for the same environment, outputs, and table."
    if name == "query_cross_join_union_right_success_bags":
        return (
            "Both set-operation sort equalities and pairwise possible-bag "
            "functionality of the duplicated left child are mandatory; UNION is "
            "multiplicity-preserving UNION ALL here."
        )
    if name in {
        "query_expr_cross_join_union_right_equiv_safe",
        "query_expr_cross_join_union_right_outcome_equiv_safe",
    }:
        return (
            "Retain both sort equalities, duplicated-left bag functionality, "
            "source and target safety, and the source-success witness."
        )
    if name == "query_expr_project_outcome_equiv_congr_safe":
        return (
            "Supply the fixed-environment child outcome equivalence plus "
            "SELECT-list safety for every row; ordered output and errors remain observable."
        )
    if name in {
        "map_left_join_functional_permut",
        "tnull_map_left_join_functional_permut",
    }:
        return (
            "Retain both matched and padded projection equalities and the "
            "per-left at-most-one bound.  No foreign-key totality premise is "
            "required; the conclusion is occurrence-preserving permutation."
        )
    notes: list[str] = []
    if has_top_level_implication(statement):
        notes.append("every explicit antecedent (`->`) in the declaration is required")
    if "scalar_subquery" in features:
        notes.append(
            "the law is for `AggregateSingleValueInt32`/`single_value_int32`; it does not justify arbitrary scalar-subquery shapes or result types"
        )
    if "scalar_subquery_bridge" in features:
        notes.append(
            "this bridge does not prove that the child is singleton or well typed; retain the lowering's restricted scalar-subquery premises"
        )
    if "runtime" in features:
        notes.append("do not erase or identify runtime errors with NULL/empty success")
    if "null" in features:
        notes.append("preserve the stated SQL NULL/Bool3 hypotheses")
    if "typmod" in features:
        notes.append(
            "retain every typmod/precision/scale and representability condition"
        )
    if "bag" in features or "multiplicity" in features:
        notes.append("respect the exact list-versus-bag and multiplicity boundary")
    if features & {"order_by", "offset", "fetch", "window"}:
        notes.append("retain exact order whenever the declaration observes it")
    if "schema" in features or "integrity" in features:
        notes.append("keep schema/integrity conformance premises explicit")
    if features & {"outer_join", "semi_join", "anti_join"}:
        notes.append(
            "retain every explicit join-kind branch and predicate/projection premise"
        )
    if "subquery" in features:
        notes.append(
            "preserve the displayed environment/correlation and SQL three-valued result"
        )
    if is_non_equivalence_law(name):
        notes.append(
            "supply the displayed runtime-error or mismatch witness; equivalence is the negated conclusion, not a premise"
        )
    elif "equivalence" in features:
        notes.append("supply the declared equivalence/properness relation")
    if not notes:
        return "No premises beyond the quantified variables and typeclass/context assumptions shown in the exact declaration."
    return "; ".join(notes) + "."


def validate_navigation(
    entries: list[dict[str, object]], documents: dict[str, str], index: str
) -> None:
    """Regression checks for the catalog's advertised search routes."""
    if has_top_level_implication("Lemma iff_only : P <-> Q."):
        raise ValueError("premise classifier mistakes `<->` for an antecedent")
    if has_top_level_implication("Lemma function_binder : forall (f : A -> B), P."):
        raise ValueError("premise classifier mistakes a binder type for an antecedent")
    if not has_top_level_implication("Lemma premise : forall x, P x -> Q x."):
        raise ValueError("premise classifier missed a top-level antecedent")

    by_name = {str(entry["name"]): entry for entry in entries}

    def entry(name: str) -> dict[str, object]:
        try:
            return by_name[name]
        except KeyError as error:
            raise ValueError(
                f"navigation regression fixture is missing: {name}"
            ) from error

    def aliases(name: str) -> set[str]:
        return {str(topic).casefold() for topic in entry(name)["topics"]}  # type: ignore[index]

    def routes(name: str) -> set[str]:
        return {str(route) for route in entry(name)["routes"]}  # type: ignore[index]

    def primary(name: str) -> str:
        return str(entry(name)["catalog"])

    def require_route_contract(
        name: str,
        card: str,
        required_routes: set[str],
        maximum_ranks: dict[str, int] | None = None,
    ) -> None:
        if primary(name) != card:
            raise ValueError(f"{name}: expected primary card {card}")
        missing_routes = required_routes - routes(name)
        if missing_routes:
            raise ValueError(
                f"{name}: missing required routes {sorted(missing_routes)}"
            )
        for route, maximum in (maximum_ranks or {}).items():
            observed = int(entry(name)["routeRanks"][route])  # type: ignore[index]
            if observed > maximum:
                raise ValueError(f"{name}: {route} rank {observed} exceeds {maximum}")

    def require(name: str, *topics: str) -> None:
        missing = {topic.casefold() for topic in topics} - aliases(name)
        if missing:
            raise ValueError(
                f"{name}: missing required search aliases {sorted(missing)}"
            )

    def reject(name: str, *topics: str) -> None:
        unexpected = {topic.casefold() for topic in topics} & aliases(name)
        if unexpected:
            raise ValueError(
                f"{name}: false semantic search aliases {sorted(unexpected)}"
            )

    # Audit regressions: slice binders are not COUNT, error constructors are
    # not EXCEPT, runtime is not TIME, and proof-level existentials are not SQL
    # EXISTS/subqueries.
    require("ordered_rows_equiv_skipn", "OFFSET")
    reject("ordered_rows_equiv_skipn", "aggregate", "GROUP BY")
    reject(
        "eval_query_expr_rank_error_iff",
        "set operation",
        "UNION",
        "INTERSECT",
        "EXCEPT",
        "temporal",
        "TIME",
        "NUMERIC",
        "DECIMAL",
    )
    reject("first_runtime_error_some_member", "subquery", "EXISTS", "temporal", "TIME")
    reject("bag_closed_exists", "subquery", "EXISTS")
    reject("related_permut_Forall_transport", "subquery", "ANY/ALL")
    reject("eval_grouping_sets_cons_success_iff", "set operation", "EXCEPT")
    reject("int32_bit_and_fold_partition", "window", "PARTITION BY")
    reject("numeric_sub_self_finite", "cardinality")
    reject("numeric_positive_from_integer_lower_bound", "cardinality")
    reject("string_map_length", "cardinality")

    # The five generic SINGLE_VALUE laws are the proof route for the lowering's
    # restricted INT32 scalar-subquery wrapper.
    scalar_entries = [
        name for name in by_name if "single_value_int32" in name.casefold()
    ]
    if len(scalar_entries) < 5:
        raise ValueError(
            f"expected at least five SINGLE_VALUE catalog laws, found {len(scalar_entries)}"
        )
    for name in scalar_entries:
        require(name, "scalar subquery", "SINGLE_VALUE", "CardinalityViolation")
        reject(name, "temporal", "TIME")
    require(
        "eval_formula_quant_error_iff",
        "scalar subquery",
        "SINGLE_VALUE",
        "CardinalityViolation",
    )
    require("eval_formula_quant_success_iff", "scalar subquery")
    require("eval_formula_quant_subquery_congr", "scalar subquery")

    # One generic kind-indexed join theorem must be reachable from every public
    # SQL spelling advertised in the index.
    join_route = "query_join_sources_length_le"
    require(join_route, "outer join", "semi join", "anti join")

    # Declaration-level routing must expose the generic exact-outcome API
    # without copying statements between cards. Generated-instance
    # admissibility is intentionally not a route.
    ordered_outcome = "query_expr_outcome_equiv_of_eval_iff"
    if primary(ordered_outcome) != "runtime-verification-rewrite.md":
        raise ValueError(
            f"{ordered_outcome}: generic OrderedQueryFacts outcome API is misrouted"
        )
    if not {"outcome", "runtime"} <= routes(ordered_outcome):
        raise ValueError(f"{ordered_outcome}: missing outcome/runtime cross-route")
    grouped_facade = "tnull_eval_groups_having_key_conj_filter_exact"
    if primary(grouped_facade) != "aggregate-grouping.md" or not {
        "facade",
        "grouping",
    } <= routes(grouped_facade):
        raise ValueError(f"{grouped_facade}: grouped facade route regressed")
    predicate_exact = "formula_pred_acceptance_exact_safe"
    if primary(predicate_exact) != "relational-algebra.md" or not {
        "runtime",
        "filter",
        "scalar",
    } <= routes(predicate_exact):
        raise ValueError(f"{predicate_exact}: exact predicate route regressed")
    filter_exact = "eval_filter_rows_acceptance_exact"
    if primary(filter_exact) != "relational-algebra.md" or "filter" not in routes(
        filter_exact
    ):
        raise ValueError(f"{filter_exact}: exact filter route regressed")
    require_route_contract(
        "query_expr_filter_outcome_congr_extensional",
        "relational-algebra.md",
        {"outcome", "runtime", "filter"},
        {"filter": 0, "outcome": 10, "runtime": 10},
    )
    require_route_contract(
        "eval_filter_rows_ordered_outcome_congr",
        "relational-algebra.md",
        {"outcome", "runtime", "filter"},
        {"filter": 8, "outcome": 16, "runtime": 16},
    )
    require_route_contract(
        "interp_predicate_eq_true_is_true_acceptance",
        "null-predicates.md",
        {"filter", "scalar"},
        {"filter": 2, "scalar": 0},
    )
    row_facade = "tnull_row_eq_of_labels_and_values"
    if not {"facade", "projection"} <= routes(row_facade):
        raise ValueError(f"{row_facade}: row-extensionality route regressed")

    # Generic JOIN execution interfaces keep exact Bool3 acceptance, branch
    # projection, and error scheduling explicit.  They must remain reachable
    # without any benchmark/schema-specific route key.
    for row_acceptance in {
        "eval_join_row_conditions_acceptance_exact",
        "eval_join_conditions_acceptance_exact",
    }:
        require_route_contract(
            row_acceptance,
            "relational-algebra.md",
            {"outcome", "runtime", "join"},
            {"join": 6, "outcome": 14, "runtime": 14},
        )
    require_route_contract(
        "project_join_sources_outcome_exact_map",
        "relational-algebra.md",
        {"outcome", "runtime", "projection", "join"},
        {"join": 4, "projection": 4, "outcome": 10, "runtime": 10},
    )
    require_route_contract(
        "eval_join_bag_safe_of_acceptance_projection_exact",
        "relational-algebra.md",
        {"outcome", "runtime", "projection", "join", "bag"},
        {"join": 0, "outcome": 2, "runtime": 2, "projection": 6, "bag": 6},
    )
    require_route_contract(
        "tnull_join_condition_pred_acceptance_exact_safe",
        "runtime-verification-rewrite.md",
        {"facade", "runtime", "filter", "join", "scalar"},
        {"facade": 0, "join": 2, "runtime": 4, "filter": 6},
    )

    for row_law in {"tnull_row_eq_refl", "tnull_row_eq_sym", "tnull_row_eq_trans"}:
        require_route_contract(
            row_law,
            "relational-algebra.md",
            {"facade", "projection"},
            {"facade": 8, "projection": 10},
        )
    for lookup_presence in {
        "tnull_select_lookup_some_iff_projected_label",
        "tnull_select_lookup_none_iff_projected_label_absent",
    }:
        require_route_contract(
            lookup_presence,
            "relational-algebra.md",
            {"facade", "projection"},
            {"facade": 6, "projection": 4},
        )
    require_route_contract(
        "tnull_project_rows_select_columns_success",
        "relational-algebra.md",
        {"facade", "runtime", "projection"},
        {"facade": 4, "runtime": 8, "projection": 2},
    )
    require_route_contract(
        "tnull_query_expr_project_select_columns_error_iff",
        "runtime-verification-rewrite.md",
        {"facade", "outcome", "runtime", "projection"},
        {"facade": 4, "outcome": 4, "runtime": 4, "projection": 6},
    )
    require_route_contract(
        "tnull_eval_group_bag_direct_columns_true_no_error",
        "aggregate-grouping.md",
        {"facade", "outcome", "grouping", "runtime", "bag"},
        {"facade": 2, "outcome": 4, "grouping": 2, "runtime": 2, "bag": 8},
    )

    # Exact acceptance and grouping interfaces must remain reachable through
    # the small routes used by grouped/filter/subquery query shapes.
    require_route_contract(
        "formula_conj_acceptance_exact",
        "aggregate-grouping.md",
        {"grouping", "filter", "scalar"},
        {"grouping": 34, "filter": 38, "scalar": 20},
    )
    require_route_contract(
        "formula_exists_acceptance_exact",
        "subquery-predicates.md",
        {"filter", "runtime", "scalar"},
        {"filter": 38},
    )
    require_route_contract(
        "eval_groups_true_outcome_exact",
        "aggregate-grouping.md",
        {"outcome", "grouping", "runtime"},
        {"grouping": 22},
    )
    require_route_contract(
        "eval_groups_acceptance_outcome_exact",
        "aggregate-grouping.md",
        {"outcome", "grouping", "runtime"},
        {"outcome": 20, "grouping": 18, "runtime": 22},
    )
    require_route_contract(
        "bag_filter_congr_on_support",
        "relational-algebra.md",
        {"filter", "bag"},
        {"filter": 38, "bag": 20},
    )
    for union_bag_law in BAG_ALGEBRA_DECLARATIONS:
        require_route_contract(
            union_bag_law,
            "relational-algebra.md",
            {"bag"},
        )
    require_route_contract(
        "query_expr_project_success_Forall",
        "relational-algebra.md",
        {"projection"},
        {"projection": 8},
    )
    require_route_contract(
        "tnull_projection_envs_eq_of_select_items",
        "relational-algebra.md",
        {"facade", "projection"},
        {"facade": 2, "projection": 0},
    )
    require_route_contract(
        "query_expr_union_success_Forall",
        "relational-algebra.md",
        {"bag"},
        {"bag": 8},
    )
    require_route_contract(
        "query_expr_cross_join_success_Forall",
        "relational-algebra.md",
        {"join", "bag"},
        {"join": 8, "bag": 10},
    )
    for scheduler, required_routes in (
        ("eval_grouping_sets_outcome_Forall2_congr", {"outcome", "grouping", "runtime"}),
        ("eval_grouping_sets_success_fold_iff", {"grouping"}),
        ("eval_grouping_sets_error_prefix_iff", {"grouping", "runtime"}),
    ):
        require_route_contract(
            scheduler,
            "aggregate-grouping.md",
            required_routes,
            {route: 4 for route in required_routes},
        )
    require_route_contract(
        "aggregate_distinct_input_Permutation_of_NoDup_support",
        "aggregate-grouping.md",
        {"grouping", "bag"},
        {"grouping": 6, "bag": 8},
    )
    require_route_contract(
        "partition_keys_Permutation_of_NoDup_support",
        "aggregate-grouping.md",
        {"grouping", "bag"},
        {"grouping": 8, "bag": 10},
    )
    for bag_law, required_routes in (
        ("query_bag_filter_union", {"filter", "bag"}),
        ("query_bag_map_union", {"bag"}),
        ("query_bag_map_congr", {"bag"}),
        ("query_bag_filter_commute", {"filter", "bag"}),
        ("query_bag_filter_map_fusion", {"filter", "bag"}),
        ("query_bag_map_pairwise_equiv_of_cardinal", {"bag", "cardinality"}),
        ("query_cross_join_bag_singleton_right_map", {"join", "bag"}),
    ):
        require_route_contract(
            bag_law,
            "relational-algebra.md",
            required_routes,
        )
    require_route_contract(
        "in_rows_acceptance_existsb",
        "subquery-predicates.md",
        {"filter", "join", "scalar"},
        {"filter": 0, "join": 0, "scalar": 2},
    )
    require_route_contract(
        "tnull_direct_projection_alias_value",
        "relational-algebra.md",
        {"facade", "projection"},
        {"facade": 16, "projection": 4},
    )
    require_route_contract(
        "tnull_select_lookup_direct_compose",
        "relational-algebra.md",
        {"facade", "projection"},
        {"facade": 2, "projection": 2},
    )
    require_route_contract(
        "tnull_select_lookup_constant_direct_compose",
        "relational-algebra.md",
        {"facade", "projection"},
        {"facade": 2, "projection": 2},
    )
    require_route_contract(
        "database_conforms_schema_primary_key",
        "schema-integrity.md",
        {"schema"},
        {"schema": 30},
    )
    require_route_contract(
        "query_same_rows_as_conforming_table_present_attribute",
        "cardinality-composition.md",
        {"cardinality", "schema"},
        {"schema": 6},
    )
    require_route_contract(
        "query_expr_table_success_rows_present_conform_attribute",
        "cardinality-composition.md",
        {"cardinality", "schema"},
        {"schema": 2},
    )
    require_route_contract(
        "query_same_rows_as_conforming_table_absent_attribute",
        "cardinality-composition.md",
        {"cardinality", "schema"},
        {"schema": 4},
    )
    require_route_contract(
        "query_expr_table_success_rows_absent_attribute",
        "cardinality-composition.md",
        {"cardinality", "schema"},
        {"schema": 0},
    )
    require_route_contract(
        "database_conforms_schema_foreign_key_nonnull_referenced",
        "schema-integrity.md",
        {"schema"},
        {"schema": 30},
    )
    require_route_contract(
        "eval_group_bag_exact_rows_permut_equiv",
        "aggregate-grouping.md",
        {"grouping", "bag"},
        {"grouping": 8, "bag": 18},
    )
    require_route_contract(
        "tnull_closed_group_sum_numeric_dot_argument_observations_permutation_rows",
        "numeric-derived.md",
        {"grouping", "bag", "scalar"},
        {"grouping": 0},
    )
    require_route_contract(
        "tnull_closed_group_sum_numeric_dot_value_runtime_exact",
        "numeric-derived.md",
        {"grouping", "runtime", "scalar"},
        {"grouping": 2, "runtime": 8},
    )
    require_route_contract(
        "query_make_groups_closed_sum_numeric_dot_outer_sum_value_runtime_exact",
        "numeric-derived.md",
        {"grouping", "runtime", "scalar"},
        {"grouping": 14, "runtime": 18},
    )
    require_route_contract(
        "query_make_groups_permut_nonempty",
        "aggregate-grouping.md",
        {"grouping"},
        {"grouping": 12},
    )
    require_route_contract(
        "query_make_groups_projected_bag_eq_of_support_rel",
        "aggregate-grouping.md",
        {"grouping", "bag"},
        {"grouping": 4, "bag": 6},
    )
    require_route_contract(
        "tnull_direct_columns_group_projection_support_rel",
        "aggregate-grouping.md",
        {"facade", "grouping", "projection", "bag"},
        {"grouping": 6, "projection": 8, "bag": 10},
    )
    require_route_contract(
        "tnull_direct_columns_group_rows_bag_eq_of_projection_support",
        "aggregate-grouping.md",
        {"facade", "grouping", "projection", "bag"},
        {"grouping": 2, "projection": 16, "bag": 2},
    )
    require_route_contract(
        "eval_group_bag_true_projected_support_equiv",
        "aggregate-grouping.md",
        {"outcome", "grouping", "bag"},
        {"outcome": 8, "grouping": 4},
    )
    require_route_contract(
        "query_expr_group_outcome_equiv_of_supported_child_outcomes",
        "aggregate-grouping.md",
        {"outcome", "grouping"},
        {"outcome": 4, "grouping": 4},
    )
    require_route_contract(
        "tnull_direct_columns_group_outcome_equiv_of_projected_support",
        "aggregate-grouping.md",
        {"facade", "outcome", "grouping", "runtime"},
        {"facade": 0, "outcome": 0, "grouping": 0, "runtime": 4},
    )
    require_route_contract(
        "list_support_rel_compose",
        "relational-algebra.md",
        {"bag"},
        {"bag": 8},
    )
    require_route_contract(
        "list_support_rel_map_left_with_witness",
        "relational-algebra.md",
        {"projection", "bag"},
        {"projection": 14, "bag": 16},
    )
    require_route_contract(
        "group_filter_map_permutation",
        "aggregate-grouping.md",
        {"grouping", "filter", "bag"},
        {"grouping": 14},
    )
    require_route_contract(
        "query_canonical_rows_length",
        "cardinality-composition.md",
        {"grouping", "cardinality"},
        {"grouping": 16, "cardinality": 28},
    )
    require_route_contract(
        "query_make_groups_constant_nonempty_key",
        "aggregate-grouping.md",
        {"grouping"},
        {"grouping": 24},
    )

    # Fixed-environment bag-reset congruence retains exact child-error order;
    # neither set sort mismatch nor an error-only child is filtered away.
    require_route_contract(
        "query_expr_outcome_equiv_implies_success_bags",
        "relational-algebra.md",
        {"outcome", "runtime", "bag"},
        {"bag": 22},
    )
    require_route_contract(
        "eval_query_expr_set_error_iff",
        "runtime-verification-rewrite.md",
        {"runtime"},
    )
    require_route_contract(
        "eval_query_expr_cross_join_error_iff",
        "runtime-verification-rewrite.md",
        {"runtime", "join"},
    )
    require_route_contract(
        "query_expr_set_outcome_equiv_congr",
        "runtime-verification-rewrite.md",
        {"outcome", "runtime"},
    )
    require_route_contract(
        "query_expr_cross_join_outcome_equiv_congr",
        "runtime-verification-rewrite.md",
        {"outcome", "runtime", "join"},
        {"join": 22},
    )

    # Projection/UNION ALL interfaces expose the correct bag layer while the
    # exact safe assembly rules remain on the runtime/outcome card.
    require_route_contract(
        "query_project_success_bags_safe",
        "relational-algebra.md",
        {"runtime", "projection", "bag"},
        {"projection": 22},
    )
    require_route_contract(
        "query_expr_project_bag_closed_safe",
        "runtime-verification-rewrite.md",
        {"runtime", "projection", "bag"},
        {"projection": 2, "bag": 6},
    )
    require_route_contract(
        "query_expr_filter_bag_closed_exact",
        "relational-algebra.md",
        {"filter", "bag"},
        {"filter": 2, "bag": 6},
    )
    require_route_contract(
        "query_project_bag_congr",
        "relational-algebra.md",
        {"projection", "bag"},
    )
    require_route_contract(
        "query_table_success_bags_functional",
        "relational-algebra.md",
        {"bag"},
        {"bag": 24},
    )
    require_route_contract(
        "query_cross_join_union_right_success_bags",
        "relational-algebra.md",
        {"join", "bag"},
        {"join": 22},
    )
    for distribution in {
        "query_expr_cross_join_union_right_equiv_safe",
        "query_expr_cross_join_union_right_outcome_equiv_safe",
    }:
        require_route_contract(
            distribution,
            "runtime-verification-rewrite.md",
            {"outcome", "runtime", "join", "bag"},
            {"join": 22},
        )
    require_route_contract(
        "query_expr_project_outcome_equiv_congr_safe",
        "runtime-verification-rewrite.md",
        {"outcome", "runtime", "projection"},
        {"projection": 22},
    )

    for value in entries:
        value_routes = list(value["routes"])  # type: ignore[arg-type]
        route_ranks = dict(value["routeRanks"])  # type: ignore[arg-type]
        if value["semanticDomain"] != value["catalog"]:
            raise ValueError(f"{value['name']}: semantic/catalog domains disagree")
        if value["sourceDomain"] not in DOMAINS:
            raise ValueError(f"{value['name']}: unknown source domain")
        if value_routes != [route for route in ROUTES if route in value_routes]:
            raise ValueError(f"{value['name']}: cross-routes are not deterministic")
        if set(value_routes) != set(route_ranks):
            raise ValueError(f"{value['name']}: route/rank keys disagree")
        if int(value["rank"]) != min(route_ranks.values(), default=100):
            raise ValueError(f"{value['name']}: aggregate rank disagrees with routes")
        if "admissibility" in value_routes:
            raise ValueError(
                f"{value['name']}: instance admissibility leaked into catalog"
            )
        if "admissible" in identifier_tokens(str(value["name"])) and value_routes:
            raise ValueError(
                f"{value['name']}: admissibility constructor entered ranked navigation"
            )
    empty_routes = [
        route
        for route in ROUTES
        if not any(route in value["routes"] for value in entries)  # type: ignore[operator]
    ]
    if empty_routes:
        raise ValueError(f"empty semantic cross-routes: {empty_routes}")

    searchable = index + "\n" + "\n".join(documents.values())
    if "Provides a direct compositional bridge" in searchable:
        raise ValueError("catalog retained a generic fallback summary")
    if "Apply to a goal with the declaration's displayed head operator" in searchable:
        raise ValueError("catalog retained a generic fallback applicability sentence")

    for phrase in (
        "outer join",
        "semi join",
        "anti join",
        "scalar subquery",
        "SINGLE_VALUE",
        "CardinalityViolation",
    ):
        if phrase.casefold() not in searchable.casefold():
            raise ValueError(f"advertised catalog search has no result: {phrase}")

    # Synthetic classifier fixtures keep future regex changes from reintroducing
    # the four substring/binder bugs even if declaration names later move.
    false_features = semantic_features(
        "ordered-observation.md",
        "OrderedQueryFacts.v",
        "runtime_slice_helper",
        "Lemma runtime_slice_helper : forall count, exists witness, "
        "DataException = DataException.",
    )
    forbidden = {"aggregate", "set_operation", "subquery", "temporal"}
    leaked = false_features & forbidden
    if leaked:
        raise ValueError(f"token-aware classifier regression: {sorted(leaked)}")

    join_features = semantic_features(
        "relational-algebra.md",
        "RelationalAlgebraFacts.v",
        "kind_bound",
        "Lemma kind_bound : QueryJoinLeft = QueryJoinFull /\\ "
        "QueryJoinSemi = QueryJoinAnti.",
    )
    required_join_features = {"outer_join", "semi_join", "anti_join"}
    if not required_join_features <= join_features:
        raise ValueError(
            "constructor-aware join routing regression: "
            f"{sorted(required_join_features - join_features)}"
        )

    union_features = semantic_features(
        "relational-algebra.md",
        "NumericRegroupFacts.v",
        "query_set_union_occurrence_exact",
        "Lemma query_set_union_occurrence_exact : forall left right, "
        "query_set_bag Union left right = query_set_bag Union left right.",
    )
    required_union_features = {"set_operation", "set_union"}
    if not required_union_features <= union_features or union_features & {
        "set_intersection",
        "set_difference",
    }:
        raise ValueError(
            "set-operation kind routing regression: "
            f"{sorted(union_features)}"
        )

    if len(index.encode("utf-8")) > MAX_INDEX_BYTES:
        raise ValueError("catalog index compactness regression")
    if "ProofAgentFacade.v" not in index or "OrderedQueryFacts.v" not in index:
        raise ValueError("compact outcome decision route omits a generic source module")


def source_domain(module: str) -> tuple[str, dict[str, object]]:
    matches = [
        (filename, domain)
        for filename, domain in DOMAINS.items()
        if module in domain["modules"]  # type: ignore[operator]
    ]
    if len(matches) != 1:
        raise ValueError(
            f"{module}: expected one semantic domain, found {len(matches)}"
        )
    return matches[0]


def build_catalog() -> tuple[dict[str, object], dict[str, str], str]:
    entries: list[dict[str, object]] = []
    by_domain: dict[str, list[dict[str, object]]] = {name: [] for name in DOMAINS}
    seen: set[str] = set()
    normalized_statements: dict[str, str] = {}
    for path in sorted(THEORIES.glob("*.v")):
        source_domain_name, _ = source_domain(path.name)
        for raw in extract_declarations(path):
            name = str(raw["name"])
            if name in seen:
                raise ValueError(f"duplicate public declaration name: {name}")
            if CASE_SPECIFIC_NAME.search(name):
                raise ValueError(f"case-specific public declaration name: {name}")
            statement = str(raw["statement"])
            if CASE_SPECIFIC_STATEMENT.search(statement):
                raise ValueError(
                    f"case-specific public declaration statement: {name}"
                )
            seen.add(name)
            normalized = re.sub(
                rf"\b{re.escape(name)}\b",
                "<declaration-name>",
                statement,
                count=1,
            )
            if normalized in normalized_statements:
                raise ValueError(
                    f"duplicate public declaration statement: {normalized_statements[normalized]} and {name}"
                )
            normalized_statements[normalized] = name
            source_features = semantic_features(
                source_domain_name, path.name, name, statement
            )
            domain_name = declaration_domain(
                source_domain_name, path.name, name, source_features
            )
            features = semantic_features(domain_name, path.name, name, statement)
            topics = topics_for(domain_name, features)
            routes = semantic_routes(domain_name, path.name, name, features)
            route_ranks = {
                route: route_rank(route, domain_name, path.name, str(raw["kind"]), name)
                for route in routes
            }
            entry = {
                "name": name,
                "kind": raw["kind"],
                "source": raw["source"],
                "line": raw["line"],
                "sourceDomain": source_domain_name,
                "semanticDomain": domain_name,
                "catalog": domain_name,
                "routes": list(routes),
                "routeRanks": route_ranks,
                "rank": min(route_ranks.values(), default=100),
                "summary": summary_for(name, domain_name, features),
                "topics": topics,
                "statement": statement,
            }
            entries.append(entry)
            by_domain[domain_name].append(entry)

    counts = {name: len(values) for name, values in by_domain.items()}
    if any(count == 0 for count in counts.values()):
        raise ValueError(f"empty semantic catalog domain: {counts}")

    documents: dict[str, str] = {}
    for filename, domain in DOMAINS.items():
        values = by_domain[filename]
        source_modules = sorted({Path(str(value["source"])).name for value in values})
        lines = [
            f"# {domain['title']}",
            "",
            f"Route here for: {domain['route']}.",
            "",
            f"This focused catalog contains {len(values)} declarations routed at declaration granularity from "
            + ", ".join(f"`{module}`" for module in source_modules)
            + ". Source declarations are authoritative; every statement below is verbatim and has no proof body.",
            "",
        ]
        for entry in values:
            source = str(entry["source"])
            line = int(entry["line"])
            module = Path(source).name
            statement = str(entry["statement"])
            topics = list(entry["topics"])
            features = semantic_features(
                filename, module, str(entry["name"]), statement
            )
            cross_index = (
                ", ".join(
                    f"`{route}` (rank {entry['routeRanks'][route]})"  # type: ignore[index]
                    for route in entry["routes"]  # type: ignore[union-attr]
                )
                or "primary card only"
            )
            lines.extend(
                [
                    f"## `{entry['name']}`",
                    "",
                    f"Source: [`{source}:{line}`](../{module}#L{line})",
                    "",
                    f"Purpose/direction: {entry['summary']}",
                    "",
                    f"Applicability: {applicability_for(str(entry['name']), filename, features)}",
                    "",
                    f"Important premises: {premises_for(str(entry['name']), statement, features)}",
                    "",
                    f"Cross-index: {cross_index}",
                    "",
                    "Search aliases: " + ", ".join(f"`{topic}`" for topic in topics),
                    "",
                    "```rocq",
                    statement,
                    "```",
                    "",
                ]
            )
        documents[filename] = "\n".join(lines).rstrip() + "\n"

    index_lines = [
        "# FormalSQL reusable lemma catalog",
        "",
        "This is a compact navigation index. The Rocq source is authoritative; `manifest.json` contains the exact declaration statements plus deterministic primary-domain, cross-route, and route-rank metadata. Lower rank means a better first read.",
        "",
        "Do not open a whole domain card. Pick one route, take at most eight ranked results, then open only the exact declaration block in its primary card (or its authoritative source line). The catalog is not an admissibility prover: use the generated `Queries.v` admissibility certificates for the concrete instance.",
        "",
        "## Fast routes",
        "",
    ]
    for route in INDEX_PREVIEW_ROUTES:
        route_spec = ROUTES[route]
        index_lines.extend(
            [
                f"### `{route}` — {route_spec['title']}",
                "",
                str(route_spec["description"]).capitalize() + ".",
                "",
                "| Rank | Declaration | Primary card |",
                "|---:|---|---|",
            ]
        )
        for entry in ranked_entries_for_route(entries, route)[:INDEX_PREVIEW_PER_ROUTE]:
            index_lines.append(
                f"| {entry['routeRanks'][route]} | `{entry['name']}` | "  # type: ignore[index]
                f"[{entry['catalog']}]({entry['catalog']}) |"
            )
        index_lines.append("")
    index_lines.extend(
        [
            "## Decision tree",
            "",
            "1. For an error-preserving query goal, inspect the ranked `facade` results and then `outcome`; this cross-index includes generic bridges from `ProofAgentFacade.v` and `OrderedQueryFacts.v`.",
            "2. For GROUP BY/HAVING or SINGLE_VALUE, inspect `grouping`; prefer a facade wrapper before lower-level grouping internals.",
            "3. For a separate safety premise, inspect `runtime`; do not identify a runtime error with NULL or empty success.",
            "4. For the smallest differing relational operator, use `projection`, `filter`, `join`, `bag`, `ordered`, or `cardinality` through the bounded query below.",
            "5. For a scalar or schema obligation, use `scalar` or `schema`. Use `query-syntax-bridges.md` only for a tuple/syntax adapter.",
            "",
            "## Primary semantic cards",
            "",
            "| Goal shape / SQL feature | Focused catalog | Declarations |",
            "|---|---|---:|",
        ]
    )
    for filename, domain in DOMAINS.items():
        index_lines.append(
            f"| {domain['route']} | [{filename}]({filename}) | {len(by_domain[filename])} |"
        )
    index_lines.extend(
        [
            "",
            "## Bounded ranked search",
            "",
            "```bash",
            "route=outcome",
            "jq --arg route \"$route\" '[.entries[] | select(.routes | index($route))] | sort_by([.routeRanks[$route], .name]) | .[:8] | map({name, rank: .routeRanks[$route], catalog, source, line, summary})' lemma-catalog/manifest.json",
            "jq --arg re 'projection|cross join' '[.entries[] | select((.topics | join(\" \")) | test($re; \"i\"))] | sort_by([.rank, .name]) | .[:8] | map({name, rank, routes, catalog, source, line})' lemma-catalog/manifest.json",
            "rg -n -A 35 '^## `DECLARATION_NAME`$' lemma-catalog/PRIMARY_CARD.md",
            "```",
            "",
            "Stop after two bounded searches for one obstacle. Keep every NULL, bag/list, order, schema, typmod, collation/timezone, cardinality, and runtime premise visible. Unsupported semantics remain fail-closed.",
            "",
        ]
    )
    manifest = {
        "schemaVersion": 2,
        "ranking": "lower-is-preferred; deterministic public declaration shape only",
        "routes": ROUTES,
        "entries": entries,
    }
    index = "\n".join(index_lines)
    if len(index.encode("utf-8")) > MAX_INDEX_BYTES:
        raise ValueError(
            f"initial catalog index is {len(index.encode('utf-8'))} bytes, exceeding {MAX_INDEX_BYTES}"
        )
    validate_navigation(entries, documents, index)
    return manifest, documents, index


def expected_files() -> dict[Path, str]:
    manifest, documents, index = build_catalog()
    files = {
        CATALOG / "manifest.json": json.dumps(manifest, indent=2, ensure_ascii=False)
        + "\n",
        CATALOG / "INDEX.md": index,
    }
    files.update({CATALOG / name: text for name, text in documents.items()})
    return files


def check(files: dict[Path, str]) -> int:
    errors: list[str] = []
    for path, expected in files.items():
        try:
            actual = path.read_text(encoding="utf-8")
        except FileNotFoundError:
            errors.append(f"missing {path.relative_to(ROOT)}")
            continue
        if actual != expected:
            errors.append(f"stale {path.relative_to(ROOT)}")
    expected_names = {path.name for path in files}
    for path in CATALOG.glob("*.md"):
        if path.name not in expected_names:
            errors.append(f"obsolete catalog document {path.relative_to(ROOT)}")
    if errors:
        for error in errors:
            print(error, file=sys.stderr)
        return 1
    manifest = json.loads(files[CATALOG / "manifest.json"])
    counts = Counter(entry["catalog"] for entry in manifest["entries"])
    print(
        f"catalog current: {len(manifest['entries'])} declarations in {len(counts)} domains"
    )
    return 0


def write(files: dict[Path, str]) -> None:
    CATALOG.mkdir(parents=True, exist_ok=True)
    for path, text in files.items():
        path.write_text(text, encoding="utf-8")
    manifest = json.loads(files[CATALOG / "manifest.json"])
    counts = Counter(entry["catalog"] for entry in manifest["entries"])
    print(f"generated {len(manifest['entries'])} declarations in {len(counts)} domains")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--check", action="store_true", help="fail if generated files differ"
    )
    args = parser.parse_args()
    try:
        files = expected_files()
    except (OSError, ValueError) as error:
        print(f"catalog generation failed: {error}", file=sys.stderr)
        return 1
    if args.check:
        return check(files)
    write(files)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
