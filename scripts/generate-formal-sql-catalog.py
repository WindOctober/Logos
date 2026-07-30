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
import os
import re
import sys
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
THEORIES = ROOT / "theories/FormalSQL"
CATALOG = THEORIES / "catalog"
GENERIC_RENAMING_SOURCES = (
    ROOT / "vendor/FormalSQL/src/data/sql/SqlRenameFacts.v",
    ROOT / "vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v",
)
GENERIC_RENAMING_MODULES = frozenset(path.name for path in GENERIC_RENAMING_SOURCES)
GENERIC_QUERY_CONTEXT_SOURCES = (
    ROOT / "vendor/FormalSQL/src/data/sql/SqlQueryContexts.v",
)
GENERIC_QUERY_CONTEXT_MODULES = frozenset(
    path.name for path in GENERIC_QUERY_CONTEXT_SOURCES
)
QUERY_SYNTAX_SOURCE = ROOT / "vendor/FormalSQL/src/data/sql/SqlQuerySyntax.v"
QUERY_LEAF_CONSTRUCTORS = frozenset({"QExpr_Error", "QExpr_Values", "QExpr_Table"})
GENERIC_QUERY_CONSTRUCTOR_CONGRUENCES = frozenset(
    {
        "query_expr_set_global_typed_congr",
        "query_expr_natural_join_global_typed_congr",
        "query_expr_cross_join_global_typed_congr",
        "query_expr_join_global_typed_congr",
        "query_expr_project_global_typed_congr",
        "query_expr_scalar_project_global_typed_congr",
        "query_expr_row_map_global_typed_congr",
        "query_expr_filter_global_typed_congr",
        "query_expr_scalar_filter_global_typed_congr",
        "query_expr_group_global_typed_congr",
        "query_expr_scalar_group_global_typed_congr",
        "query_expr_grouping_sets_global_typed_congr",
        "query_expr_rank_global_typed_congr",
        "query_expr_window_global_typed_congr",
        "query_expr_distinct_global_typed_congr",
        "query_expr_order_by_global_typed_congr",
        "query_expr_offset_global_typed_congr",
        "query_expr_fetch_global_typed_congr",
    }
)
RELATIONAL_QUERY_CONGRUENCES = frozenset(
    {
        "query_expr_set_global_typed_congr",
        "query_expr_natural_join_global_typed_congr",
        "query_expr_cross_join_global_typed_congr",
        "query_expr_join_global_typed_congr",
        "query_expr_project_global_typed_congr",
        "query_expr_scalar_project_global_typed_congr",
        "query_expr_row_map_global_typed_congr",
        "query_expr_filter_global_typed_congr",
        "query_expr_scalar_filter_global_typed_congr",
        "query_expr_filter_global_typed_acceptance_congr",
    }
)
GROUPING_QUERY_CONGRUENCES = frozenset(
    {
        "query_expr_group_global_typed_congr",
        "query_expr_scalar_group_global_typed_congr",
        "query_expr_grouping_sets_global_typed_congr",
    }
)
ORDERED_QUERY_CONGRUENCES = frozenset(
    {
        "query_expr_rank_global_typed_congr",
        "query_expr_window_global_typed_congr",
        "query_expr_distinct_global_typed_congr",
        "query_expr_order_by_global_typed_congr",
        "query_expr_offset_global_typed_congr",
        "query_expr_fetch_global_typed_congr",
    }
)
GENERIC_QUERY_RENAME_CONSTRUCTOR_THEOREMS = frozenset(
    {
        "QExpr_Error_rename_transport",
        "QExpr_Values_rename_transport",
        "QExpr_Table_rename_transport",
        "QExpr_Set_rename_transport",
        "QExpr_NaturalJoin_rename_transport",
        "QExpr_CrossJoin_rename_transport",
        "QExpr_Join_rename_transport",
        "QExpr_Project_rename_transport",
        "QExpr_RowMap_rename_transport",
        "QExpr_Filter_rename_transport",
        "QExpr_Group_rename_transport",
        "QExpr_GroupingSets_rename_transport",
        "QExpr_Rank_rename_transport",
        "QExpr_Window_rename_transport",
        "QExpr_Distinct_rename_transport",
        "QExpr_OrderBy_rename_transport",
        "QExpr_Offset_rename_transport",
        "QExpr_Fetch_rename_transport",
    }
)
GENERIC_RENAMING_DIMENSION_ENTRIES = frozenset(
    {
        "rename_tuple_identity",
        "rename_tuple_composition",
        "rename_tuple_labels_transport",
        "rename_tuple_lookup_transport",
        "rename_tuple_equivalence_iff",
        "attribute_rename_collision_rejects_injectivity",
        "rows_rename_sound_firstn",
        "rows_rename_sound_skipn",
        "rename_rows_permutation_transport",
        "rename_bag_multiplicity_transport",
        "query_rows_bag_rename_rows",
        "query_bag_source_local_rename_transport",
        "rename_query_outcome_error",
        "query_formula_outcome_rename_compatible_success_iff",
        "query_rename_context_chain_transport",
        "tnull_query_renaming_context_chain_transport",
    }
)
OUTPUT_ONLY_RENAMING_ADAPTER_ENTRIES = frozenset(
    {
        "row_map_rows_output_rename",
        "query_output_rename_adapter_outputs",
        "eval_query_output_rename_adapter_success_iff",
        "eval_query_output_rename_adapter_error_iff",
    }
)
MAPPED_SCHEMA_OBSERVATION_ENTRIES = frozenset(
    {
        "query_mapped_schema_outcome_equiv_mapped_schema",
        "query_rename_transport_under_implies_mapped_schema_outcome_equiv",
    }
)

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
    "renaming-transport.md": {
        "title": "Attribute and query renaming transport",
        "modules": (
            "RenameTransportFacts.v",
            "SqlRenameFacts.v",
            "SqlQueryRenameTransport.v",
        ),
        "topics": (
            "rename",
            "renaming",
            "alias",
            "alpha-renaming",
            "projection",
            "join",
            "transport",
        ),
        "route": "collision-safe tuple, row, outcome, and compositional query alpha-renaming",
        "ownership": (
            "The semantics-generic implementation is owned by "
            "[`SqlRenameFacts.v`](../../../vendor/FormalSQL/src/data/sql/SqlRenameFacts.v) "
            "and [`SqlQueryRenameTransport.v`](../../../vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.v). "
            "`RenameTransportFacts.v` contains only TNull type/typmod adapters and proof-agent entry points; "
            "its query facade accepts a textual `string -> string` name map and cannot change typmods."
        ),
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
            "OuterJoinFilterFacts.v",
            "SemijoinCompositionFacts.v",
            "FilterFkEliminationFacts.v",
            "ProofAgentFacade.v",
        ),
        "topics": ("bag", "list", "occurrence", "projection", "join", "set operation"),
        "route": "bag/list abstraction, multiplicity, filter/project/join/set operators",
    },
    "ordered-observation.md": {
        "title": "Ordered observations and slicing",
        "modules": (
            "OrderedQueryFacts.v",
            "OrderedObservationTransportFacts.v",
        ),
        "topics": ("order by", "ordered observation", "offset", "fetch", "distinct"),
        "route": "exact order and multiplicity, ORDER BY, OFFSET/LIMIT/FETCH, DISTINCT",
    },
    "aggregate-grouping.md": {
        "title": "Aggregates, modifiers, grouping, and aggregate errors",
        "modules": (
            "AggregateRuntimeFacts.v",
            "AggregateOutcomeBridgeFacts.v",
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
        "modules": (
            "SubqueryFacts.v",
            "MembershipCompositionFacts.v",
            "CorrelatedMembershipFacts.v",
            "MembershipJoinCompositionFacts.v",
        ),
        "topics": ("subquery", "EXISTS", "IN", "quantified predicate", "correlation"),
        "route": "EXISTS, IN, ANY/ALL-style quantified predicates, correlated query/formula goals; use aggregate/grouping for SINGLE_VALUE scalar cardinality",
    },
    "schema-integrity.md": {
        "title": "Schema conformance and integrity constraints",
        "modules": ("SchemaCardinality.v", "IntegrityFacts.v", "WitnessFacts.v"),
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
        "modules": (
            "VerificationConditions.v",
            "CountermodelFacts.v",
            "SqlQueryContexts.v",
        ),
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

# Routes are a deliberately small, unranked cross-index over the primary
# semantic cards. A declaration may occur in several routes, but its exact
# statement occurs in only one primary card. Stable pagination exposes every
# matching declaration without copying statements between cards.
ROUTES: dict[str, dict[str, str]] = {
    "renaming": {
        "title": "attribute and query renaming transport",
        "description": "collision-safe tuple, row, outcome, and nested query alpha-renaming",
    },
    "facade": {
        "title": "high-level TNull proof facade",
        "description": "compositional wrappers over generated TNull query terms",
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

CATALOG_PAGE_SIZE = 32
MAX_INDEX_BYTES = 32 * 1024

# A domain anchor describes why the entry lives in its focused document without
# claiming every feature handled by that document.  Entry-specific aliases are
# added below from declaration-name tokens and exact FormalSQL constructors.
DOMAIN_ENTRY_TOPICS: dict[str, str] = {
    "null-predicates.md": "scalar predicate semantics",
    "query-syntax-bridges.md": "query syntax bridge",
    "renaming-transport.md": "renaming transport and alpha-renaming",
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
        "renaming",
        ("rename", "renaming", "alias", "alpha-renaming", "transport"),
    ),
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

# These interfaces encode distinctions that constructor tokens alone cannot
# recover.  In particular, SQL NOT does not complement a filter-acceptance bit
# when the underlying three-valued truth is UNKNOWN.
DECLARATION_TOPIC_ALIASES: dict[str, tuple[str, ...]] = {
    "existsb_support_rel": ("support", "duplicate-insensitive existence"),
    "in_rows_acceptance_support_rel": (
        "IN", "semantic tuple equality", "duplicate-insensitive support"
    ),
    "in_rows_acceptance_append": ("IN", "UNION", "filter acceptance"),
    "formula_truth_exact_acceptance_exact": (
        "exact Bool3 truth", "UNKNOWN", "runtime error"
    ),
    "formula_not_truth_exact": ("SQL NOT", "exact Bool3 truth", "UNKNOWN"),
    "formula_not_acceptance_exact": ("SQL NOT", "UNKNOWN", "filter acceptance"),
    "formula_in_truth_exact": ("IN", "exact Bool3 truth", "UNKNOWN"),
    "formula_in_acceptance_exact": ("IN", "UNKNOWN", "filter acceptance"),
    "formula_not_in_acceptance_exact_of_fixed_truth": (
        "NOT IN", "exact Bool3 truth", "UNKNOWN", "runtime error"
    ),
    "formula_exists_truth_exact": ("EXISTS", "exact Bool3 truth", "empty input"),
    "formula_not_exists_acceptance_exact": (
        "NOT EXISTS", "empty input", "runtime error"
    ),
    "tnull_in_rows_unknown_iff": (
        "IN", "UNKNOWN", "semantic tuple equality", "duplicates"
    ),
    "tnull_in_rows_semantic_cases": (
        "IN", "empty input", "TRUE FALSE UNKNOWN", "duplicates"
    ),
    "tnull_not_in_rows_acceptance_iff_all_false": (
        "NOT IN", "UNKNOWN", "all comparisons FALSE", "empty input"
    ),
    "tnull_not_in_rows_acceptance_iff_no_true_or_unknown": (
        "NOT IN", "anti existence", "NULL marker", "UNKNOWN"
    ),
    "tnull_formula_not_in_accepts_exact_of_all_false": (
        "NOT IN", "correlation", "exact acceptance", "runtime error"
    ),
    "tnull_formula_not_in_rejects_exact_of_true_match": (
        "NOT IN", "TRUE match", "exact rejection", "runtime error"
    ),
    "tnull_formula_not_in_rejects_exact_of_unknown_without_match": (
        "NOT IN", "UNKNOWN without match", "exact rejection", "runtime error"
    ),
    "formula_in_union_all_acceptance_exact": (
        "IN", "UNION ALL", "correlation", "filter acceptance", "runtime error"
    ),
    "query_distinct_rows_support_rel": (
        "DISTINCT", "semantic support", "duplicates", "IN"
    ),
    "in_rows_acceptance_distinct": (
        "IN", "DISTINCT", "filter acceptance", "duplicate-insensitive"
    ),
    "query_join_sources_member_iff": (
        "inner join", "outer join", "semi join", "anti join", "scheduler"
    ),
    "query_join_sources_support_rel": (
        "join", "support", "matched and unmatched branches"
    ),
    "query_join_sources_projected_support_rel": (
        "join", "projection", "reached source", "support"
    ),
    "list_support_rel_filter_transport": (
        "filter", "support", "properness", "reachable representatives"
    ),
    "eval_groups_all_rejected_outcome_exact": (
        "HAVING", "empty result", "evaluation reachability", "runtime error"
    ),
    "tnull_group_count_star_value_runtime_exact": (
        "COUNT star", "group cardinality", "BIGINT overflow", "runtime error"
    ),
    "count_star_value_local_error_exact_of_equal_length": (
        "COUNT star", "equal cardinality", "BIGINT overflow", "local error"
    ),
    "count_star_value_runtime_error_exact_of_equal_observation_length": (
        "COUNT star", "equal cardinality", "runtime error", "observations"
    ),
    "count_star_count_all_nonnull_value_local_error_exact": (
        "COUNT star", "COUNT expression", "NOT NULL", "local error"
    ),
    "count_star_count_all_nonnull_value_runtime_error_exact": (
        "COUNT star", "COUNT expression", "NOT NULL", "runtime error"
    ),
    "formula_pred_outcome_equiv_of_argument_observations": (
        "predicate", "aggregate observation", "Bool3", "runtime error"
    ),
    "tnull_group_count_star_projection_eq_of_equal_length": (
        "COUNT star", "group projection", "equal cardinality", "semantic row equality"
    ),
    "tnull_count_star_group_observation_equiv_of_equal_length": (
        "COUNT star", "group outcome", "HAVING", "equal cardinality"
    ),
    "tnull_count_star_groups_outcome_equiv_of_Forall2_observations": (
        "COUNT star", "group scheduler", "first error", "duplicate groups"
    ),
    "tnull_count_star_groups_true_outcome_equiv_of_Forall2_length": (
        "COUNT star", "TRUE HAVING", "group cardinality", "runtime error"
    ),
    "formula_and_redundant_right_acceptance_exact": (
        "SQL AND", "redundant conjunct", "eager evaluation", "runtime error"
    ),
    "integer_stats_fold_interval_invariant": (
        "aggregate fold", "interval invariant", "integer statistics"
    ),
    "integer_stats_initial_interval_bounds": (
        "aggregate fold", "interval bounds", "integer statistics"
    ),
    "bounded_integer_stats_sum_positive": (
        "aggregate sum", "positivity", "integer statistics"
    ),
    "full_outer_filter_to_left_outer_exact": (
        "full join", "left join", "null rejection", "multiplicity"
    ),
    "left_right_outer_scheduler_swap_Permutation": (
        "left join", "right join", "transpose", "multiplicity"
    ),
    "left_outer_null_reject_to_inner_exact": (
        "left join", "inner join", "null rejection", "multiplicity"
    ),
    "position_rows_from_values": ("position", "window prefix", "duplicates"),
    "position_rows_from_nth_error": ("position", "indexed lookup", "window"),
    "position_rows_from_filter_le_prefix": (
        "position", "prefix", "ROWS frame", "duplicates"
    ),
    "partition_runs_by_compare_exact_well_formed": (
        "partition", "peer ties", "semantic comparator", "window"
    ),
    "rows_key_aligned_length": ("ordered alignment", "order key", "position"),
    "rows_key_aligned_firstn": ("ordered alignment", "FETCH", "ties"),
    "rows_key_aligned_skipn": ("ordered alignment", "OFFSET", "ties"),
    "rows_key_aligned_filter": (
        "ordered alignment", "filter observation", "peer ties"
    ),
    "rows_key_aligned_total_map_transport": (
        "ordered alignment", "total projection", "order key"
    ),
    "prefix_scan_observation_peer_transport": (
        "window prefix", "peer permutation", "filter observation", "ties"
    ),
    "prefix_scan_outcome_peer_transport_iff": (
        "window prefix", "peer permutation", "runtime error", "exact outcome"
    ),
    "partitioned_prefix_scan_observation_peer_transport": (
        "partitioned window", "peer permutation", "prefix reset", "filter observation"
    ),
    "partitioned_prefix_scan_outcome_peer_transport_iff": (
        "partitioned window", "peer permutation", "runtime error", "exact outcome"
    ),
    "order_by_rows_total_map_preimage": (
        "ORDER BY", "total functional map", "legal ties", "multiplicity"
    ),
    "total_map_order_fetch_observation_iff": (
        "ORDER BY", "FETCH", "total functional map", "all legal observations"
    ),
    "total_map_order_fetch_outcome_observation_iff": (
        "ORDER BY", "FETCH", "runtime error", "all legal observations"
    ),
    "query_expr_join_no_error_of_acceptance_projection_exact": (
        "join", "exact acceptance", "projection safety", "runtime error"
    ),
    "partial_semijoin_projection_support_rel": (
        "semijoin", "join projection", "support", "DISTINCT", "duplicates"
    ),
    "exact_extrema_aggregate_support_equiv": (
        "MIN", "MAX", "duplicate-insensitive support", "runtime boundary"
    ),
    "fold_nonempty_support_equiv": (
        "associative commutative idempotent fold", "support", "duplicates"
    ),
    "exact_extrema_aggregate_permutation": (
        "MIN", "MAX", "permutation", "C collation"
    ),
    "exact_extrema_aggregate_duplicate_block": (
        "MIN", "MAX", "idempotence", "duplicate block"
    ),
    "first_runtime_error_duplicate_block": (
        "runtime error", "evaluation order", "duplicate block"
    ),
    "first_observation_error_duplicate_block": (
        "runtime error", "evaluation order", "duplicate block"
    ),
    "exact_extrema_aggregate_runtime_error_duplicate_block": (
        "MIN", "MAX", "runtime error", "duplicate block"
    ),
    "numeric_round_quot_nonnegative_half_ulp": (
        "NUMERIC rounding", "half ULP", "nonnegative"
    ),
    "numeric_pg_div_scale_display_valid": (
        "NUMERIC division", "display scale", "runtime boundary"
    ),
    "numeric_of_scaled_compare_lt": (
        "NUMERIC comparison", "cross scale", "strict order"
    ),
    "numeric_round_to_scale_nonnegative_half_ulp": (
        "NUMERIC rounding", "display scale", "half ULP"
    ),
    "finite_numeric_division_result_rounding": (
        "NUMERIC division", "rounding", "selected scale"
    ),
    "finite_numeric_division_strict_margin": (
        "NUMERIC division", "strict margin", "runtime error"
    ),
    "finite_numeric_division_runtime_error_zero_divisor": (
        "NUMERIC division", "DivisionByZero", "runtime error"
    ),
    "finite_numeric_division_runtime_error_invalid_scale": (
        "NUMERIC division", "NumericValueOutOfRange", "display scale"
    ),
    "finite_numeric_division_runtime_error_missing_result": (
        "NUMERIC division", "NumericValueOutOfRange", "runtime error"
    ),
    "finite_numeric_division_runtime_error_result_out_of_range": (
        "NUMERIC division", "NumericValueOutOfRange", "runtime error"
    ),
    "numeric_sqrt_at_scale_half_ulp_shape": (
        "NUMERIC square root", "half ULP", "midpoint"
    ),
    "numeric_integer_stddev_samp_positive_success_iff": (
        "STDDEV_SAMP", "NUMERIC square root", "selected scale"
    ),
    "int32_avg_numeric_with_scale_success_iff": (
        "AVG", "NUMERIC division", "selected scale"
    ),
    "numeric_of_scaled_compare_not_gt": (
        "NUMERIC comparison", "cross scale", "not greater", "equality preserved"
    ),
    "interp_direct_attribute_in_env_t_absent": (
        "correlation", "environment shadowing", "attribute lookup"
    ),
    "correlated_inner_guard_relation_of_outer_match": (
        "correlation", "inner guard", "outer match", "semantic tuple equality"
    ),
    "NoDupA_bidirectionally_related_members_eq": (
        "semantic support", "duplicate elimination", "NoDupA"
    ),
    "key_unique_self_filter_existsb_exact": (
        "unique key", "self membership", "semantic tuple equality"
    ),
    "primary_key_self_filter_existsb_exact": (
        "primary key", "self membership", "NOT NULL"
    ),
    "tnull_primary_key_self_in_rows_acceptance_exact": (
        "primary key", "IN", "self membership", "UNKNOWN"
    ),
    "tnull_primary_key_self_in_rows_true": (
        "primary key", "IN", "exact TRUE", "correlation"
    ),
    "formula_in_distinct_acceptance_exact_of_inner": (
        "IN", "DISTINCT", "correlation", "runtime error"
    ),
    "query_expr_project_filter_runtime_safe_exact": (
        "filter", "projection", "runtime safety", "evaluation reachability"
    ),
    "join_matched_rows_filter_inputs_exact": (
        "inner join", "filter movement", "multiplicity", "total predicate"
    ),
    "inner_filter_to_input_filters_exact": (
        "inner join", "filter pushdown", "exact list", "properness"
    ),
    "join_left_guard_reached_iff_of_witness": (
        "join", "left guard", "reachability", "self witness"
    ),
    "join_right_guard_reached_iff_of_witness": (
        "join", "right guard", "reachability", "self witness"
    ),
    "join_self_guard_reachability_exact": (
        "self join", "filter movement", "evaluation reachability"
    ),
    "join_matched_rows_member_of_accepted_cell": (
        "join", "accepted cell", "reached occurrence", "multiplicity"
    ),
    "query_filter_success_bags_of_stable_total_acceptance": (
        "filter", "stable total acceptance", "success bag", "non volatility"
    ),
    "query_filter_error_iff_of_stable_total_acceptance": (
        "filter", "stable total acceptance", "runtime error", "reachability"
    ),
    "eval_filter_rows_uniform_error_of_reached_member": (
        "filter", "reached occurrence", "exact error category", "evaluation order"
    ),
    "eval_filter_rows_error_category_of_reached_categories": (
        "filter", "error category", "reached rows", "evaluation order"
    ),
    "eval_filter_rows_success_excludes_reached_exact_error": (
        "filter", "success exclusion", "reached error", "evaluation order"
    ),
    "eval_filter_rows_reached_uniform_error_exact": (
        "filter", "exact error only", "reached occurrence", "runtime outcome"
    ),
    "eval_filter_rows_uniform_error_of_join_witness": (
        "join", "filter", "witness reachability", "exact error category"
    ),
    "eval_filter_rows_uniform_error_of_self_match": (
        "self join", "filter", "self witness", "exact error category"
    ),
    "nonnull_foreign_key_direct_accept_has_middle": (
        "foreign key", "NOT NULL", "middle elimination", "existence"
    ),
    "nonnull_foreign_key_no_middle_rejects_direct": (
        "foreign key", "NOT NULL", "null rejection", "middle elimination"
    ),
    "join_matched_rows_empty_of_rejection": (
        "join", "null rejection", "empty branch", "multiplicity"
    ),
    "middle_padding_downstream_empty": (
        "left join", "NULL padding", "null rejection", "middle elimination"
    ),
    "filtered_payload_erasure_permut": (
        "filter", "payload erasure", "multiplicity", "semantic relation"
    ),
    "query_expr_outcome_equiv_of_shared_exact_error": (
        "exact error only", "error category", "success exclusion", "query outcome"
    ),
}


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


def camel_to_snake(identifier: str) -> str:
    """Convert a closed QExpr constructor suffix to its theorem-name form."""
    return re.sub(r"(?<!^)(?=[A-Z])", "_", identifier).casefold()


def expected_query_constructor_congruences() -> frozenset[str]:
    """Derive the non-leaf congruence family from authoritative query syntax."""
    constructors = frozenset(
        re.findall(
            r"(?m)^[ \t]*\|[ \t]+(QExpr_[A-Za-z][A-Za-z0-9_]*)\b",
            QUERY_SYNTAX_SOURCE.read_text(encoding="utf-8"),
        )
    )
    return frozenset(
        f"query_expr_{camel_to_snake(constructor.removeprefix('QExpr_'))}"
        "_global_typed_congr"
        for constructor in constructors - QUERY_LEAF_CONSTRUCTORS
    )


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

    if domain_name == "renaming-transport.md" or tokens & {
        "rename",
        "renaming",
    }:
        features.add("renaming")
    if name == "tnull_query_renaming_context_chain_transport":
        # This is the generic closure entry point for arbitrarily nested paired
        # query contexts.  Keep attribute-observing operators findable even
        # though their constructors are abstracted behind the context relation.
        features.update(
            ("projection", "join", "grouping", "order_by", "window", "bag")
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
    if name == "tnull_select_columns_lookup_output":
        features.add("projection")
    if name == "tnull_query_expr_project_select_columns_error_iff":
        features.update(("outcome", "projection", "runtime"))
    if "order_by" in normalized_name or has_identifier("QExpr_OrderBy"):
        features.add("order_by")
    if tokens & {"offset", "skipn"} or has_identifier("QExpr_Offset"):
        features.add("offset")
    if tokens & {"fetch", "limit", "firstn"} or has_identifier("QExpr_Fetch"):
        features.add("fetch")
    if (
        module in {"OrderedQueryFacts.v", "OrderedObservationTransportFacts.v"}
        and bool(tokens & {"window", "rank", "partition", "prefix", "peer"})
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
        "query_expr_outcome_equiv",
        "query_expr_global_outcome_equiv",
        "query_expr_global_typed_outcome_equiv",
        "formula_expr_global_outcome_equiv",
        "formula_expr_global_filter_outcome_equiv",
        "formula_expr_global_group_outcome_equiv",
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


def topics_for(
    name: str, domain_name: str, features: frozenset[str]
) -> list[str]:
    topics = [DOMAIN_ENTRY_TOPICS[domain_name]]
    for feature, aliases in FEATURE_TOPIC_ALIASES:
        if feature in features:
            topics.extend(aliases)
    topics.extend(DECLARATION_TOPIC_ALIASES.get(name, ()))
    # Stable, case-insensitive de-duplication keeps aliases compact while the
    # semantic order above preserves all join-kind and scalar-cardinality routes.
    seen: set[str] = set()
    result: list[str] = []
    for topic in topics:
        key = topic.casefold()
        if key not in seen:
            seen.add(key)
            result.append(topic)
    return result


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

    # These two authoritative FormalSQL modules form one theorem layer.  Keep
    # every declaration on its focused card even when a name also mentions a
    # bag, ordered observation, or runtime outcome; cross-routes still expose
    # those secondary uses without hiding the renaming API across cards.
    if module in GENERIC_RENAMING_MODULES:
        return "renaming-transport.md"

    # FormalSQL owns the complete typed-outcome constructor congruence family.
    # Route each operator beside the corresponding Logos proof layer while
    # retaining the arbitrary-context theorem on the runtime/outcome card.
    if module in GENERIC_QUERY_CONTEXT_MODULES:
        if name in RELATIONAL_QUERY_CONGRUENCES or name.startswith(
            ("eval_filter_rows_", "eval_join_")
        ):
            return "relational-algebra.md"
        if name in GROUPING_QUERY_CONGRUENCES or name.startswith(
            ("eval_groups_", "eval_group_bag_")
        ):
            return "aggregate-grouping.md"
        if name in ORDERED_QUERY_CONGRUENCES:
            return "ordered-observation.md"
        return "runtime-verification-rewrite.md"

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

    if module in {"OrderedQueryFacts.v", "OrderedObservationTransportFacts.v"}:
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
    if name in {
        "eval_group_bag_global_true_success_exists",
        "eval_group_bag_global_true_success_bag_unique_if_stable",
    }:
        # Global GROUP BY is the result-producing core of a scalar aggregate
        # subquery, so expose its representative-independent singleton theorem
        # on the scalar route as well as the grouping and bag routes.
        selected.add("scalar")
    if name == "query_canonical_rows_map_factor_permut":
        # This is the semantic boundary used by projection/alias renaming at
        # bag-reset operators, even though its generic name mentions neither
        # one concrete constructor nor one generated rename.
        selected.update(("renaming", "projection", "bag"))
    if module in {"ProofAgentFacade.v", "RenameTransportFacts.v"}:
        selected.add("facade")
    if "renaming" in features:
        selected.add("renaming")
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



def semantic_subject(domain_name: str, features: frozenset[str]) -> str:
    if domain_name == "renaming-transport.md":
        return "collision-safe attribute and query renaming transport"
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
    if name in GENERIC_QUERY_RENAME_CONSTRUCTOR_THEOREMS:
        operator = name.removeprefix("QExpr_").removesuffix("_rename_transport")
        return (
            f"Provides the constructor-local renaming transport theorem for "
            f"`QExpr_{operator}`, preserving mapped schemas and exact successful/error "
            "observations under every displayed semantic side condition."
        )
    if name in OUTPUT_ONLY_RENAMING_ADAPTER_ENTRIES:
        return (
            "Characterizes the output-boundary RowMap adapter that relabels only "
            "successful result tuples and preserves child errors; it is not a full "
            "query alpha-renaming theorem."
        )
    if name in MAPPED_SCHEMA_OBSERVATION_ENTRIES:
        return (
            "Connects constructor-certified transport to exact mapped-schema "
            "observations; this relation alone does not certify renamed operator metadata."
        )
    if name == "tnull_attribute_name_renaming_type_preserving":
        return (
            "Shows that name-only TNull attribute renaming preserves the exact "
            "SQL value type, including every textual, decimal, and temporal typmod."
        )
    if name == "tnull_attribute_name_renaming_value_conforms":
        return (
            "Preserves and reflects TNull value conformance under name-only "
            "attribute renaming, including NULL payloads and constrained types."
        )
    if name == "tnull_rows_name_renaming_type_safe":
        return (
            "Discharges actual successful-row type/typmod safety for every row "
            "under the name-only TNull attribute adapter."
        )
    if name == "tnull_tuple_conforms_sort_renaming_transport":
        return (
            "Transports tuple/schema conformance through name-only renaming under "
            "injectivity on the source sort, rejecting attribute collisions."
        )
    if name in {
        "tnull_rows_renaming_firstn_transport",
        "tnull_rows_renaming_skipn_transport",
    }:
        return (
            "Commutes exact row-wise renaming with the displayed ordered slice, "
            "preserving row order and duplicate occurrences."
        )
    if name == "tnull_query_mapped_schema_outcome_equiv_mapped_schema":
        return (
            "Extracts the ordered name-only mapped output schema from exact TNull observations; "
            "this observational relation is neither full alpha-renaming nor ordinary same-schema equivalence."
        )
    if name == "tnull_query_renaming_context_chain_transport":
        return (
            "Closes a proved name-only renaming transport under an arbitrary list of "
            "paired query contexts, retaining typmods, operator metadata, and outcomes."
        )
    if name == "query_bag_reset_success_permutation_closed":
        return (
            "Establishes concrete-row permutation closure for successful "
            "observations at any constructor classified as a bag reset."
        )
    if name in {
        "query_project_preserves_success_permutation_closed",
        "query_row_map_preserves_success_permutation_closed",
        "query_filter_preserves_success_permutation_closed",
    }:
        operator = {
            "query_project_preserves_success_permutation_closed": "projection",
            "query_row_map_preserves_success_permutation_closed": "row mapping",
            "query_filter_preserves_success_permutation_closed": "filtering",
        }[name]
        return (
            f"Transports concrete-row permutation closure of successful "
            f"observations through pointwise {operator}."
        )
    if name == "query_structural_successes_bag_closed":
        return (
            "Turns the syntax-directed reset/Project/Filter/RowMap certificate "
            "into observation-level BagClosed for successful rows."
        )
    if name == "in_rows_acceptance_existsb":
        return (
            "Reduces only the TRUE-acceptance observation of SQL IN over a row "
            "bag to an ordinary Boolean existence test, retaining the underlying "
            "FALSE/UNKNOWN distinction."
        )
    if name == "existsb_support_rel":
        return (
            "Shows that a Boolean existence observation is invariant under "
            "bidirectional relational support when the tested predicates agree "
            "on related representatives; multiplicity is intentionally ignored."
        )
    if name == "in_rows_acceptance_support_rel":
        return (
            "Transports only SQL IN TRUE-acceptance across duplicate-insensitive "
            "support correspondence under FormalSQL semantic tuple equality."
        )
    if name == "in_rows_acceptance_append":
        return (
            "Distributes SQL IN TRUE-acceptance over appended candidate lists as "
            "Boolean OR without equating the underlying FALSE and UNKNOWN truths."
        )
    if name == "formula_truth_exact_acceptance_exact":
        return (
            "Projects an inhabited, unique exact Bool3 success with no reachable "
            "runtime error to its SQL TRUE-acceptance bit."
        )
    if name == "formula_not_truth_exact":
        return (
            "Transports an inhabited, error-free exact Bool3 observation through "
            "SQL NOT; in particular, UNKNOWN remains UNKNOWN."
        )
    if name == "formula_not_acceptance_exact":
        return (
            "Derives exact acceptance for SQL NOT from the stronger exact-truth "
            "contract, without complementing a FALSE/UNKNOWN acceptance bit."
        )
    if name == "formula_in_truth_exact":
        return (
            "Builds exact tuple-valued IN truth from runtime-safe arguments, an "
            "inhabited child, fixed Bool3 truth across every child success, and no errors."
        )
    if name == "formula_in_acceptance_exact":
        return (
            "Builds exact tuple-valued IN acceptance from pointwise SQL equality "
            "decisions while retaining empty inputs, duplicates, UNKNOWN, and errors."
        )
    if name == "formula_not_in_acceptance_exact_of_fixed_truth":
        return (
            "Builds NOT IN acceptance only from fixed exact IN truth, applying SQL "
            "negation before TRUE projection so UNKNOWN is never accepted."
        )
    if name == "formula_exists_truth_exact":
        return (
            "Builds the exact two-valued EXISTS truth from inhabited child outcomes "
            "that all agree on emptiness and from exclusion of every child error."
        )
    if name == "formula_not_exists_acceptance_exact":
        return (
            "Characterizes NOT EXISTS acceptance as child emptiness while preserving "
            "the fixed correlated environment and excluding every child runtime error."
        )
    if name == "tnull_in_rows_unknown_iff":
        return (
            "Characterizes TNull IN UNKNOWN as at least one UNKNOWN candidate "
            "comparison and no TRUE candidate, over the canonical bag representative."
        )
    if name == "tnull_in_rows_semantic_cases":
        return (
            "Partitions TNull IN into empty/FALSE, TRUE-match, UNKNOWN-without-match, "
            "and nonempty-all-FALSE cases without replacing SQL tuple comparison by Rocq equality."
        )
    if name in {
        "tnull_not_in_rows_acceptance_iff_all_false",
        "tnull_not_in_rows_acceptance_iff_no_true_or_unknown",
    }:
        return (
            "Characterizes TNull NOT IN acceptance by all candidate comparisons being "
            "FALSE, equivalently by absence of both a TRUE match and an UNKNOWN comparison."
        )
    if name in {
        "tnull_formula_not_in_accepts_exact_of_all_false",
        "tnull_formula_not_in_rejects_exact_of_true_match",
        "tnull_formula_not_in_rejects_exact_of_unknown_without_match",
    }:
        return (
            "Lifts the displayed TNull NOT IN semantic case to exact formula acceptance "
            "at one correlated environment, retaining argument and child error premises."
        )
    if name == "formula_in_union_all_acceptance_exact":
        return (
            "Builds exact correlated IN acceptance over UNION ALL as the Boolean OR "
            "of fixed branch decisions while retaining duplicate candidates and requiring "
            "both branch error relations to be empty."
        )
    if name == "query_distinct_rows_support_rel":
        return (
            "Relates every legal DISTINCT output representative bidirectionally to "
            "the input's semantic row support without preserving duplicate counts."
        )
    if name == "in_rows_acceptance_distinct":
        return (
            "Shows SQL IN TRUE-acceptance is unchanged by DISTINCT candidate "
            "elimination while leaving the underlying row multiplicities distinct."
        )
    if name == "query_join_sources_member_iff":
        return (
            "Characterizes scheduler-source membership for every native join kind, "
            "keeping matched, unmatched-left, unmatched-right, semi, and anti "
            "reachability distinct."
        )
    if name == "query_join_sources_support_rel":
        return (
            "Transports bidirectional source support across all six native join "
            "constructors under exact match-decision correspondence."
        )
    if name == "query_join_sources_projected_support_rel":
        return (
            "Lifts all-kind join-source support through reached-only emitters, "
            "without claiming multiplicity, ordering, or runtime-error equivalence."
        )
    if name == "list_support_rel_filter_transport":
        return (
            "Transports bidirectional relational support through two total filters "
            "whose decisions agree only on actually related representatives."
        )
    if name == "eval_groups_all_rejected_outcome_exact":
        return (
            "Characterizes an all-rejected HAVING schedule as exact empty success "
            "while retaining reached SELECT/HAVING aggregate finalization and "
            "excluding HAVING runtime errors."
        )
    if name == "tnull_group_count_star_value_runtime_exact":
        return (
            "Computes one TNull group COUNT-star value and both aggregate/full "
            "runtime checks exactly from the group's mathematical cardinality."
        )
    if name in {
        "count_star_value_local_error_exact_of_equal_length",
        "count_star_value_runtime_error_exact_of_equal_observation_length",
    }:
        return (
            "Shows equal occurrence cardinality gives the same COUNT-star value and "
            "exact BIGINT overflow/error observation, without an in-range premise."
        )
    if name in {
        "count_star_count_all_nonnull_value_local_error_exact",
        "count_star_count_all_nonnull_value_runtime_error_exact",
    }:
        return (
            "Relates COUNT-star to COUNT ALL over an equally long reached expression "
            "list under explicit non-NULL and, for full outcomes, child-safety premises."
        )
    if name == "formula_pred_outcome_equiv_of_argument_observations":
        return (
            "Transports full predicate-formula outcomes from equality of reached "
            "argument values and first runtime errors, retaining FALSE versus UNKNOWN."
        )
    if name == "tnull_group_count_star_projection_eq_of_equal_length":
        return (
            "Derives semantic equality of one-column COUNT-star group projections "
            "from equal group cardinality, independent of the output alias."
        )
    if name == "tnull_count_star_group_observation_equiv_of_equal_length":
        return (
            "Builds one exact COUNT-star group execution relation from equal cardinality "
            "and explicit aggregate/HAVING outcome correspondence."
        )
    if name in {
        "tnull_count_star_groups_outcome_equiv_of_Forall2_observations",
        "tnull_count_star_groups_true_outcome_equiv_of_Forall2_length",
    }:
        return (
            "Lifts pointwise equal-cardinality COUNT-star observations through the "
            "ordered group scheduler, preserving duplicate groups and the first error."
        )
    if name == "formula_and_redundant_right_acceptance_exact":
        return (
            "Eliminates an acceptance-redundant eager right conjunct only after "
            "both sides have exact error-free acceptance and right acceptance is "
            "proved whenever the left guard accepts."
        )
    if name in {
        "integer_stats_fold_interval_invariant",
        "integer_stats_initial_interval_bounds",
    }:
        return (
            "Preserves symbolic lower-sum and upper-square interval bounds through "
            "the exact logical integer-statistics fold."
        )
    if name == "bounded_integer_stats_sum_positive":
        return (
            "Derives strict positivity of the logical integer-statistics sum from "
            "a positive symbolic lower bound and a nonempty fold count."
        )
    if name == "full_outer_filter_to_left_outer_exact":
        return (
            "Rewrites a null-rejecting filter over the three FULL-join scheduler "
            "branches to a LEFT join over the filtered left input, preserving "
            "duplicate occurrences exactly."
        )
    if name == "left_right_outer_scheduler_swap_Permutation":
        return (
            "Shows exact occurrence permutation between LEFT and operand-swapped "
            "RIGHT outer schedulers after transposing both match decisions and "
            "matched-row emission."
        )
    if name == "left_outer_null_reject_to_inner_exact":
        return (
            "Removes exactly the NULL-padded branch of a LEFT outer scheduler "
            "under an explicit rejecting consumer, retaining matched-row filtering "
            "and duplicate occurrences."
        )
    if name in {
        "position_rows_from_values",
        "position_rows_from_nth_error",
        "position_rows_from_filter_le_prefix",
    }:
        return (
            "Characterizes zero-based positions and inclusive prefixes of an "
            "arbitrary occurrence list, preserving empty inputs and duplicate rows."
        )
    if name == "partition_runs_by_compare_exact_well_formed":
        return (
            "Partitions an occurrence list into exact adjacent comparator-equal "
            "runs and proves both concatenation and boundary inequality without "
            "using Rocq equality on SQL rows."
        )
    if name in {
        "rows_key_aligned_length",
        "rows_key_aligned_firstn",
        "rows_key_aligned_skipn",
        "rows_key_aligned_filter",
        "rows_key_aligned_total_map_transport",
    }:
        return (
            "Transports heterogeneous relational order-key alignment through the "
            "displayed positional or total deterministic list consumer."
        )
    if name == "prefix_scan_observation_peer_transport":
        return (
            "Transports the post-filter semantic row observation of a cumulative prefix "
            "scan across every caller-certified adjacent peer permutation."
        )
    if name == "prefix_scan_outcome_peer_transport_iff":
        return (
            "Lifts peer-order prefix-observation transport to exact success/error outcomes "
            "only after the two evaluation schedules' error categories are equated explicitly."
        )
    if name == "partitioned_prefix_scan_observation_peer_transport":
        return (
            "Applies tie-aware prefix-observation transport independently to aligned "
            "partition blocks, resetting the cumulative prefix at each boundary."
        )
    if name == "partitioned_prefix_scan_outcome_peer_transport_iff":
        return (
            "Lifts aligned partition-block peer transport to exact outcome observations "
            "under an explicit equality of the two schedules' runtime-error categories."
        )
    if name == "order_by_rows_total_map_preimage":
        return (
            "Pulls every legal ordered representative of a total mapped bag back to a "
            "source ordering, preserving occurrences even when the map is non-injective."
        )
    if name == "total_map_order_fetch_observation_iff":
        return (
            "Equates all legal ORDER BY/FETCH observations before and after a total "
            "semantic row map whose order-key comparison is preserved and reflected."
        )
    if name == "total_map_order_fetch_outcome_observation_iff":
        return (
            "Adds an explicit exact error relation to total-map ORDER BY/FETCH observation "
            "transport; it does not infer error safety from the successful mapping law."
        )
    if name == "query_expr_join_no_error_of_acceptance_projection_exact":
        return (
            "Rules out every native join error after both children are error-free and every "
            "reached condition and matched/padded projection has one exact success."
        )
    if name == "partial_semijoin_projection_support_rel":
        return (
            "Relates the support of surviving semijoin rows to the support of projected "
            "matching join cells without assuming a functional match; repeated right "
            "matches remain present on the join side."
        )
    if name in {
        "fold_nonempty_support_equiv",
        "exact_extrema_aggregate_permutation",
        "exact_extrema_aggregate_support_equiv",
        "exact_extrema_aggregate_duplicate_block",
    }:
        return (
            "Makes the displayed associative/commutative/idempotent fold or exact "
            "integral, NUMERIC, and C-collation textual extrema invariant under "
            "permutation, support equivalence, or repeated input blocks."
        )
    if name in {
        "first_runtime_error_duplicate_block",
        "first_observation_error_duplicate_block",
        "exact_extrema_aggregate_runtime_error_duplicate_block",
    }:
        return (
            "Shows that repeating one reached input block preserves its left-biased "
            "first runtime error, and packages that boundary for exact extrema aggregates."
        )
    if name in {
        "numeric_round_quot_nonnegative_half_ulp",
        "numeric_round_to_scale_nonnegative_half_ulp",
        "numeric_sqrt_at_scale_half_ulp_shape",
    }:
        return (
            "Exposes the exact nonnegative PostgreSQL NUMERIC rounding or square-"
            "root midpoint branch together with its half-unit fixed-point bound."
        )
    if name in {
        "numeric_pg_div_scale_display_valid",
        "numeric_of_scaled_compare_lt",
        "finite_numeric_division_result_rounding",
        "finite_numeric_division_strict_margin",
    }:
        return (
            "Connects PostgreSQL-selected NUMERIC division scale and rounding to "
            "a fixed-point strict comparison, retaining the explicit half-ULP margin."
        )
    if name in {
        "finite_numeric_division_runtime_error_zero_divisor",
        "finite_numeric_division_runtime_error_invalid_scale",
        "finite_numeric_division_runtime_error_missing_result",
        "finite_numeric_division_runtime_error_result_out_of_range",
    }:
        return (
            "Classifies the displayed finite NUMERIC division failure as the exact "
            "PostgreSQL DivisionByZero or NumericValueOutOfRange category."
        )
    if name in {
        "numeric_integer_stddev_samp_positive_success_iff",
        "int32_avg_numeric_with_scale_success_iff",
    }:
        return (
            "Decomposes the positive/nonempty integral aggregate finalizer into its "
            "exact selected-scale NUMERIC division and, for STDDEV_SAMP, square-root path."
        )
    if name == "numeric_of_scaled_compare_not_gt":
        return (
            "Transports a non-strict cross-scale coefficient bound to a NUMERIC "
            "comparison that cannot be Gt while preserving the observable Eq case."
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
    if name == "tnull_select_lookup_direct_compose_interp_value":
        return (
            "Composes two first-match direct projection lookups while retaining "
            "the original row-extended expression value, including correlated fallback."
        )
    if name == "tnull_projection_rows_eq_of_output_values":
        return (
            "Builds semantic equality of two projected rows from equality of their "
            "output-label sets and every observable projected cell."
        )
    if name == "tnull_direct_projection_fusion_row_eq":
        return (
            "Fuses one direct projection with two direct projections from exact "
            "source-to-middle-to-target first-match lookup chains."
        )
    if name == "tnull_select_columns_lookup_output":
        return (
            "Computes the exact first-match lookup of every present SelectColumns "
            "output without requiring output uniqueness."
        )
    if name == "tnull_select_columns_projection_fusion_row_eq":
        return (
            "Fuses direct-column single and double projections from final-label "
            "set equality and coverage of every outer label by the inner projection."
        )
    if name == "tnull_project_fusion_success_bag_contract_of_row_eq":
        return (
            "Lifts a total single-versus-double projection row law to the named "
            "reachable-child-bag fusion contract without changing multiplicities."
        )
    if name == "query_project_success_bags_fusion_safe":
        return (
            "Uses three locally safe projections and their reachable-bag fusion "
            "contract to equate the possible successful bags of one and two Projects."
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
    if name == "eval_groups_global_true_outcome_exact":
        return (
            "Specializes exact TRUE-HAVING group execution to SQL global "
            "aggregation, including the singleton empty-input group."
        )
    if name == "query_canonical_rows_map_factor_permut":
        return (
            "Transports a projection or rename through canonical bag-row "
            "selection up to semantic permutation, without exposing the bag "
            "implementation's concrete sorting algorithm."
        )
    if name == "eval_group_bag_global_true_success_exists":
        return (
            "Constructs a successful global-aggregate bag outcome from explicit "
            "aggregate-finalization and scalar-projection runtime safety."
        )
    if name == "eval_group_bag_global_true_success_bag_unique_if_stable":
        return (
            "Lifts safe global aggregation through the bag reset and proves a "
            "representative-independent singleton result when the projection is "
            "explicitly permutation-stable."
        )
    if name == "group_projection_permutation_stable":
        return (
            "Defines the semantic side condition under which a group projection "
            "is invariant under permutation of its group members."
        )
    if name == "rows_permut_implies_bag_eq":
        return (
            "Converts semantic row permutation into equality of finite row bags, "
            "the converse of the reset-boundary occurrence bridge."
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
    if name == "interp_direct_attribute_in_env_t_absent":
        return (
            "Shows that an attribute absent from the current row of an environment "
            "extension is resolved from the retained outer environment."
        )
    if name == "correlated_inner_guard_relation_of_outer_match":
        return (
            "Transports one reached outer-to-inner semantic match to the reversed "
            "correlated guard while retaining row presence, shadowing, and symmetry premises."
        )
    if name == "NoDupA_bidirectionally_related_members_eq":
        return (
            "Identifies two represented occurrences only after NoDupA and both "
            "directions of the caller-supplied semantic relation are proved."
        )
    if name in {
        "key_unique_self_filter_existsb_exact",
        "primary_key_self_filter_existsb_exact",
    }:
        return (
            "Computes filtered self-membership from an actual semantic self witness "
            "and occurrence-sensitive key uniqueness; the primary-key form also exposes NOT NULL."
        )
    if name in {
        "tnull_primary_key_self_in_rows_acceptance_exact",
        "tnull_primary_key_self_in_rows_true",
    }:
        return (
            "Establishes TNull primary-key self-IN TRUE-acceptance from an actual "
            "tuple-comparison witness, key reflection, and the complete projected NOT NULL fact."
        )
    if name == "formula_in_distinct_acceptance_exact_of_inner":
        return (
            "Lifts an exact correlated IN acceptance contract through DISTINCT "
            "without claiming equality of the complete FALSE/UNKNOWN Bool3 result."
        )
    if name == "query_expr_project_filter_runtime_safe_exact":
        return (
            "Composes child, filter-formula, and reached-projection safety into exact "
            "runtime safety for a Project over Filter without inferring safety from bags."
        )
    if name in {
        "join_matched_rows_filter_inputs_exact",
        "inner_filter_to_input_filters_exact",
    }:
        return (
            "Factors stable total Boolean join acceptance into input guards and a "
            "residual predicate while preserving the exact output list and duplicate occurrences."
        )
    if name in {
        "join_left_guard_reached_iff_of_witness",
        "join_right_guard_reached_iff_of_witness",
        "join_self_guard_reachability_exact",
    }:
        return (
            "Relates prefilter and post-join guard reachability only under the displayed "
            "match witness; the self form supplies both directions for a reflexive match."
        )
    if name == "join_matched_rows_member_of_accepted_cell":
        return (
            "Shows that one accepted pair contributes its emitted occurrence to the "
            "concrete matched-row scheduler without dropping duplicates."
        )
    if name == "query_filter_success_bags_of_stable_total_acceptance":
        return (
            "Characterizes successful filter bags by one stable total acceptance "
            "callback only after exact per-row formula success and no-error are supplied."
        )
    if name == "query_filter_error_iff_of_stable_total_acceptance":
        return (
            "Characterizes filter errors under the same stable total acceptance "
            "contract, retaining child errors and exact reached formula error categories."
        )
    if name == "eval_filter_rows_uniform_error_of_reached_member":
        return (
            "Constructs the sequential FILTER error from one reached bad occurrence "
            "when every reached row succeeds or exposes that same category."
        )
    if name == "eval_filter_rows_error_category_of_reached_categories":
        return (
            "Shows that any FILTER error has the fixed category shared by every "
            "reached formula-error observation."
        )
    if name == "eval_filter_rows_success_excludes_reached_exact_error":
        return (
            "Excludes every successful FILTER traversal when one reached occurrence "
            "has no successful formula observation."
        )
    if name == "eval_filter_rows_reached_uniform_error_exact":
        return (
            "Packages FILTER error existence, success exclusion, and uniqueness of "
            "the exact runtime category from explicit reached-row premises."
        )
    if name in {
        "eval_filter_rows_uniform_error_of_join_witness",
        "eval_filter_rows_uniform_error_of_self_match",
    }:
        return (
            "Constructs the FILTER error derivation from a concrete accepted join "
            "cell; the self form retains the explicit accepted diagonal witness."
        )
    if name in {
        "nonnull_foreign_key_direct_accept_has_middle",
        "nonnull_foreign_key_no_middle_rejects_direct",
    }:
        return (
            "Lifts a conforming non-NULL foreign key to an explicit referenced middle "
            "witness, or derives rejection when no such middle row exists."
        )
    if name in {
        "join_matched_rows_empty_of_rejection",
        "middle_padding_downstream_empty",
    }:
        return (
            "Eliminates exactly the displayed rejected matched or NULL-padded branch "
            "without moving SQL evaluations or changing duplicate multiplicity."
        )
    if name == "filtered_payload_erasure_permut":
        return (
            "Transports one filtered occurrence block across explicit predicate agreement "
            "and a payload relation while preserving multiplicity."
        )
    if name == "query_expr_outcome_equiv_of_shared_exact_error":
        return (
            "Lifts two error-only query relations exposing the same unique category "
            "to exact outcome equivalence after successful outcomes are excluded."
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
    if name in GENERIC_QUERY_RENAME_CONSTRUCTOR_THEOREMS:
        specialized = {
            "QExpr_Error_rename_transport":
                "Use after proving the mapped, admissible endpoint-schema contract; the same opaque SQL error is retained exactly.",
            "QExpr_Values_rename_transport":
                "Use only when the target VALUES bag is the concrete renamed source bag and every represented source row satisfies collision/type safety.",
            "QExpr_Table_rename_transport":
                "Use with an explicitly transported table/database bag; changing only the scan output labels is not a table alpha-renaming.",
            "QExpr_Set_rename_transport":
                "Use after transporting both children and certifying schema comparison plus the exact UNION/INTERSECT/EXCEPT bag scheduler on actual rows.",
            "QExpr_NaturalJoin_rename_transport":
                "Use after transporting both children and proving the exact NULL-aware common-label join behavior, including actual cross-row collisions.",
            "QExpr_CrossJoin_rename_transport":
                "Use with disjoint admissible endpoint schemas and an exact local proof for left-biased tuple construction on all reachable row pairs.",
            "QExpr_Join_rename_transport":
                "Use only when predicate, all kind-dependent projections/aliases, both children, exact Bool3 outcomes, bags, and errors are transported together.",
            "QExpr_Project_rename_transport":
                "Use only with a local proof covering every selected expression, input reference, output alias, projection order, and runtime error.",
            "QExpr_RowMap_rename_transport":
                "Use with pointwise callback conjugacy plus cross-output collision/type safety for every successful source callback run.",
            "QExpr_Filter_rename_transport":
                "Use with exact formula outcomes in renamed row environments and the exact ordered filter scheduler; FALSE and UNKNOWN may not be exchanged.",
            "QExpr_Group_rename_transport":
                "Use with paired reachable group formation, exact HAVING Bool3/aggregate-error behavior, renamed keys/projection aliases, and the exact bag scheduler.",
            "QExpr_GroupingSets_rename_transport":
                "Use only after pairing every grouping-set branch, its projection/group metadata, output schema, bag results, and runtime errors.",
            "QExpr_Rank_rename_transport":
                "Use when partition/order keys and the fresh rank output alias are renamed together and the rank callback/error scheduler is preserved.",
            "QExpr_Window_rename_transport":
                "Use when partition/order keys, every window item and alias, ordered peer behavior, aggregate outcomes, and errors are transported together.",
            "QExpr_Distinct_rename_transport":
                "Use only under collision-reflecting child transport and the exact finite-bag duplicate-elimination compatibility premise.",
            "QExpr_OrderBy_rename_transport":
                "Use when each sort-key attribute, direction, NULL placement, comparator, nondeterministic tie order, and exact output order are preserved.",
            "QExpr_Offset_rename_transport":
                "Use after transporting the child and mapped endpoint schema; the proved `skipn` law preserves exact positions and multiplicity.",
            "QExpr_Fetch_rename_transport":
                "Use after transporting the child and mapped endpoint schema; the proved `firstn` law preserves exact positions and multiplicity.",
        }
        return specialized[name]
    if name in OUTPUT_ONLY_RENAMING_ADAPTER_ENTRIES:
        return (
            "Use only at an output observation boundary.  It does not rename predicates, "
            "projection inputs, group/join/sort/window metadata, aliases inside nested "
            "operators, or correlated subqueries, so do not cite it as full alpha-renaming."
        )
    if name in MAPPED_SCHEMA_OBSERVATION_ENTRIES:
        return (
            "Use to package or project exact outcomes under a mapped ordered schema after "
            "constructor-local transport has been proved.  Output-only relabeling can also "
            "satisfy this observation, so it is not ordinary equivalence or full alpha-renaming."
        )
    if name in {
        "tnull_attribute_name_renaming_type_preserving",
        "tnull_attribute_name_renaming_value_conforms",
        "tnull_rows_name_renaming_type_safe",
    }:
        return (
            "Use only with `rename_tnull_attribute_name`, which changes the textual "
            "name and leaves the complete SQL type/typmod constructor untouched."
        )
    if name == "tnull_tuple_conforms_sort_renaming_transport":
        return (
            "Use after proving injectivity on the relevant source sort.  A collision "
            "between two represented attributes is deliberately not transportable."
        )
    if name in {
        "tnull_rows_renaming_firstn_transport",
        "tnull_rows_renaming_skipn_transport",
    }:
        return (
            "Use for OFFSET/FETCH-style ordered slicing after establishing exact "
            "pointwise row renaming; the conclusion is not merely bag equality."
        )
    if name == "tnull_query_mapped_schema_outcome_equiv_mapped_schema":
        return (
            "Use to recover the target schema from mapped-schema outcome equivalence.  "
            "It is observational only; certify full alpha-renaming through constructor-local "
            "metadata premises, while ordinary equivalence still requires unchanged labels."
        )
    if name == "tnull_query_renaming_context_chain_transport":
        return (
            "Use for any finite nesting after certifying every paired context with "
            "its constructor-local transport rule.  Supply a textual `string -> string` "
            "map; the facade lifts it without permitting a typmod change, while predicates, "
            "projections, join/group/sort/window metadata, aliases, and schemas move together."
        )
    if name == "query_bag_reset_success_permutation_closed":
        return (
            "Use when `query_expr_order_behavior query = BagReset` computes or "
            "is proved directly.  The conclusion concerns successful row lists "
            "only; prove SQL errors separately."
        )
    if name in {
        "query_project_preserves_success_permutation_closed",
        "query_row_map_preserves_success_permutation_closed",
        "query_filter_preserves_success_permutation_closed",
    }:
        return (
            "Use with `ConcretePermutationClosed` for the child, not merely "
            "`BagClosed`.  It reorders the same concrete row representatives "
            "and makes no claim about error outcomes."
        )
    if name == "query_structural_successes_bag_closed":
        return (
            "Try first on a Project/Filter/RowMap stack above a bag reset; the "
            "Boolean premise usually closes by reflexivity.  It intentionally "
            "does not cross OrderBy, Offset, or Fetch, and errors remain separate."
        )
    if name == "in_rows_acceptance_existsb":
        return (
            "Use after proving the per-candidate `Bool.is_true` decision.  The "
            "conclusion is suitable for WHERE or semijoin filtering only; it is "
            "not equality of the complete SQL Bool3 result."
        )
    if name == "existsb_support_rel":
        return (
            "Use only for a Boolean existence consumer after proving bidirectional "
            "support and predicate properness.  It does not preserve counts, list "
            "order, evaluation effects, or a three-valued predicate result."
        )
    if name in {
        "in_rows_acceptance_support_rel",
        "in_rows_acceptance_append",
    }:
        return (
            "Use only at an IN TRUE-acceptance boundary after candidate-query "
            "success/error behavior has been handled separately.  Do not use it "
            "to prove full Bool3 equality, NOT IN, multiplicity, or ordered outcomes."
        )
    if name in {
        "formula_truth_exact_acceptance_exact",
        "formula_not_truth_exact",
        "formula_not_acceptance_exact",
    }:
        return (
            "Use only with the displayed exact-truth contract: it includes one "
            "successful observation, uniqueness of the full Bool3 truth, and "
            "exclusion of every runtime error at the same environment."
        )
    if name in {
        "formula_in_truth_exact",
        "formula_not_in_acceptance_exact_of_fixed_truth",
    }:
        return (
            "Use after proving argument safety, child-success inhabitation, one "
            "fixed full Bool3 IN truth across all legal child observations, and "
            "absence of child errors; an acceptance bit alone cannot justify NOT IN."
        )
    if name == "formula_in_acceptance_exact":
        return (
            "Use at a filter/join acceptance boundary with the pointwise tuple-IN "
            "decision and every displayed child/no-error premise; FALSE and UNKNOWN "
            "may share rejection but remain distinct semantic truths."
        )
    if name in {
        "formula_exists_truth_exact",
        "formula_not_exists_acceptance_exact",
    }:
        return (
            "Use at one fixed, possibly correlated environment after proving a child "
            "success, agreement of every child success on emptiness, and exclusion "
            "of every child runtime error."
        )
    if name in {
        "tnull_in_rows_unknown_iff",
        "tnull_in_rows_semantic_cases",
        "tnull_not_in_rows_acceptance_iff_all_false",
        "tnull_not_in_rows_acceptance_iff_no_true_or_unknown",
    }:
        return (
            "Use at the TNull row-truth boundary over query_canonical_rows.  Empty "
            "inputs and duplicate candidates remain represented, and UNKNOWN must "
            "not be collapsed into FALSE when reasoning about NOT IN."
        )
    if name in {
        "tnull_formula_not_in_accepts_exact_of_all_false",
        "tnull_formula_not_in_rejects_exact_of_true_match",
        "tnull_formula_not_in_rejects_exact_of_unknown_without_match",
    }:
        return (
            "Use at one fixed correlated environment after proving argument safety, "
            "child-success inhabitation, the displayed case for every legal child "
            "success, and exclusion of every child error."
        )
    if name == "formula_in_union_all_acceptance_exact":
        return (
            "Use only for UNION ALL at one fixed correlated environment after proving "
            "schema compatibility, argument safety, inhabited branch successes, fixed "
            "per-branch TRUE-acceptance decisions, and absence of both branch errors.  "
            "It is not a full Bool3 or UNION DISTINCT distribution theorem."
        )
    if name in {"query_distinct_rows_support_rel", "in_rows_acceptance_distinct"}:
        return (
            "Use only for duplicate-insensitive support or IN TRUE-acceptance.  DISTINCT "
            "changes row multiplicity and may not be erased for COUNT, bags, exact ordered "
            "results, or full FALSE/UNKNOWN truth without additional premises."
        )
    if name == "query_join_sources_member_iff":
        return (
            "Use on a concrete scheduler source list and inspect the constructor-"
            "specific disjunct.  Semi and anti emit left sources for opposite "
            "reachability decisions; outer unmatched branches are not symmetric aliases."
        )
    if name in {
        "query_join_sources_support_rel",
        "query_join_sources_projected_support_rel",
    }:
        return (
            "Use after proving bidirectional input support and exact Boolean match "
            "correspondence.  The projected form also requires both source inputs "
            "to be reached before applying an emitter; prove bags, order, and errors separately."
        )
    if name == "query_expr_join_no_error_of_acceptance_projection_exact":
        return (
            "Use only after proving both children error-free, exact condition acceptance "
            "for every row pair, and exact successful projection for every potentially "
            "reached join source.  This proves safety, not bag or outcome equivalence."
        )
    if name == "partial_semijoin_projection_support_rel":
        return (
            "Use only at a support or duplicate-elimination boundary after relating every "
            "accepted projected join cell to its surviving left row.  It intentionally does "
            "not preserve multiplicity, order, SQL Bool3 evaluation, or runtime errors."
        )
    if name == "list_support_rel_filter_transport":
        return (
            "Use after proving support and decision properness on the support "
            "relation.  It ignores multiplicity and does not model volatile or "
            "runtime-error-producing SQL predicate evaluation."
        )
    if name == "eval_groups_all_rejected_outcome_exact":
        return (
            "Use only when SELECT and HAVING aggregate finalization succeeds for "
            "every reached group and HAVING has one exact nontrue, error-free "
            "decision.  Scalar SELECT projection is intentionally not a premise."
        )
    if name in {
        "tnull_group_count_star_value_runtime_exact",
        "count_star_value_local_error_exact_of_equal_length",
        "count_star_value_runtime_error_exact_of_equal_observation_length",
    }:
        return (
            "Use for COUNT-star cardinality transport without assuming the count is "
            "inside BIGINT range.  Equal lengths preserve both the value placeholder "
            "and the exact overflow category; child query errors remain separate."
        )
    if name in {
        "count_star_count_all_nonnull_value_local_error_exact",
        "count_star_count_all_nonnull_value_runtime_error_exact",
    }:
        return (
            "Use only for AggregateAll after proving equal reached cardinality and "
            "every expression value non-NULL.  The full runtime form also requires "
            "each reached child observation to be error-free; DISTINCT is excluded."
        )
    if name == "formula_pred_outcome_equiv_of_argument_observations":
        return (
            "Use after proving equality of the complete reached argument-value list and "
            "its left-biased first runtime error.  Acceptance equality alone is insufficient "
            "because the theorem preserves the full Bool3 outcome."
        )
    if name in {
        "tnull_group_count_star_projection_eq_of_equal_length",
        "tnull_count_star_group_observation_equiv_of_equal_length",
        "tnull_count_star_groups_outcome_equiv_of_Forall2_observations",
        "tnull_count_star_groups_true_outcome_equiv_of_Forall2_length",
    }:
        return (
            "Use with equal cardinality for every paired reached group.  Arbitrary HAVING "
            "requires exact aggregate and formula outcome correspondence; the TRUE-HAVING "
            "specialization discharges only that predicate boundary.  The scheduler result "
            "is semantic permutation, not a promoted exact ordered row list."
        )
    if name == "formula_and_redundant_right_acceptance_exact":
        return (
            "Use for guarded correlated predicates only after the inserted right "
            "formula is exact and cannot error on every reached row.  FormalSQL is "
            "eager, so a witness proved only on accepting guard rows is insufficient."
        )
    if name in {
        "integer_stats_fold_interval_invariant",
        "integer_stats_initial_interval_bounds",
        "bounded_integer_stats_sum_positive",
    }:
        return (
            "Use for the exact logical Z-valued statistics state under the displayed "
            "symbolic interval/count hypotheses.  These bounds alone do not justify "
            "NUMERIC division, square-root rounding, comparison, or runtime safety."
        )
    if name == "full_outer_filter_to_left_outer_exact":
        return (
            "Use only after matched and left-padded rows are proved to inherit one "
            "left guard and every right-padded row is rejected.  At SQL level also "
            "prove predicate totality, non-volatility, properness, and exact error equivalence."
        )
    if name == "left_right_outer_scheduler_swap_Permutation":
        return (
            "Use only after the target condition is the exact transpose and the "
            "matched and padded projections agree through one common emitter.  "
            "SQL condition/projection errors and semantic tuple equality remain separate."
        )
    if name == "left_outer_null_reject_to_inner_exact":
        return (
            "Use only when every padded-left row is rejected.  Moving the retained "
            "matched-row filter or claiming SQL outcome equivalence additionally "
            "requires totality, properness, non-volatility, and exact error premises."
        )
    if name in {
        "position_rows_from_values",
        "position_rows_from_nth_error",
        "position_rows_from_filter_le_prefix",
        "partition_runs_by_compare_exact_well_formed",
    }:
        return (
            "Use as an intrinsic list/position or comparator-run fact.  Connect it "
            "to QExpr_Rank/QExpr_Window only after proving the authoritative legal "
            "ordering, aggregate/runtime-error, and BagClosed boundary premises."
        )
    if name in {
        "rows_key_aligned_length",
        "rows_key_aligned_firstn",
        "rows_key_aligned_skipn",
        "rows_key_aligned_filter",
        "rows_key_aligned_total_map_transport",
    }:
        return (
            "Use only with a semantic key relation.  Filter decisions must be "
            "key-determined and maps total/deterministic; this interface does not "
            "equate peer payload order, bags, volatile expressions, or SQL errors."
        )
    if name in {
        "prefix_scan_observation_peer_transport",
        "prefix_scan_outcome_peer_transport_iff",
        "partitioned_prefix_scan_observation_peer_transport",
        "partitioned_prefix_scan_outcome_peer_transport_iff",
    }:
        return (
            "Use only after proving the adjacent-peer contract for every allowed swap: "
            "the two affected post-filter observations and every later observed prefix "
            "must agree semantically.  The outcome form additionally requires exact "
            "error-category equivalence and does not equate hidden window rows."
        )
    if name in {
        "order_by_rows_total_map_preimage",
        "total_map_order_fetch_observation_iff",
        "total_map_order_fetch_outcome_observation_iff",
    }:
        return (
            "Use only with a semantic row map that preserves and reflects the complete "
            "ORDER BY comparison, including NULL placement and ties.  The result ranges "
            "over every legal representative; the outcome form still requires exact "
            "child/join/projection/order error equivalence."
        )
    if name in {
        "fold_nonempty_support_equiv",
        "exact_extrema_aggregate_permutation",
        "exact_extrema_aggregate_support_equiv",
        "exact_extrema_aggregate_duplicate_block",
        "exact_extrema_aggregate_runtime_error_duplicate_block",
    }:
        return (
            "Use only for the explicitly enumerated exact MIN/MAX functions.  The "
            "law is deliberately unavailable for SUM/AVG, especially FLOAT/DOUBLE; "
            "preserve child-error order through the separate runtime theorem."
        )
    if name in {
        "first_runtime_error_duplicate_block",
        "first_observation_error_duplicate_block",
    }:
        return (
            "Use only for literal repetition of the same reached block in the same "
            "prefix/suffix schedule.  Arbitrary support equivalence does not preserve "
            "which SQL error is observed first."
        )
    if name in {
        "numeric_round_quot_nonnegative_half_ulp",
        "numeric_round_to_scale_nonnegative_half_ulp",
        "numeric_sqrt_at_scale_half_ulp_shape",
    }:
        return (
            "Use only under the displayed nonnegative input and scale premises.  "
            "The coefficient shape is not itself a SQL comparison or runtime-safety result."
        )
    if name in {
        "numeric_pg_div_scale_display_valid",
        "numeric_of_scaled_compare_lt",
        "finite_numeric_division_result_rounding",
        "finite_numeric_division_strict_margin",
    }:
        return (
            "Use with the exact selected-scale equation and explicit fixed-point "
            "half-ULP margin.  Supply denominator nonzero, scale validity, and result "
            "fit premises; do not infer them from rational order alone."
        )
    if name in {
        "finite_numeric_division_runtime_error_zero_divisor",
        "finite_numeric_division_runtime_error_invalid_scale",
        "finite_numeric_division_runtime_error_missing_result",
        "finite_numeric_division_runtime_error_result_out_of_range",
    }:
        return (
            "Use for the exact displayed failure branch and preserve evaluation "
            "reachability.  These categories are complementary to, not interchangeable "
            "with, a generic no-error premise."
        )
    if name in {
        "numeric_integer_stddev_samp_positive_success_iff",
        "int32_avg_numeric_with_scale_success_iff",
    }:
        return (
            "Use only after proving the positive sample numerator or nonempty AVG "
            "fold/count premise.  Compose rounding, comparison, and runtime categories "
            "through the separate NUMERIC interfaces."
        )
    if name == "numeric_of_scaled_compare_not_gt":
        return (
            "Use with nonnegative coefficients and the displayed cross-multiplied "
            "non-strict bound.  The result excludes only Gt and deliberately retains Eq."
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
    if name == "tnull_select_lookup_direct_compose_interp_value":
        return (
            "Use when both SELECT stages have the displayed first-match direct "
            "lookups.  No source-label presence premise is needed because the "
            "conclusion preserves the original row-extended interpretation."
        )
    if name == "tnull_projection_rows_eq_of_output_values":
        return (
            "Use after proving exact equality of the two SELECT output-label sets "
            "and equality of each cell observable through that set."
        )
    if name == "tnull_direct_projection_fusion_row_eq":
        return (
            "Applies to composition of one direct projection with a two-stage direct "
            "projection after supplying the exact first-match lookup chains."
        )
    if name == "tnull_select_columns_lookup_output":
        return (
            "Use for a SelectColumns member instead of proving uniqueness or "
            "manually reducing first-match lookup over a concrete list."
        )
    if name == "tnull_select_columns_projection_fusion_row_eq":
        return (
            "Applies when the compared projection composition uses SelectColumns; "
            "it reduces the row law to output-set equality and outer-to-inner coverage."
        )
    if name == "tnull_project_fusion_success_bag_contract_of_row_eq":
        return (
            "Applies when the projection-composition row law is valid for every row. "
            "A law restricted to reachable rows must instead discharge the original "
            "reachable-bag contract."
        )
    if name == "query_project_success_bags_fusion_safe":
        return (
            "Use after proving all three SELECT lists locally safe and the named "
            "fusion contract on every reachable child bag; errors and ordered "
            "observations are outside this success-bag theorem."
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
    if name == "eval_groups_global_true_outcome_exact":
        return (
            "Use for `GROUP BY [] HAVING TRUE` after proving aggregate finalization "
            "and scalar projection runtime safety for the one global group."
        )
    if name == "query_canonical_rows_map_factor_permut":
        return (
            "Use when a schema-changing projection or alias rename is moved "
            "across grouping, quantified predicates, or another canonical bag "
            "representative boundary."
        )
    if name == "eval_group_bag_global_true_success_exists":
        return (
            "Use to discharge an outcome-inhabitation premise for a runtime-safe "
            "`GROUP BY [] HAVING TRUE` or scalar aggregate subquery."
        )
    if name == "eval_group_bag_global_true_success_bag_unique_if_stable":
        return (
            "Use at a successful scalar/global aggregate subquery when the child "
            "is represented as a bag and the actual aggregate projection has a "
            "separate permutation-stability proof."
        )
    if name == "group_projection_permutation_stable":
        return (
            "Use as the explicit contract required before treating a grouping "
            "projection as a function of only the input bag."
        )
    if name == "rows_permut_implies_bag_eq":
        return (
            "Use after a semantic list-permutation proof when the enclosing "
            "constructor or equivalence goal expects finite-bag equality."
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
    if name in GENERIC_QUERY_RENAME_CONSTRUCTOR_THEOREMS:
        common = (
            "The displayed `query_rename_schema_compatible` premise retains ordered "
            "mapped outputs, collision/type safety, and admissibility of both endpoints.  "
        )
        specialized = {
            "QExpr_Error_rename_transport":
                "No child or local premise is needed; the error value itself must be identical.",
            "QExpr_Values_rename_transport":
                "Keep `query_bag_source_rename_safe` and exact mapped-bag equality; declared outputs alone do not constrain malformed rows.",
            "QExpr_Table_rename_transport":
                "Keep actual table-bag safety and exact mapped equality between the two database scans.",
            "QExpr_Set_rename_transport":
                "Keep union-support injection, both child transports, and the binary local compatibility premise for actual representatives.",
            "QExpr_NaturalJoin_rename_transport":
                "Keep union-support injection, both child transports, and the NULL-aware binary local compatibility premise.",
            "QExpr_CrossJoin_rename_transport":
                "Keep union-support injection, both endpoint disjointness proofs, both child transports, and binary local compatibility.",
            "QExpr_Join_rename_transport":
                "Keep union-support injection, both child transports, exact predicate outcomes over joined row environments, and full binary local compatibility.",
            "QExpr_Project_rename_transport":
                "Keep child transport and the projection-local compatibility premise; output-only alias mapping does not prove input-expression transport.",
            "QExpr_RowMap_rename_transport":
                "Keep child transport, pointwise callback compatibility, and successful-output collision/type safety.",
            "QExpr_Filter_rename_transport":
                "Keep child transport, exact Bool3/error formula compatibility, and ordered unary local compatibility.",
            "QExpr_Group_rename_transport":
                "Keep child transport, reachable group-formation pairing, exact HAVING plus aggregate-precheck compatibility, and unary local compatibility.",
            "QExpr_GroupingSets_rename_transport":
                "Keep child transport and one exact unary local compatibility proof covering every grouping-set branch.",
            "QExpr_Rank_rename_transport":
                "Keep both key-list relations, mapped fresh output alias, child transport, and exact rank-local compatibility.",
            "QExpr_Window_rename_transport":
                "Keep both key-list relations, mapped item aliases, child transport, and exact window-local compatibility.",
            "QExpr_Distinct_rename_transport":
                "Keep source-sort injection, child transport, and exact duplicate-elimination local compatibility.",
            "QExpr_OrderBy_rename_transport":
                "Keep the complete sort-key relation, child transport, and exact order-producing local compatibility.",
            "QExpr_Offset_rename_transport":
                "Keep the child transport; the constructor-local `skipn` compatibility is proved by the library.",
            "QExpr_Fetch_rename_transport":
                "Keep the child transport; the constructor-local `firstn` compatibility is proved by the library.",
        }
        return common + specialized[name]
    if name in OUTPUT_ONLY_RENAMING_ADAPTER_ENTRIES:
        return (
            "The adapter uses the existing `QExpr_RowMap` and maps successful rows only; "
            "retain the exact child evaluation and error category.  No conclusion about "
            "attribute-bearing metadata inside the child query follows."
        )
    if name in MAPPED_SCHEMA_OBSERVATION_ENTRIES:
        return (
            "Retain the full mapped-schema and exact success/error relation displayed.  "
            "For alpha-renaming, separately derive it from the relevant `QExpr_*_rename_transport` "
            "theorems and their metadata, collision, typing, and admissibility premises."
        )
    if name == "tnull_rows_name_renaming_type_safe":
        return (
            "No injectivity premise is needed for this actual-row type/typmod fact.  "
            "Collision reflection remains a separate `rows_rename_collision_safe` obligation."
        )
    if name in {
        "tnull_attribute_name_renaming_type_preserving",
        "tnull_attribute_name_renaming_value_conforms",
    }:
        return (
            "No injectivity premise is needed for this one-attribute fact, but the "
            "renamer must be the displayed name-only TNull adapter."
        )
    if name == "tnull_tuple_conforms_sort_renaming_transport":
        return (
            "Retain tuple conformance and `attribute_rename_injective_on sort`; "
            "without the latter, finite-map keys can collide and lose a value."
        )
    if name in {
        "tnull_rows_renaming_firstn_transport",
        "tnull_rows_renaming_skipn_transport",
    }:
        return (
            "Supply the exact `rows_rename_equiv` relation.  It fixes pointwise "
            "renamed representatives, list order, length, and duplicate positions."
        )
    if name == "tnull_query_mapped_schema_outcome_equiv_mapped_schema":
        return (
            "Supply a textual `string -> string` map and exact mapped-schema outcomes.  "
            "The facade applies `rename_tnull_attribute_name`, so typmods cannot change, "
            "but this premise alone does not certify predicate/key/subquery metadata."
        )
    if name == "tnull_query_renaming_context_chain_transport":
        return (
            "Supply a textual `string -> string` map, `Forall2` compatibility for the "
            "complete left/right context lists, and a transport proof for the holes.  "
            "The facade preserves typmods and infers no metadata premise from output-only renaming."
        )
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
    if name == "tnull_select_lookup_direct_compose_interp_value":
        return (
            "Both displayed lookup equalities are mandatory and use authoritative "
            "first-match semantics; the theorem deliberately has no source-presence premise."
        )
    if name == "tnull_projection_rows_eq_of_output_values":
        return (
            "Retain exact output-label-set equality and cell equality for every "
            "attribute in the left output set; neither premise follows from arity alone."
        )
    if name == "tnull_direct_projection_fusion_row_eq":
        return (
            "Retain equal final output-label sets and all three first-match lookup "
            "equations for every observable target; repeated aliases cannot select a later item."
        )
    if name == "tnull_select_columns_lookup_output":
        return (
            "The attribute must belong to the displayed SelectColumns output set. "
            "Repeated identical columns remain valid under first-match semantics."
        )
    if name == "tnull_select_columns_projection_fusion_row_eq":
        return (
            "Retain exact single/outer output-set equality and outer-to-inner set "
            "coverage; coverage prevents correlated fallback for an absent inner label."
        )
    if name == "tnull_project_fusion_success_bag_contract_of_row_eq":
        return (
            "The displayed all-row semantic equality is a stronger sufficient "
            "premise; the resulting contract still ranges only over reachable child bags."
        )
    if name == "query_project_success_bags_fusion_safe":
        return (
            "Keep all three per-row SELECT safety premises and the exact reachable-bag "
            "fusion contract; the theorem does not establish error equivalence."
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
    if name == "eval_groups_global_true_outcome_exact":
        return (
            "Aggregate finalization and scalar SELECT evaluation must be safe in "
            "the one environment formed from `rev rows`; HAVING is literally TRUE."
        )
    if name == "query_canonical_rows_map_factor_permut":
        return (
            "The representation map must respect semantic tuple equality, and "
            "the displayed pointwise factor equation must hold for every source item."
        )
    if name == "eval_group_bag_global_true_success_exists":
        return (
            "Aggregate finalization and scalar SELECT evaluation must be safe for "
            "every group list that the representative-saturated reset may choose."
        )
    if name == "eval_group_bag_global_true_success_bag_unique_if_stable":
        return (
            "Retain input-representative validity, aggregate and scalar SELECT "
            "safety for every possible global group, explicit projection "
            "permutation stability, and the successful reset outcome."
        )
    if name == "group_projection_permutation_stable":
        return (
            "This is a property to prove, not an unconditional theorem; floating-"
            "point SUM/AVG generally do not satisfy it."
        )
    if name == "rows_permut_implies_bag_eq":
        return "The two row lists must be semantically permuted under `OTuple`."
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

    if "lemma-catalog/" in index or "PRIMARY_CARD" in index:
        raise ValueError("catalog index advertises an obsolete search path")
    if len(index.encode("utf-8")) > MAX_INDEX_BYTES:
        raise ValueError("catalog index compactness regression")
    if ".[0:" in index:
        raise ValueError("catalog index retained a silent top-k slice")
    if index.count("{total: length") != 2:
        raise ValueError("catalog index must expose totals for both paged searches")
    for route in ROUTES:
        if f"| `{route}` |" not in index:
            raise ValueError(f"catalog index omits neutral route {route}")

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
    ) -> None:
        if primary(name) != card:
            raise ValueError(f"{name}: expected primary card {card}")
        missing_routes = required_routes - routes(name)
        if missing_routes:
            raise ValueError(
                f"{name}: missing required routes {sorted(missing_routes)}"
            )

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

    # Every non-leaf query constructor has an authoritative exact typed-outcome
    # congruence in FormalSQL.  Keep the family complete and searchable so an
    # agent never re-proves a constructor lift by unfolding the evaluator.
    expected_constructor_congruences = expected_query_constructor_congruences()
    if GENERIC_QUERY_CONSTRUCTOR_CONGRUENCES != expected_constructor_congruences:
        raise ValueError(
            "query syntax and constructor congruence inventory diverged: "
            f"missing={sorted(expected_constructor_congruences - GENERIC_QUERY_CONSTRUCTOR_CONGRUENCES)}, "
            f"stale={sorted(GENERIC_QUERY_CONSTRUCTOR_CONGRUENCES - expected_constructor_congruences)}"
        )
    missing_constructor_congruences = (
        GENERIC_QUERY_CONSTRUCTOR_CONGRUENCES - by_name.keys()
    )
    if missing_constructor_congruences:
        raise ValueError(
            "query constructor congruence coverage regressed: "
            f"{sorted(missing_constructor_congruences)}"
        )
    for congruence in GENERIC_QUERY_CONSTRUCTOR_CONGRUENCES:
        if not {"outcome", "runtime"} <= routes(congruence):
            raise ValueError(
                f"{congruence}: missing outcome/runtime constructor routes"
            )
        if str(entry(congruence)["source"]) != (
            "vendor/FormalSQL/src/data/sql/SqlQueryContexts.v"
        ):
            raise ValueError(
                f"{congruence}: constructor congruence is not FormalSQL-owned"
            )
    require_route_contract(
        "query_expr_context_global_congr",
        "runtime-verification-rewrite.md",
        {"outcome", "runtime"},
    )
    require_route_contract(
        "query_context_global_congr",
        "runtime-verification-rewrite.md",
        {"outcome", "runtime"},
    )
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
    )
    require_route_contract(
        "eval_filter_rows_ordered_outcome_congr",
        "relational-algebra.md",
        {"outcome", "runtime", "filter"},
    )
    require_route_contract(
        "interp_predicate_eq_true_is_true_acceptance",
        "null-predicates.md",
        {"filter", "scalar"},
    )
    row_facade = "tnull_row_eq_of_labels_and_values"
    if not {"facade", "projection"} <= routes(row_facade):
        raise ValueError(f"{row_facade}: row-extensionality route regressed")

    renaming_entries = {
        "tnull_attribute_name_renaming_type_preserving",
        "tnull_attribute_name_renaming_value_conforms",
        "tnull_rows_name_renaming_type_safe",
        "tnull_tuple_conforms_sort_renaming_transport",
        "tnull_rows_renaming_firstn_transport",
        "tnull_rows_renaming_skipn_transport",
        "tnull_query_mapped_schema_outcome_equiv_mapped_schema",
        "tnull_query_renaming_context_chain_transport",
    }
    for renaming_entry in renaming_entries:
        require_route_contract(
            renaming_entry,
            "renaming-transport.md",
            {"renaming", "facade"},
        )
        require(
            renaming_entry,
            "rename",
            "renaming",
            "alias",
            "alpha-renaming",
            "transport",
        )
    for generic_entry in (
        GENERIC_QUERY_RENAME_CONSTRUCTOR_THEOREMS
        | GENERIC_RENAMING_DIMENSION_ENTRIES
    ):
        require_route_contract(
            generic_entry,
            "renaming-transport.md",
            {"renaming"},
        )
        require(
            generic_entry,
            "rename",
            "renaming",
            "alias",
            "alpha-renaming",
            "transport",
        )
        generic_source = str(entry(generic_entry)["source"])
        if not (
            generic_source.startswith("vendor/FormalSQL/src/data/sql/")
            or generic_source == "theories/FormalSQL/RenameTransportFacts.v"
        ):
            raise ValueError(
                f"{generic_entry}: unexpected renaming source {generic_source}"
            )
    for constructor_entry, operator_route in {
        "QExpr_Project_rename_transport": "projection",
        "QExpr_Join_rename_transport": "join",
    }.items():
        require_route_contract(
            constructor_entry,
            "renaming-transport.md",
            {"renaming", operator_route},
        )

    for observation_only in OUTPUT_ONLY_RENAMING_ADAPTER_ENTRIES:
        require_route_contract(
            observation_only,
            "renaming-transport.md",
            {"renaming"},
        )
        if "not a full query alpha-renaming" not in str(
            entry(observation_only)["summary"]
        ):
            raise ValueError(
                f"{observation_only}: output-only alpha-renaming warning regressed"
            )
    for mapped_observation in MAPPED_SCHEMA_OBSERVATION_ENTRIES:
        require_route_contract(
            mapped_observation,
            "renaming-transport.md",
            {"renaming"},
        )
        if "does not certify renamed operator metadata" not in str(
            entry(mapped_observation)["summary"]
        ):
            raise ValueError(
                f"{mapped_observation}: mapped-schema observation warning regressed"
            )
    require_route_contract(
        "tnull_query_renaming_context_chain_transport",
        "renaming-transport.md",
        {"renaming", "facade", "grouping", "projection", "join", "bag", "ordered"},
    )
    for query_facade in {
        "tnull_query_mapped_schema_outcome_equiv_mapped_schema",
        "tnull_query_renaming_context_chain_transport",
    }:
        if "(rename_name : string -> string)" not in str(entry(query_facade)["statement"]):
            raise ValueError(f"{query_facade}: TNull facade is not name-only")
    if "rename_tnull_attribute_name rename_name" not in str(
        entry("tnull_query_mapped_schema_outcome_equiv_mapped_schema")["statement"]
    ):
        raise ValueError("TNull mapped-schema facade bypasses the typmod-preserving adapter")
    renaming_document = documents["renaming-transport.md"]
    for generic_source in ("SqlRenameFacts.v", "SqlQueryRenameTransport.v"):
        if generic_source not in renaming_document:
            raise ValueError(
                f"renaming catalog omits FormalSQL ownership source: {generic_source}"
            )

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
        )
    require_route_contract(
        "project_join_sources_outcome_exact_map",
        "relational-algebra.md",
        {"outcome", "runtime", "projection", "join"},
    )
    require_route_contract(
        "eval_join_bag_safe_of_acceptance_projection_exact",
        "relational-algebra.md",
        {"outcome", "runtime", "projection", "join", "bag"},
    )
    require_route_contract(
        "tnull_join_condition_pred_acceptance_exact_safe",
        "runtime-verification-rewrite.md",
        {"facade", "runtime", "filter", "join", "scalar"},
    )

    for row_law in {"tnull_row_eq_refl", "tnull_row_eq_sym", "tnull_row_eq_trans"}:
        require_route_contract(
            row_law,
            "relational-algebra.md",
            {"facade", "projection"},
        )
    for lookup_presence in {
        "tnull_select_lookup_some_iff_projected_label",
        "tnull_select_lookup_none_iff_projected_label_absent",
    }:
        require_route_contract(
            lookup_presence,
            "relational-algebra.md",
            {"facade", "projection"},
        )
    require_route_contract(
        "tnull_project_rows_select_columns_success",
        "relational-algebra.md",
        {"facade", "runtime", "projection"},
    )
    require_route_contract(
        "tnull_query_expr_project_select_columns_error_iff",
        "runtime-verification-rewrite.md",
        {"facade", "outcome", "runtime", "projection"},
    )
    require_route_contract(
        "tnull_eval_group_bag_direct_columns_true_no_error",
        "aggregate-grouping.md",
        {"facade", "outcome", "grouping", "runtime", "bag"},
    )

    # Exact acceptance and grouping interfaces must remain reachable through
    # the small routes used by grouped/filter/subquery query shapes.
    require_route_contract(
        "formula_conj_acceptance_exact",
        "aggregate-grouping.md",
        {"grouping", "filter", "scalar"},
    )
    require_route_contract(
        "formula_exists_acceptance_exact",
        "subquery-predicates.md",
        {"filter", "runtime", "scalar"},
    )
    require_route_contract(
        "eval_groups_true_outcome_exact",
        "aggregate-grouping.md",
        {"outcome", "grouping", "runtime"},
    )
    require_route_contract(
        "eval_groups_global_true_outcome_exact",
        "aggregate-grouping.md",
        {"outcome", "grouping", "runtime"},
    )
    require_route_contract(
        "query_canonical_rows_map_factor_permut",
        "aggregate-grouping.md",
        {"grouping", "bag", "renaming", "projection"},
    )
    require_route_contract(
        "eval_group_bag_global_true_success_exists",
        "aggregate-grouping.md",
        {"outcome", "grouping", "runtime", "scalar"},
    )
    require_route_contract(
        "eval_group_bag_global_true_success_bag_unique_if_stable",
        "aggregate-grouping.md",
        {"outcome", "grouping", "bag", "scalar"},
    )
    require_route_contract(
        "rows_permut_implies_bag_eq",
        "aggregate-grouping.md",
        {"bag"},
    )
    require_route_contract(
        "eval_groups_acceptance_outcome_exact",
        "aggregate-grouping.md",
        {"outcome", "grouping", "runtime"},
    )
    require_route_contract(
        "bag_filter_congr_on_support",
        "relational-algebra.md",
        {"filter", "bag"},
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
    )
    require_route_contract(
        "tnull_projection_envs_eq_of_select_items",
        "relational-algebra.md",
        {"facade", "projection"},
    )
    require_route_contract(
        "query_expr_union_success_Forall",
        "relational-algebra.md",
        {"bag"},
    )
    require_route_contract(
        "query_expr_cross_join_success_Forall",
        "relational-algebra.md",
        {"join", "bag"},
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
        )
    require_route_contract(
        "aggregate_distinct_input_Permutation_of_NoDup_support",
        "aggregate-grouping.md",
        {"grouping", "bag"},
    )
    require_route_contract(
        "partition_keys_Permutation_of_NoDup_support",
        "aggregate-grouping.md",
        {"grouping", "bag"},
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
    )
    require_route_contract(
        "tnull_direct_projection_alias_value",
        "relational-algebra.md",
        {"facade", "projection"},
    )
    require_route_contract(
        "tnull_select_columns_lookup_output",
        "relational-algebra.md",
        {"facade", "projection"},
    )
    require_route_contract(
        "tnull_select_columns_projection_fusion_row_eq",
        "relational-algebra.md",
        {"facade", "projection"},
    )
    require_route_contract(
        "tnull_select_lookup_direct_compose",
        "relational-algebra.md",
        {"facade", "projection"},
    )
    require_route_contract(
        "tnull_select_lookup_constant_direct_compose",
        "relational-algebra.md",
        {"facade", "projection"},
    )
    require_route_contract(
        "database_conforms_schema_primary_key",
        "schema-integrity.md",
        {"schema"},
    )
    require_route_contract(
        "query_same_rows_as_conforming_table_present_attribute",
        "cardinality-composition.md",
        {"cardinality", "schema"},
    )
    require_route_contract(
        "query_expr_table_success_rows_present_conform_attribute",
        "cardinality-composition.md",
        {"cardinality", "schema"},
    )
    require_route_contract(
        "query_same_rows_as_conforming_table_absent_attribute",
        "cardinality-composition.md",
        {"cardinality", "schema"},
    )
    require_route_contract(
        "query_expr_table_success_rows_absent_attribute",
        "cardinality-composition.md",
        {"cardinality", "schema"},
    )
    require_route_contract(
        "database_conforms_schema_foreign_key_nonnull_referenced",
        "schema-integrity.md",
        {"schema"},
    )
    require_route_contract(
        "eval_group_bag_exact_rows_permut_equiv",
        "aggregate-grouping.md",
        {"grouping", "bag"},
    )
    require_route_contract(
        "tnull_closed_group_sum_numeric_dot_argument_observations_permutation_rows",
        "numeric-derived.md",
        {"grouping", "bag", "scalar"},
    )
    require_route_contract(
        "tnull_closed_group_sum_numeric_dot_value_runtime_exact",
        "numeric-derived.md",
        {"grouping", "runtime", "scalar"},
    )
    require_route_contract(
        "query_make_groups_closed_sum_numeric_dot_outer_sum_value_runtime_exact",
        "numeric-derived.md",
        {"grouping", "runtime", "scalar"},
    )
    require_route_contract(
        "query_make_groups_permut_nonempty",
        "aggregate-grouping.md",
        {"grouping"},
    )
    require_route_contract(
        "query_make_groups_projected_bag_eq_of_support_rel",
        "aggregate-grouping.md",
        {"grouping", "bag"},
    )
    require_route_contract(
        "tnull_direct_columns_group_projection_support_rel",
        "aggregate-grouping.md",
        {"facade", "grouping", "projection", "bag"},
    )
    require_route_contract(
        "tnull_direct_columns_group_rows_bag_eq_of_projection_support",
        "aggregate-grouping.md",
        {"facade", "grouping", "projection", "bag"},
    )
    require_route_contract(
        "eval_group_bag_true_projected_support_equiv",
        "aggregate-grouping.md",
        {"outcome", "grouping", "bag"},
    )
    require_route_contract(
        "query_expr_group_outcome_equiv_of_supported_child_outcomes",
        "aggregate-grouping.md",
        {"outcome", "grouping"},
    )
    require_route_contract(
        "tnull_direct_columns_group_outcome_equiv_of_projected_support",
        "aggregate-grouping.md",
        {"facade", "outcome", "grouping", "runtime"},
    )
    require_route_contract(
        "list_support_rel_compose",
        "relational-algebra.md",
        {"bag"},
    )
    require_route_contract(
        "list_support_rel_map_left_with_witness",
        "relational-algebra.md",
        {"projection", "bag"},
    )
    require_route_contract(
        "group_filter_map_permutation",
        "aggregate-grouping.md",
        {"grouping", "filter", "bag"},
    )
    require_route_contract(
        "query_canonical_rows_length",
        "cardinality-composition.md",
        {"grouping", "cardinality"},
    )
    require_route_contract(
        "query_make_groups_constant_nonempty_key",
        "aggregate-grouping.md",
        {"grouping"},
    )

    # Fixed-environment bag-reset congruence retains exact child-error order;
    # neither set sort mismatch nor an error-only child is filtered away.
    require_route_contract(
        "query_expr_outcome_equiv_implies_success_bags",
        "relational-algebra.md",
        {"outcome", "runtime", "bag"},
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
    )

    # Projection/UNION ALL interfaces expose the correct bag layer while the
    # exact safe assembly rules remain on the runtime/outcome card.
    require_route_contract(
        "query_project_success_bags_safe",
        "relational-algebra.md",
        {"runtime", "projection", "bag"},
    )
    require_route_contract(
        "query_expr_project_bag_closed_safe",
        "runtime-verification-rewrite.md",
        {"runtime", "projection", "bag"},
    )
    require_route_contract(
        "query_expr_filter_bag_closed_exact",
        "relational-algebra.md",
        {"filter", "bag"},
    )
    require_route_contract(
        "query_structural_successes_bag_closed",
        "relational-algebra.md",
        {"bag"},
    )
    require_route_contract(
        "query_bag_reset_success_permutation_closed",
        "relational-algebra.md",
        {"bag"},
    )
    require_route_contract(
        "query_project_preserves_success_permutation_closed",
        "relational-algebra.md",
        {"projection", "bag"},
    )
    require_route_contract(
        "query_row_map_preserves_success_permutation_closed",
        "relational-algebra.md",
        {"projection", "bag"},
    )
    require_route_contract(
        "query_filter_preserves_success_permutation_closed",
        "relational-algebra.md",
        {"filter", "bag"},
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
    )
    require_route_contract(
        "query_cross_join_union_right_success_bags",
        "relational-algebra.md",
        {"join", "bag"},
    )
    for distribution in {
        "query_expr_cross_join_union_right_equiv_safe",
        "query_expr_cross_join_union_right_outcome_equiv_safe",
    }:
        require_route_contract(
            distribution,
            "runtime-verification-rewrite.md",
            {"outcome", "runtime", "join", "bag"},
        )
    require_route_contract(
        "query_expr_project_outcome_equiv_congr_safe",
        "runtime-verification-rewrite.md",
        {"outcome", "runtime", "projection"},
    )

    expected_entry_keys = {
        "name",
        "kind",
        "source",
        "line",
        "sourceDomain",
        "semanticDomain",
        "catalog",
        "routes",
        "summary",
        "topics",
        "statement",
    }
    for value in entries:
        if set(value) != expected_entry_keys:
            raise ValueError(
                f"{value.get('name', '<unnamed>')}: unexpected catalog entry fields "
                f"{sorted(set(value) - expected_entry_keys)}; missing "
                f"{sorted(expected_entry_keys - set(value))}"
            )
        value_routes = list(value["routes"])  # type: ignore[arg-type]
        if value["semanticDomain"] != value["catalog"]:
            raise ValueError(f"{value['name']}: semantic/catalog domains disagree")
        if value["sourceDomain"] not in DOMAINS:
            raise ValueError(f"{value['name']}: unknown source domain")
        if value_routes != [route for route in ROUTES if route in value_routes]:
            raise ValueError(f"{value['name']}: cross-routes are not deterministic")
        if "admissibility" in value_routes:
            raise ValueError(
                f"{value['name']}: instance admissibility leaked into catalog"
            )
        if "admissible" in identifier_tokens(str(value["name"])) and value_routes:
            raise ValueError(
                f"{value['name']}: admissibility constructor entered catalog navigation"
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
        "rename",
        "renaming",
        "alias",
        "alpha-renaming",
        "transport",
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


def catalog_source_href(source: str) -> str:
    """Return a card-relative link for either Logos or vendored FormalSQL."""
    return Path(os.path.relpath(ROOT / source, CATALOG)).as_posix()


def build_catalog() -> tuple[dict[str, object], dict[str, str], str]:
    entries: list[dict[str, object]] = []
    by_domain: dict[str, list[dict[str, object]]] = {name: [] for name in DOMAINS}
    seen: set[str] = set()
    normalized_statements: dict[str, str] = {}
    public_sources = [
        *THEORIES.glob("*.v"),
        *GENERIC_RENAMING_SOURCES,
        *GENERIC_QUERY_CONTEXT_SOURCES,
    ]
    for path in sorted(public_sources):
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
            topics = topics_for(name, domain_name, features)
            routes = semantic_routes(domain_name, path.name, name, features)
            entry = {
                "name": name,
                "kind": raw["kind"],
                "source": raw["source"],
                "line": raw["line"],
                "sourceDomain": source_domain_name,
                "semanticDomain": domain_name,
                "catalog": domain_name,
                "routes": list(routes),
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
        if "ownership" in domain:
            lines.extend([str(domain["ownership"]), ""])
        for entry in values:
            source = str(entry["source"])
            line = int(entry["line"])
            module = Path(source).name
            source_href = catalog_source_href(source)
            statement = str(entry["statement"])
            topics = list(entry["topics"])
            features = semantic_features(
                filename, module, str(entry["name"]), statement
            )
            cross_index = (
                ", ".join(
                    f"`{route}`"
                    for route in entry["routes"]  # type: ignore[union-attr]
                )
                or "primary card only"
            )
            lines.extend(
                [
                    f"## `{entry['name']}`",
                    "",
                    f"Source: [`{source}:{line}`]({source_href}#L{line})",
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
        "This is a compact, unranked navigation index. The Rocq source is authoritative; `manifest.json` contains each exact declaration statement plus deterministic source, primary-domain, cross-route, and topic metadata.",
        "",
        "Routes and topics are neutral filters, not proof plans. No declaration receives a relevance score or preferred position. Search results below are ordered only by source path, source line, and declaration name; use the reported total and explicit pages to inspect every match.",
        "",
        "The catalog is not an admissibility prover: use the generated `Queries.v` admissibility certificates for the concrete instance.",
        "",
        "## Neutral routes",
        "",
        "| Route | Scope |",
        "|---|---|",
    ]
    for route, route_spec in ROUTES.items():
        index_lines.append(
            f"| `{route}` | {str(route_spec['description']).capitalize()}. |"
        )
    index_lines.extend(
        [
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
            "## Stable paged search",
            "",
            "Run these commands from the Logos repository root. Each query reports the total number of matches and returns one explicit page; increase `page` until `offset >= total` rather than treating the first page as a shortlist.",
            "",
            "```bash",
            "catalog=theories/FormalSQL/catalog",
            'route="${ROUTE:?set ROUTE to one manifest route}"',
            'page="${PAGE:-0}"',
            f'page_size="${{PAGE_SIZE:-{CATALOG_PAGE_SIZE}}}"',
            "offset=$((page * page_size))",
            'jq --arg route "$route" --argjson offset "$offset" --argjson page_size "$page_size" \'',
            "  [.entries[] | select(.routes | index($route))]",
            "  | sort_by([.source, .line, .name])",
            "  | {total: length, offset: $offset, pageSize: $page_size,",
            "     entries: .[$offset:($offset + $page_size)]",
            "       | map({name, routes, catalog, source, line, summary})}",
            '\' "$catalog/manifest.json"',
            "",
            'pattern="${PATTERN:?set PATTERN to a declaration-name or topic regex}"',
            'jq --arg re "$pattern" --argjson offset "$offset" --argjson page_size "$page_size" \'',
            '  [.entries[] | select((.topics | join(" ")) | test($re; "i"))]',
            "  | sort_by([.source, .line, .name])",
            "  | {total: length, offset: $offset, pageSize: $page_size,",
            "     entries: .[$offset:($offset + $page_size)]",
            "       | map({name, routes, catalog, source, line})}",
            '\' "$catalog/manifest.json"',
            "",
            'name="${DECLARATION:?set DECLARATION to an exact declaration name}"',
            'card=$(jq -r --arg name "$name" \'.entries[] | select(.name == $name) | .catalog\' "$catalog/manifest.json")',
            'heading=$(printf \'## `%s`\' "$name")',
            'rg -n -F -A 35 "$heading" "$catalog/$card"',
            "```",
            "",
            "Keep every NULL, bag/list, order, schema, typmod, collation/timezone, cardinality, and runtime premise visible. Unsupported semantics remain fail-closed.",
            "",
        ]
    )
    manifest = {
        "schemaVersion": 3,
        "routes": ROUTES,
        "entries": entries,
    }
    index = "\n".join(index_lines)
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
