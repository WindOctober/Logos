# FormalSQL reusable lemma catalog

This is a compact navigation index. The Rocq source is authoritative; `manifest.json` contains the exact declaration statements plus deterministic primary-domain, cross-route, and route-rank metadata. Lower rank means a better first read.

Do not open a whole domain card. Pick one route, take at most eight ranked results, then open only the exact declaration block in its primary card (or its authoritative source line). The catalog is not an admissibility prover: use the generated `Queries.v` admissibility certificates for the concrete instance.

## Fast routes

### `facade` — high-level TNull proof facade

First-stop compositional wrappers over generated tnull query terms.

| Rank | Declaration | Primary card |
|---:|---|---|
| 0 | `tnull_direct_columns_group_outcome_equiv_of_projected_support` | [aggregate-grouping.md](aggregate-grouping.md) |
| 0 | `tnull_join_condition_pred_acceptance_exact_safe` | [runtime-verification-rewrite.md](runtime-verification-rewrite.md) |
| 2 | `tnull_eval_group_bag_direct_columns_true_no_error` | [aggregate-grouping.md](aggregate-grouping.md) |
| 2 | `tnull_projection_envs_eq_of_select_items` | [relational-algebra.md](relational-algebra.md) |
| 2 | `tnull_row_eq_trans` | [relational-algebra.md](relational-algebra.md) |

### `outcome` — query outcome equivalence

Error-preserving query-outcome bridges and congruences.

| Rank | Declaration | Primary card |
|---:|---|---|
| 0 | `eval_grouping_sets_outcome_Forall2_congr` | [aggregate-grouping.md](aggregate-grouping.md) |
| 0 | `tnull_direct_columns_group_outcome_equiv_of_projected_support` | [aggregate-grouping.md](aggregate-grouping.md) |
| 2 | `eval_join_bag_safe_of_acceptance_projection_exact` | [relational-algebra.md](relational-algebra.md) |
| 4 | `query_expr_group_outcome_equiv_of_supported_child_outcomes` | [aggregate-grouping.md](aggregate-grouping.md) |
| 4 | `tnull_eval_group_bag_direct_columns_true_equiv_of_projection_support` | [aggregate-grouping.md](aggregate-grouping.md) |

### `grouping` — grouping and HAVING

Group construction, grouped-key filters, and aggregate outcomes.

| Rank | Declaration | Primary card |
|---:|---|---|
| 0 | `eval_grouping_sets_outcome_Forall2_congr` | [aggregate-grouping.md](aggregate-grouping.md) |
| 0 | `tnull_closed_group_sum_numeric_dot_argument_observations_permutation_rows` | [numeric-derived.md](numeric-derived.md) |
| 0 | `tnull_direct_columns_group_outcome_equiv_of_projected_support` | [aggregate-grouping.md](aggregate-grouping.md) |
| 2 | `eval_grouping_sets_success_fold_iff` | [aggregate-grouping.md](aggregate-grouping.md) |
| 2 | `tnull_closed_group_sum_numeric_dot_value_runtime_exact` | [numeric-derived.md](numeric-derived.md) |

### `runtime` — runtime safety and errors

Runtime-error propagation, absence, success, and lifting.

| Rank | Declaration | Primary card |
|---:|---|---|
| 0 | `eval_grouping_sets_outcome_Forall2_congr` | [aggregate-grouping.md](aggregate-grouping.md) |
| 2 | `eval_join_bag_safe_of_acceptance_projection_exact` | [relational-algebra.md](relational-algebra.md) |
| 2 | `tnull_eval_group_bag_direct_columns_true_no_error` | [aggregate-grouping.md](aggregate-grouping.md) |
| 4 | `eval_grouping_sets_error_prefix_iff` | [aggregate-grouping.md](aggregate-grouping.md) |
| 4 | `tnull_direct_columns_group_outcome_equiv_of_projected_support` | [aggregate-grouping.md](aggregate-grouping.md) |

## Decision tree

1. For an error-preserving query goal, inspect the ranked `facade` results and then `outcome`; this cross-index includes generic bridges from `ProofAgentFacade.v` and `OrderedQueryFacts.v`.
2. For GROUP BY/HAVING or SINGLE_VALUE, inspect `grouping`; prefer a facade wrapper before lower-level grouping internals.
3. For a separate safety premise, inspect `runtime`; do not identify a runtime error with NULL or empty success.
4. For the smallest differing relational operator, use `projection`, `filter`, `join`, `bag`, `ordered`, or `cardinality` through the bounded query below.
5. For a scalar or schema obligation, use `scalar` or `schema`. Use `query-syntax-bridges.md` only for a tuple/syntax adapter.

## Primary semantic cards

| Goal shape / SQL feature | Focused catalog | Declarations |
|---|---|---:|
| UNKNOWN/TRUE/FALSE, strict predicates, NULL tests, comparisons, CASE | [null-predicates.md](null-predicates.md) | 97 |
| query-level nullable syntax adapters, tuple projection, attribute lookup | [query-syntax-bridges.md](query-syntax-bridges.md) | 43 |
| NUMERIC representation, precision/scale, division, rounding, AVG states | [numeric-primitives.md](numeric-primitives.md) | 81 |
| INTEGER/BIGINT bounds, derived NUMERIC laws, floats, casts, overflow | [numeric-derived.md](numeric-derived.md) | 127 |
| integer bit operations, shifts, BIT_AND/BIT_OR aggregate laws | [bitwise.md](bitwise.md) | 43 |
| CHAR/VARCHAR/TEXT, LIKE, substring, DATE/TIME/TIMESTAMP/TIMESTAMPTZ | [string-temporal.md](string-temporal.md) | 69 |
| bag/list abstraction, multiplicity, filter/project/join/set operators | [relational-algebra.md](relational-algebra.md) | 184 |
| exact order and multiplicity, ORDER BY, OFFSET/LIMIT/FETCH, DISTINCT | [ordered-observation.md](ordered-observation.md) | 45 |
| COUNT/SUM/MIN/MAX/AVG, ALL/DISTINCT, empty/all-NULL, grouping, and SINGLE_VALUE scalar-subquery cardinality | [aggregate-grouping.md](aggregate-grouping.md) | 166 |
| EXISTS, IN, ANY/ALL-style quantified predicates, correlated query/formula goals; use aggregate/grouping for SINGLE_VALUE scalar cardinality | [subquery-predicates.md](subquery-predicates.md) | 53 |
| typing/schema conformance, NOT NULL, PK/UNIQUE/FK/CHECK, unique indexes | [schema-integrity.md](schema-integrity.md) | 64 |
| row-count bounds, functional joins, filters, groups, finite images | [cardinality-composition.md](cardinality-composition.md) | 101 |
| success/error outcomes, safe vs error-preserving equivalence, rewrite contracts | [runtime-verification-rewrite.md](runtime-verification-rewrite.md) | 52 |

## Bounded ranked search

```bash
route=outcome
jq --arg route "$route" '[.entries[] | select(.routes | index($route))] | sort_by([.routeRanks[$route], .name]) | .[:8] | map({name, rank: .routeRanks[$route], catalog, source, line, summary})' lemma-catalog/manifest.json
jq --arg re 'projection|cross join' '[.entries[] | select((.topics | join(" ")) | test($re; "i"))] | sort_by([.rank, .name]) | .[:8] | map({name, rank, routes, catalog, source, line})' lemma-catalog/manifest.json
rg -n -A 35 '^## `DECLARATION_NAME`$' lemma-catalog/PRIMARY_CARD.md
```

Stop after two bounded searches for one obstacle. Keep every NULL, bag/list, order, schema, typmod, collation/timezone, cardinality, and runtime premise visible. Unsupported semantics remain fail-closed.
