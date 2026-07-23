# FormalSQL reusable lemma catalog

This is a compact navigation index. The Rocq source is authoritative; `manifest.json` contains the exact declaration statements plus deterministic primary-domain, cross-route, and route-rank metadata. Lower rank means a better first read.

Do not open a whole domain card. Pick one route, take at most eight ranked results, then open only the exact declaration block in its primary card (or its authoritative source line). The catalog is not an admissibility prover: use the generated `Queries.v` admissibility certificates for the concrete instance.

## Fast routes

### `facade` — high-level TNull proof facade

First-stop compositional wrappers over generated tnull query terms.

| Rank | Declaration | Primary card |
|---:|---|---|
| 2 | `tnull_qexpr_bag_outcome_eq_of_runtime_and_bag_eq` | [runtime-verification-rewrite.md](runtime-verification-rewrite.md) |
| 3 | `tnull_direct_table_projection_query_bag_eq` | [relational-algebra.md](relational-algebra.md) |
| 4 | `tnull_direct_projection_query_bag_eq` | [relational-algebra.md](relational-algebra.md) |
| 4 | `tnull_double_projection_query_bag_eq` | [relational-algebra.md](relational-algebra.md) |
| 4 | `tnull_single_double_projection_query_bag_eq` | [relational-algebra.md](relational-algebra.md) |

### `outcome` — query outcome equivalence

Error-preserving query-outcome bridges and congruences.

| Rank | Declaration | Primary card |
|---:|---|---|
| 2 | `tnull_qexpr_bag_outcome_eq_of_runtime_and_bag_eq` | [runtime-verification-rewrite.md](runtime-verification-rewrite.md) |
| 22 | `query_expr_filter_outcome_equiv_of_always_true` | [runtime-verification-rewrite.md](runtime-verification-rewrite.md) |
| 24 | `query_expr_filter_outcome_equiv_of_global_acceptance` | [runtime-verification-rewrite.md](runtime-verification-rewrite.md) |
| 24 | `query_expr_outcome_equiv_of_eval_iff` | [runtime-verification-rewrite.md](runtime-verification-rewrite.md) |
| 24 | `query_expr_outcome_equiv_of_global_typed` | [runtime-verification-rewrite.md](runtime-verification-rewrite.md) |

### `grouping` — grouping and HAVING

Group construction, grouped-key filters, and aggregate outcomes.

| Rank | Declaration | Primary card |
|---:|---|---|
| 2 | `tnull_eval_groups_having_key_conj_after_bag_filter_exact` | [aggregate-grouping.md](aggregate-grouping.md) |
| 2 | `tnull_eval_groups_having_key_conj_filter_exact` | [aggregate-grouping.md](aggregate-grouping.md) |
| 20 | `eval_groups_having_key_conj_after_bag_formula_filter_exact` | [aggregate-grouping.md](aggregate-grouping.md) |
| 20 | `eval_groups_having_key_conj_filter_exact` | [aggregate-grouping.md](aggregate-grouping.md) |
| 24 | `eval_grouping_sets_cons_error_iff` | [aggregate-grouping.md](aggregate-grouping.md) |

### `runtime` — runtime safety and errors

Runtime-error propagation, absence, success, and lifting.

| Rank | Declaration | Primary card |
|---:|---|---|
| 2 | `tnull_qexpr_bag_outcome_eq_of_runtime_and_bag_eq` | [runtime-verification-rewrite.md](runtime-verification-rewrite.md) |
| 3 | `tnull_cross_join_runtime_error_none` | [runtime-verification-rewrite.md](runtime-verification-rewrite.md) |
| 4 | `tnull_pi_runtime_error_none` | [runtime-verification-rewrite.md](runtime-verification-rewrite.md) |
| 4 | `tnull_sigma_runtime_error_none` | [runtime-verification-rewrite.md](runtime-verification-rewrite.md) |
| 6 | `tnull_cross_join_runtime_error_congr` | [runtime-verification-rewrite.md](runtime-verification-rewrite.md) |

## Decision tree

1. For an error-preserving query goal, inspect the ranked `facade` results and then `outcome`; this cross-index includes generic bridges from `ProofAgentFacade.v` and `OrderedQueryFacts.v`.
2. For GROUP BY/HAVING or SINGLE_VALUE, inspect `grouping`; prefer a facade wrapper before lower-level grouping internals.
3. For a separate safety premise, inspect `runtime`; do not identify a runtime error with NULL or empty success.
4. For the smallest differing relational operator, use `projection`, `filter`, `join`, `bag`, `ordered`, or `cardinality` through the bounded query below.
5. For a scalar or schema obligation, use `scalar` or `schema`. Use `query-syntax-bridges.md` only for a tuple/syntax adapter.

## Primary semantic cards

| Goal shape / SQL feature | Focused catalog | Declarations |
|---|---|---:|
| UNKNOWN/TRUE/FALSE, strict predicates, NULL tests, comparisons, CASE | [null-predicates.md](null-predicates.md) | 100 |
| query-level nullable syntax adapters, tuple projection, attribute lookup | [query-syntax-bridges.md](query-syntax-bridges.md) | 62 |
| NUMERIC representation, precision/scale, division, rounding, AVG states | [numeric-primitives.md](numeric-primitives.md) | 85 |
| INTEGER/BIGINT bounds, derived NUMERIC laws, floats, casts, overflow | [numeric-derived.md](numeric-derived.md) | 125 |
| integer bit operations, shifts, BIT_AND/BIT_OR aggregate laws | [bitwise.md](bitwise.md) | 43 |
| CHAR/VARCHAR/TEXT, LIKE, substring, DATE/TIME/TIMESTAMP/TIMESTAMPTZ | [string-temporal.md](string-temporal.md) | 69 |
| bag/list abstraction, multiplicity, filter/project/join/set operators | [relational-algebra.md](relational-algebra.md) | 115 |
| exact order and multiplicity, ORDER BY, OFFSET/LIMIT/FETCH, DISTINCT | [ordered-observation.md](ordered-observation.md) | 38 |
| COUNT/SUM/MIN/MAX/AVG, ALL/DISTINCT, empty/all-NULL, grouping, and SINGLE_VALUE scalar-subquery cardinality | [aggregate-grouping.md](aggregate-grouping.md) | 136 |
| EXISTS, IN, ANY/ALL-style quantified predicates, correlated query/formula goals; use aggregate/grouping for SINGLE_VALUE scalar cardinality | [subquery-predicates.md](subquery-predicates.md) | 31 |
| typing/schema conformance, NOT NULL, PK/UNIQUE/FK/CHECK, unique indexes | [schema-integrity.md](schema-integrity.md) | 62 |
| row-count bounds, functional joins, filters, groups, finite images | [cardinality-composition.md](cardinality-composition.md) | 88 |
| success/error outcomes, safe vs error-preserving equivalence, rewrite contracts | [runtime-verification-rewrite.md](runtime-verification-rewrite.md) | 51 |

## Bounded ranked search

```bash
route=outcome
jq --arg route "$route" '[.entries[] | select(.routes | index($route))] | sort_by([.routeRanks[$route], .name]) | .[:8] | map({name, rank: .routeRanks[$route], catalog, source, line, summary})' lemma-catalog/manifest.json
jq --arg re 'projection|cross join' '[.entries[] | select((.topics | join(" ")) | test($re; "i"))] | sort_by([.rank, .name]) | .[:8] | map({name, rank, routes, catalog, source, line})' lemma-catalog/manifest.json
rg -n -A 35 '^## `DECLARATION_NAME`$' lemma-catalog/PRIMARY_CARD.md
```

Stop after two bounded searches for one obstacle. Keep every NULL, bag/list, order, schema, typmod, collation/timezone, cardinality, and runtime premise visible. Unsupported semantics remain fail-closed.
