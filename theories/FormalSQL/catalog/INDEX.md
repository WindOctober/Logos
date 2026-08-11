# FormalSQL reusable lemma catalog

This is a compact, unranked navigation index. The Rocq source is authoritative; `manifest.json` contains each exact declaration statement plus deterministic source, primary-domain, cross-route, and topic metadata.

For a generated SQL equivalence goal, search the `possible` route first. Entries on the `scheduled` route are pointwise foundations only: a theorem for one fixed Boolean schedule is never a final possible-outcome certificate. Boolean schedules are unrelated to SQL row order; ordered operators continue to use exact list observations.

Routes and topics are neutral filters, not proof plans. No declaration receives a relevance score or preferred position. Search results below are ordered only by source path, source line, and declaration name; use the reported total and explicit pages to inspect every match.

The catalog is not an admissibility prover: use the generated `Queries.v` admissibility certificates for the concrete instance.

## Neutral routes

| Route | Scope |
|---|---|
| `possible` | Public relations, equivalences, errors, and transports over every legal boolean schedule. |
| `scheduled` | Internal pointwise evaluator and transport lemmas, not final sql certificates. |
| `renaming` | Collision-safe tuple, row, outcome, and nested query alpha-renaming. |
| `facade` | Compositional wrappers over generated tnull query terms. |
| `outcome` | Error-preserving query-outcome bridges and congruences. |
| `grouping` | Group construction, grouped-key filters, and aggregate outcomes. |
| `runtime` | Runtime-error propagation, absence, success, and lifting. |
| `projection` | Row extensionality, project operators, and projection congruence. |
| `filter` | Where/having row filters and filter congruence. |
| `join` | Cross, inner, outer, semi, anti, and functional joins. |
| `bag` | Bag equality, occurrence, and list/bag transport. |
| `ordered` | Order by, offset/fetch, windows, and order-sensitive equality. |
| `cardinality` | Row bounds, finite domains, and functional composition. |
| `schema` | Schema conformance, keys, and integrity facts. |
| `scalar` | Null/bool3, numeric, string, temporal, and scalar subqueries. |

## Primary semantic cards

| Goal shape / SQL feature | Focused catalog | Declarations |
|---|---|---:|
| UNKNOWN/TRUE/FALSE, strict predicates, NULL tests, comparisons, CASE | [null-predicates.md](null-predicates.md) | 97 |
| query-level nullable syntax adapters, query-local bindings, tuple projection, attribute lookup | [query-syntax-bridges.md](query-syntax-bridges.md) | 73 |
| collision-safe tuple, row, outcome, and compositional query alpha-renaming | [renaming-transport.md](renaming-transport.md) | 155 |
| NUMERIC representation, precision/scale, division, rounding, AVG states | [numeric-primitives.md](numeric-primitives.md) | 125 |
| INTEGER/BIGINT bounds, derived NUMERIC laws, floats, casts, overflow | [numeric-derived.md](numeric-derived.md) | 127 |
| integer bit operations, shifts, BIT_AND/BIT_OR aggregate laws | [bitwise.md](bitwise.md) | 47 |
| CHAR/VARCHAR/TEXT, LIKE, substring, DATE/TIME/TIMESTAMP/TIMESTAMPTZ | [string-temporal.md](string-temporal.md) | 80 |
| bag/list abstraction, multiplicity, filter/project/join/set operators | [relational-algebra.md](relational-algebra.md) | 288 |
| exact order and multiplicity, ORDER BY, OFFSET/LIMIT/FETCH, DISTINCT | [ordered-observation.md](ordered-observation.md) | 116 |
| COUNT/SUM/MIN/MAX/AVG, ALL/DISTINCT, empty/all-NULL, grouping, and SINGLE_VALUE scalar-subquery cardinality | [aggregate-grouping.md](aggregate-grouping.md) | 239 |
| EXISTS, IN, ANY/ALL-style quantified predicates, correlated query/scalar-expression goals; use aggregate/grouping for SINGLE_VALUE scalar cardinality | [subquery-predicates.md](subquery-predicates.md) | 109 |
| typing/schema conformance, NOT NULL, PK/UNIQUE/FK/CHECK, unique indexes | [schema-integrity.md](schema-integrity.md) | 113 |
| row-count bounds, functional joins, filters, groups, finite images | [cardinality-composition.md](cardinality-composition.md) | 137 |
| success/error outcomes, safe vs error-preserving equivalence, rewrite contracts | [runtime-verification-rewrite.md](runtime-verification-rewrite.md) | 356 |

## Stable paged search

Run these commands from the Logos repository root. Each query reports the total number of matches and returns one explicit page; increase `page` until `offset >= total` rather than treating the first page as a shortlist.

```bash
catalog=theories/FormalSQL/catalog
route="${ROUTE:?set ROUTE to one manifest route}"
page="${PAGE:-0}"
page_size="${PAGE_SIZE:-32}"
offset=$((page * page_size))
jq --arg route "$route" --argjson offset "$offset" --argjson page_size "$page_size" '
  [.entries[] | select(.routes | index($route))]
  | sort_by([.source, .line, .name])
  | {total: length, offset: $offset, pageSize: $page_size,
     entries: .[$offset:($offset + $page_size)]
       | map({name, interfaceLayer, replacement, routes, catalog, source, line, summary})}
' "$catalog/manifest.json"

pattern="${PATTERN:?set PATTERN to a declaration-name or topic regex}"
jq --arg re "$pattern" --argjson offset "$offset" --argjson page_size "$page_size" '
  [.entries[] | select((.topics | join(" ")) | test($re; "i"))]
  | sort_by([.source, .line, .name])
  | {total: length, offset: $offset, pageSize: $page_size,
     entries: .[$offset:($offset + $page_size)]
       | map({name, interfaceLayer, replacement, routes, catalog, source, line})}
' "$catalog/manifest.json"

name="${DECLARATION:?set DECLARATION to an exact declaration name}"
card=$(jq -r --arg name "$name" '.entries[] | select(.name == $name) | .catalog' "$catalog/manifest.json")
heading=$(printf '## `%s`' "$name")
rg -n -F -A 35 "$heading" "$catalog/$card"
```

Keep every NULL, bag/list, order, schema, typmod, collation/timezone, cardinality, and runtime premise visible. Unsupported semantics remain fail-closed.
