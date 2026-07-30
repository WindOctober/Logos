# Logos Core SQL Rewrite Benchmarks

This directory contains a small, local benchmark seed for SQL rewrite equivalence work. It intentionally vendors only the files needed for the initial Logos pipeline instead of cloning full upstream repositories.

## Contents

```text
verieql/literature/literature-rewrite.jsonlines  30 query pairs
verieql/calcite/calcite2.jsonlines               236 query pairs
rbot/tpch/                                      22 query pairs plus schema
rbot/dsb/                                       37 query pairs plus schema
tpcds/variants/                                14 TPC-DS base/variant query pairs plus schema
wetune/issues/issues.tsv                        50 real-world rewrite issue pairs
wetune/schemas/                                 raw schemas for 7 WeTune applications
wetune/schemas/core/                            normalized WeTune schemas plus semantic constraints
licenses/                                       upstream license files
ingestion.json                                  benchmark-to-Calcite-IR ingestion plan
```

The WeTune schema subset is restricted to the applications referenced by `wetune/issues/issues.tsv`: `diaspora`, `discourse`, `gitlab`, `lobsters`, `redmine`, `solidus`, and `spree`.

## Baseline Run Configuration

Paper-tool baseline runs should use the shared resource budget recorded at the
workflow root in:

```text
PaperTools/config/default.json
```

The current default configuration is:

```text
timeoutSeconds  14400  # 4 hours per case
maxParallel     6      # maximum concurrent cases
cpuCores        4      # CPU quota exposed per case when supported
memoryGb        16     # memory budget per case
SQLSolver Xmx   16g
Cosette image   shumo/cosette-frontend:latest
```

From the workflow root, the unified runner consumes this config by default:

```bash
PaperTools/scripts/run-benchmark-tools --tool all
```

Individual tools can be selected with `--tool sqlsolver`, `--tool qed`, or
`--tool cosette`. Use `--tool qed-cosette` to run the two external paper
baselines without executing SQLSolver.

## Cosette Frontend Profile

The generated Cosette profile is a frontend-compatibility profile over
Cosette's public DSL, not a general SQL normalizer. Before DSL embedding, shared
protected-aware lexical normalization removes comments, compacts structural
whitespace, and strips one structural trailing semicolon while leaving
protected text unchanged. A query may be reserialized from its exact generated
Calcite tree only after the tree's embedded SQL and schema are bound to the
current materialized case by content and digest.

`benchmarks/adapters/materializers/materialize_cosette.py` admits the
unmodified parser overlap plus a closed set of attested compatibility
lowerings. The ordinary bridge handles scans, inner products/joins, filters,
projects, and ordinary grouping over a small typed Rex surface. An exact
branch-wise compiler covers `Project`/inner-join/scan trees joined by
`UNION ALL`, including exact product distribution; four additional rules cover
grouped unobserved LEFT JOIN elimination, contradictory
integer INTERSECT, error-free FETCH 0, and a singleton VALUES constant group
key. A pair-level checker also recognizes base-relation occurrence renaming,
inner join/conjunct order, duplicate predicates, simple equality closure,
redundant strict integer bounds, GROUP BY key order, and a closed set of exact
paired `WHERE` TRUE-acceptance identities over fixed-width integer fields. The
last comparison is deliberately weaker than scalar Boolean equality: it may
identify `FALSE` and `UNKNOWN` only because both reject a row at that exact
filter site. A separate direct
Project-over-equality-Filter rule substitutes a typed integer constant only
after proving that the filter accepted the row and that every folded arithmetic
result remains in range. A closed preprocessing layer additionally handles a
small set of direct-field Boolean forms in `WHERE` or `INNER JOIN` matching:
NULL partitions, comparison-implied non-NULL tests, equality to a non-NULL
literal, finite two-integer exclusion searches, and selected error-free
searched-`CASE` forms. Direct, error-free n-ary `AND`/`OR` trees may also be
reassociated without changing operand order. These are TRUE-acceptance rewrites
only; they are never applied to a predicate returned by `SELECT`. A directly
adjacent null-rejecting filter may strengthen a LEFT or RIGHT join to INNER, or
a FULL join when it rejects null extension from both sides. Under an explicit
bag observation, a sort with no `OFFSET`/`FETCH` may be erased over direct
base-scan keys, or at the root over fixed-width integer aggregate outputs,
provided no ancestor consumes that order for a slice. The aggregate itself is
still evaluated. The bridge does not use NULL-sensitive self-join elimination,
general inequality reasoning, unmatched-row-preserving outer-join laws, or
slicing laws, and it never moves unresolved checked arithmetic across a
join/filter boundary. String trichotomy remains rejected because the bridge
has no shared collation contract, even when one concrete PostgreSQL query would
make the law valid.

Every applied rule records its exact IR/schema/SQL digests and side conditions
under `compatibilityLowering`; unknown trees and failed obligations retain the
source query unchanged. Rewrites involving `CASE`, NULL, or Boolean-test nodes
also carry an exact before/after Rex rewrite-site inventory. The source waiver
is granted only when source occurrence counts equal the bound IR inventory and
no risky node remains after preprocessing. Protected SQL regions are excluded
from feature detection. Every case is still emitted for an auditable tool run.
`metadata.json` binds the artifact and all three source inputs with
`cosetteFileSha256`, `sourceSchemaSha256`, `sourceSql1Sha256`, and
`sourceSql2Sha256`; the runner rejects a changed `case.cos` before execution.
It also reports two independent axes:
`syntaxCompatibility` covers the parser surface, while
`semanticProfileCompatibility` covers source constraints, SQL NULL behavior,
type lowering, and runtime-error/overflow semantics. Their blocker lists are
systematic; no case-id or rewrite-class allow/deny list participates in the
classification. The older aggregate `cosetteCompatibility` field is retained
only for generated-profile compatibility.

Call admission is closed: only unqualified `SUM`, `COUNT`, `MAX`, and `MIN`
over one simple unquoted column path, plus `COUNT(*)`, are classified as
compatible. Every other unprotected call name or aggregate form is flagged.
Parser acceptance alone is not sufficient: for example, a filtered branch of
`UNION ALL` remains flagged because the pinned public Rosette backend fails
that shape (`rosSelectList`) even though its front end parses it. Likewise, the
materializer does not move group-key `HAVING` below aggregation or replace
`EXISTS` over a global `COUNT(*)` with `TRUE`, because either rewrite could
avoid an aggregate overflow that PostgreSQL would have raised.

Outside those exact patterns, conservatively flagged constructs include CTEs,
outer joins, general `VALUES` and duplicate-eliminating set operations, window
and grouping-set syntax, general `CASE`, non-identity `CAST`, unclosed SQL NULL
and three-valued predicates, unsupported comparisons and functions,
date/interval and decimal values, checked integer arithmetic without
pair-identical error paths, general literal or subquery `IN`, `BETWEEN`,
observable ordering, and row slicing. These forms remain byte-present so
runtime errors, type resolution, grouping ordinals, collation, and predicate
precedence cannot be erased by an unproved rewrite.

## Benchmark Semantics

### VeriEQL Literature and Calcite

Files:

```text
verieql/literature/literature-rewrite.jsonlines
verieql/calcite/calcite2.jsonlines
```

These files are JSON Lines datasets. Each line is a self-contained equivalence instance with this shape:

```json
{
  "schema": { "...": "..." },
  "constraint": [ "... optional integrity constraints ..." ],
  "pair": [ "SQL before", "SQL after" ]
}
```

Schema and constraints are therefore **pair-level metadata**:

```text
one JSON line -> one schema/constraint environment -> one query pair
```

Different lines may reuse the same schema, but consumers should not assume a single global schema for the whole file. When generating solver inputs, the schema must be reconstructed from the `schema` field of the same JSON line as the query pair, and supported constraints should be translated from the same line's `constraint` field.

The generated SQLSolver metadata normalizes an absent or JSON `null` constraint
array to `[]` and records an `integrityContract` source list. Logos treats the
parser-facing `schema.sql` and, for pair-scoped inputs, the adjacent
`metadata.json#/constraints` value as one authoritative contract. Pair-level
constraints are therefore not lost merely because SQLSolver itself reads only
its narrower DDL file.

The `literature` subset contains compact rewrite examples from prior query-equivalence literature. The `calcite` subset contains rewrite examples derived from Apache Calcite optimizer tests.

The common PostgreSQL execution profile preserves the raw Calcite benchmark and
materializes coercions only after exact generated Calcite IR is available. Each
rewrite must match the case metadata, source-schema digest, query text, and an
inclusive Calcite source span; stale, overlapping, or unsupported evidence
fails closed. The materialized case metadata records the IR digest and every inserted cast under
`calciteCoercionMaterialization`.

The current 236-case audit requires two closed rewrite classes. Validator Rex
casts restore `NULL` result domains in `calcite-2` and the `VARCHAR`-to-`INTEGER`
comparisons in `calcite-133`, which PostgreSQL otherwise rejects. Aggregate
result casts align PostgreSQL's `SUM(BIGINT) -> NUMERIC` and
`AVG`/`STDDEV`/`VARIANCE(INTEGER) -> NUMERIC` signatures with the observable
types attested by Calcite. The affected aggregate cases are `calcite-2`,
`calcite-54`, `calcite-79`, `calcite-97`, `calcite-104`, `calcite-174`,
`calcite-175`, `calcite-176`, `calcite-202`, `calcite-212`, `calcite-219`,
`calcite-232`, `calcite-234`, and `calcite-276`. Common-subexpression
elimination may map several source aggregate occurrences to one Calcite call;
all exactly matching source occurrences are rewritten. These 15 affected cases
form the targeted rerun cohort after any in-flight campaign using the previous
generated inputs has finished.

No other value- or typmod-changing implicit Rex cast occurs in this retained
Calcite subset; 35 additional Rex casts change only Calcite nullability and are
not emitted as SQL. Bare `NULL` output columns remain unresolved rather than
being assigned an invented domain. The coercion pass also does not rewrite
`calcite-9` (ambiguous output `ORDER BY`), `calcite-158` (multi-argument
`COUNT(DISTINCT ...)`), `calcite-209`/`calcite-343` (ambiguous unqualified
columns), or `calcite-246` (`SINGLE_VALUE` is absent from PostgreSQL); these are
separate syntax/name-resolution gaps. Future row, collection, collation,
time-zone, or same-base typmod coercions require new exact IR-backed rules and
remain fail-closed until implemented. Aggregate casts align observable result
types for the PostgreSQL validation profile; they do not claim to reproduce a
separate Calcite runtime's internal accumulator implementation.

Only the standard-SQL subset is vendored here. Tool-specific VeriEQL inputs were removed, including symbolic predicates such as `B1(x)`, Calcite-internal dollar identifiers such as `$cor0.$f`, unquoted reserved identifiers such as `USER` and `YEAR`, and cases rejected by Calcite's standard SQL parser/validator as ambiguous or malformed. The upstream files originally contained 64 literature pairs and 397 Calcite pairs; this benchmark seed keeps 30 literature pairs and 236 Calcite pairs.

### R-Bot TPC-H and DSB

Directories:

```text
rbot/tpch/
rbot/dsb/
```

These are workload-level benchmark directories. Each workload has one shared
schema file and multiple source/rewrite query files:

```text
rbot/tpch/create_tables.sql
rbot/tpch/query*/query*_0.sql
rbot/tpch/query*/query*_1.sql

rbot/dsb/create_tables.sql
rbot/dsb/query*/query*_0.sql
rbot/dsb/query*/query*_1.sql
```

The pairing rule is:

```text
query*_0.sql -> one upstream workload input
query*_1.sql -> a fresh rewrite of that exact input
create_tables.sql -> shared schema for every pair in the workload
```

The upstream R-Bot repository treats its original `_0` and `_1` files as two
independent parameterized workload inputs; they are not an author-declared
rewrite pair. This corpus fixes that ambiguity by selecting `_0` before seeing
any solver result and replacing the old independent `_1` input with SQL emitted
by the pinned R-Bot Calcite rewrite engine at commit
`c9c90e5d7867888c3aaba86e4fc9e6d48f53b375`. The deterministic generation
profile tries applicable rules in lexical rule-name order and selects the first
single-rule, non-identity output that round-trips through that same pinned
R-Bot parser/serializer. This generation-integrity test is independent of
Logos, QED, Cosette, and SQLSolver results. Every generated target is nonempty
single-statement SQL, and the exact matched/tried/applied rules and file hashes
are recorded in `rbot/rewrite-pairs.manifest.json`.

The paper's per-query LLM responses and output SQL were not published. These
are therefore fresh, reproducible R-Bot-engine rewrites rather than a claim to
recover the paper run's stochastic RAG-selected, cost-best outputs. DSB
`query039_0.sql` is the only upstream file containing two executable queries;
the predeclared case-unit policy selects its first statement so all 59 cases
remain one-query pairs.

Regenerate the corpus from a clean pinned checkout with the local isolated
`JPype1==1.7.1` environment:

```bash
direnv exec . PaperTools/envs/rbot/bin/python \
  Logos/benchmarks/scripts/generate-rbot-pairs \
  --rbot-root PaperTools/R-Bot
```

So R-Bot is **workload-level schema**:

```text
TPC-H schema -> 22 query pairs
DSB schema  -> 37 query pairs
```

The sources and schemas come from the R-Bot query workload; the targets and
their provenance are generated as described above. They represent
optimizer-style rewrites over decision-support workloads without assuming that
every generated pair is semantically equivalent.

### TPC-DS Query Variants

Directory:

```text
tpcds/variants/
```

This subset contains materialized TPC-DS base/variant query pairs generated from the official base templates and query variant templates:

```text
tpcds/variants/create_tables.sql
tpcds/variants/manifest.tsv
tpcds/variants/query*/query*_0.sql
tpcds/variants/query*/query*_1.sql
```

The pairing rule is:

```text
query*_0.sql -> base query generated from query_templates/queryN.tpl
query*_1.sql -> variant query generated from query_variants/queryNa.tpl
create_tables.sql -> shared TPC-DS schema for every pair
```

So TPC-DS variants are also **workload-level schema**:

```text
TPC-DS schema -> 14 base/variant query pairs
```

The variants include rewrites such as manual `ROLLUP` expansion, `EXISTS`/`UNION ALL` rewrites, and window-function rewrites. The generated SQL may include dialect features such as `TOP`, `ROLLUP`, `GROUPING`, window functions, `FULL OUTER JOIN`, and `INTERSECT`; solver runners should consult `manifest.tsv` and normalize unsupported dialect constructs before invoking a solver. For `query036`, `query070`, and `query086`, PostgreSQL materialization expands the kit's same-level `lochierarchy` alias inside `ORDER BY CASE` back to its exact `GROUPING` expression; the case-local normalization report records every such site.

### WeTune Issues

Files:

```text
wetune/issues/issues.tsv
wetune/schemas/*.schema.sql
```

`issues.tsv` contains real-world application rewrite cases. Each row has the following tab-separated structure:

```text
id    app_name    rewrite_type    commit_url    before_sql    after_sql
```

The `app_name` column selects the schema:

```text
app_name -> wetune/schemas/<app_name>.base.schema.sql
app_name -> wetune/schemas/<app_name>.opt.schema.sql
```

WeTune is therefore **application-level schema**:

```text
one issue pair -> one application -> that application's schema
```

Both `base` and `opt` schemas are preserved because WeTune records application schemas before and after schema-level optimization passes. For query equivalence experiments, the default conservative choice is to use `<app_name>.base.schema.sql` unless the specific issue or rewrite explicitly requires the optimized schema.

The SQL input is best treated as Rails/ActiveRecord application SQL rather than a single standard dialect. The ingestion config currently normalizes queries through SQLGlot with a per-application reader:

```text
discourse, gitlab, redmine -> postgres
diaspora, lobsters, solidus, spree -> mysql
```

The raw schema files are real application dumps. PostgreSQL dumps may use schema-qualified declarations such as `CREATE TABLE public.posts (...)`, `SET`, `CREATE EXTENSION`, `CREATE SEQUENCE`, and `ALTER SEQUENCE`; MySQL dumps may include versioned comments, `DROP TABLE`, `AUTO_INCREMENT`, table storage options, and index declarations such as `KEY ...`. These deployment-oriented DDL forms are not part of the query-pair semantics and are not accepted uniformly by baseline solver frontends.

For frontend ingestion, WeTune schemas are normalized into:

```text
wetune/schemas/core/<app_name>.base.schema.sql
wetune/schemas/core/<app_name>.opt.schema.sql
```

The core schemas are generated by:

```bash
benchmarks/scripts/wetune-schema-sanitize --all
```

The generated `*.schema.sql` files are tool-facing frontend DDL. They keep `CREATE TABLE` declarations, columns, lowered scalar types, `NOT NULL`, `PRIMARY KEY`, and `UNIQUE` constraints in a form accepted by baseline parsers. Simple `CREATE UNIQUE INDEX ... (col, ...)` declarations are also exposed as uniqueness constraints. This frontend DDL may lower source types such as `DECIMAL`, `UUID`, `JSONB`, `INET`, or dialect-specific arrays to simpler parser-facing types.

The benchmark-level schema semantics are preserved in sibling sidecar files:

```text
wetune/schemas/core/<app_name>.base.schema.constraints.json
wetune/schemas/core/<app_name>.opt.schema.constraints.json
```

The sidecar records each column's original declaration, original source type, nullability, default, generated/auto-increment flags, and the parser-facing lowered type. It also preserves semantic constraints that baseline DDL parsers do not uniformly accept, such as `FOREIGN KEY`, `CHECK`, and partial or expression unique indexes. Dump/runtime DDL such as `SET`, `CREATE EXTENSION`, `CREATE SEQUENCE`, `ALTER SEQUENCE`, `DROP TABLE`, ordinary non-unique indexes, table storage options, and MySQL versioned comments is stripped because it does not define the query-pair schema semantics.

Consumers that claim fidelity to the raw source schema must reconcile the normalized
`*.schema.sql` file with the raw-type audit fields and constraints in its
`*.schema.constraints.json` sidecar. The frozen generated SQLSolver campaign described
below intentionally makes a narrower claim: normalized DDL is its type authority, while
the selected sidecar is authoritative only for integrity declarations.

The current schema subset contains only the applications referenced by `issues.tsv`, not the full WeTune schema collection.

## Independent Logos Materialization

Logos has its own generated profile, separate from every external solver
frontend:

```bash
benchmarks/scripts/materialize --tool logos --target all --force
```

The case layout is:

```text
benchmarks/core/.generated/logos/wetune-issues/<issue-id>/
benchmarks/core/.generated/logos/nonwetune-flat/<benchmark>__<case>/
  schema.sql
  sql1.sql
  sql2.sql
  metadata.json
```

For the frozen 59-case R-Bot corpus, all three SQL files are byte-identical to
the manifest-bound core schema/source/target files. In particular, PostgreSQL
identifier delimiters are retained: `query075` keeps `AS "year"` rather than
passing through the SQLSolver delimiter-elision policy. `metadata.json` records
the manifest digest, each exact input and output digest, an empty `repairs`
array, and the three files used as Calcite authority inputs. The materializer
does not call an external solver preprocessor, parser, planner, or admission
gate. The manifest itself is pinned to its campaign-launch digest, and any
manifest, source, or target digest mismatch fails closed. The DSB and TPC-H
schemas are independently pinned to
`805a1b08edf45fee0326efca6056ca881d92a00969e102fe731cf0781d24c0ea` and
`4fc33b97f09b573d748179f6a0a4d049f8d5057c7919ce2c163bb80e1af23eef`.
Before writing any R-Bot output, including a filtered developer run, the
materializer validates the exact exported 59-case superset and every frozen
schema/query digest. The canonical runner and Rust integrity loader then
independently revalidate adjacent files, identities, manifest/input hashes,
empty repairs, and Calcite authority bindings. Borrowed or jointly rewritten
metadata cannot establish a replacement authority.

Existing non-R-Bot inputs are an intentional byte regression boundary. The
Logos materializer regenerates their campaign-start representation from core
sources with a frozen compatibility renderer; it does not copy the old
`.generated/sqlsolver` tree at runtime. Historical SQLSolver-spelled metadata
values remain only where changing `metadata.json` would violate that byte
contract. The one frozen Calcite coercion class is a one-operand implicit
`VARCHAR`-to-`INTEGER` cast bound to the current authority metadata, embedded
query, exact source node span, and source text. Unsupported or stale evidence
fails closed.

An exhaustive scratch regeneration can enforce all 1,320 non-R-Bot hashes:

```bash
benchmarks/scripts/materialize \
  --tool logos \
  --target all \
  --output-root <fresh-scratch-root> \
  --force \
  --verify-non-rbot-baseline
```

SQLSolver has a narrower SQL frontend than Calcite and QED: it does not accept quoted
identifiers, and several ordinary application column names are reserved by its grammar
(`key`, `type`, `ref`, `value`, and similar names). For SQLSolver runs, generate a
separate materialized profile with:

```bash
benchmarks/scripts/materialize --tool sqlsolver --target wetune --force
```

This writes solver inputs under:

```text
benchmarks/core/.generated/sqlsolver/wetune-issues/<issue-id>/
  schema.sql
  sql1.sql
  sql2.sql
  metadata.json
```

The frozen SQLSolver campaign is a normalized benchmark profile. It first normalizes
each query with the same per-application SQLGlot reader as the Calcite ingestion path,
then consistently alpha-renames unsafe table and column identifiers in both the full
application core schema and the two queries. `metadata.json` records the source issue,
read dialect, materialized tables, semantic constraint counts, and every identifier
rename. SQLSolver's DDL frontend does not support the full constraint vocabulary, so its
`schema.sql` remains a frontend-compatible subset and SQLSolver alone does not enforce
the omitted forms. For Logos, `metadata.json.integrityContract` selects exactly the
`<app_name>.base.schema.constraints.json` sidecar together with
`metadata.json#/renamedIdentifiers` as the integrity source. The Logos loader consumes
ordinary unique keys, foreign keys, checks, and partial or expression unique indexes
from that source; these forms are not reimplemented by the materializer and are not
silently discarded.

This frozen generated profile deliberately distinguishes type authority from integrity
declaration authority. Every WeTune `metadata.json` records
`typeAuthority: "parser_facing_normalized_ddl"` and
`sidecarAuthority: "integrity_declarations_only"`. It also copies the sidecar's exact
`semanticSchema.typeSemantics` raw-source statement into
`sidecarRawTypeSemantics`, with `sidecarRawTypeSemanticsDisposition` set to
`"preserved_for_audit_but_overridden_by_typeAuthority"`. Thus the statement
remains auditable, but the generated campaign uses the normalized parser-facing DDL for
column types and uses the selected sidecar only for integrity declarations. This profile
does not claim fidelity to the raw WeTune source types.

The materializer also audits type lowerings against the actual query text. It records
observed lowerings in each case's `metadata.json`, including lowerings that may be
precision-sensitive or domain-specific, such as `DOUBLE PRECISION`, `DECIMAL`,
`TIMESTAMP`, `DATETIME`, unsigned integer types, `BYTEA`, `JSONB`, or `UUID`.
These audits are diagnostic metadata only: SQLSolver-facing inputs are still
materialized, and SQLSolver's own parser/solver run determines whether the case is
accepted, rejected, timed out, or proved unsupported by the tool frontend.

## Solver Input Mapping

The benchmark families should be normalized into solver input files with different schema lookup rules:

```text
VeriEQL:
  read one jsonline
  emit schema from jsonline["schema"]
  emit sql1/sql2 from jsonline["pair"]

R-Bot:
  use create_tables.sql for the workload
  pair query*_0.sql with query*_1.sql

TPC-DS variants:
  use tpcds/variants/create_tables.sql
  pair query*_0.sql with query*_1.sql
  read feature tags from tpcds/variants/manifest.tsv

WeTune:
  read one TSV row
  use app_name to select wetune/schemas/core/<app_name>.base.schema.sql by default
  load app-level semantic constraints from wetune/schemas/core/<app_name>.base.schema.constraints.json
  emit before_sql/after_sql from the same row
  for SQLSolver, use the generated profile under .generated/sqlsolver/wetune-issues/
```

SQLSolver expects separate `schema`, `sql1`, and `sql2` files. QED expects one `.sql` file containing `CREATE TABLE` declarations followed by exactly two `SELECT` statements, which can then be converted to QED JSON by `PaperTools/scripts/qed-parser`.

For non-WeTune SQLSolver runs, generate the flat input profile with:

```bash
benchmarks/scripts/materialize --tool sqlsolver --target nonwetune --force
```

This writes:

```text
benchmarks/core/.generated/sqlsolver/nonwetune-flat/<benchmark>__<case>/
  schema.sql
  sql1.sql
  sql2.sql
  metadata.json
```

Calcite ingestion and solver materialization are separate boundaries. The
ingestion `adapter` still controls the first normalization, but it is never used
as evidence that a target solver needs no further frontend work. A benchmark may
declare a target-specific `solverMaterialization.sqlsolver` policy. The R-Bot
policy removes double-quote delimiters only from complete ASCII lowercase
non-keyword identifiers under PostgreSQL's lowercase-folding rule. It neither
renames identifiers nor changes their spelling, so qualifications, correlated
bindings, output labels, aggregate expressions, and `ORDER BY` alias references
remain identical. Whitespace/`$`/case-sensitive/reserved identifiers stay quoted
and make the pair `Unsupport`, because SQLSolver rewrites those quotes as string
quotes and has no sound alternate delimiter for them.

Every enabled query-side transformation is recorded under
`normalizationForSolverRun.<side>.solverBoundary`, including its rule, affected
identifier counts, input/output digests, residual preservation obligations, and
protected-layout normalization. The materializer then invokes
`benchmarks/scripts/sqlsolver-preflight`, which mirrors SQLSolver's actual
preprocess, parser, validator, and relational planner and stops before proof
search. `solverFrontendPreflight` distinguishes materialization preservation
failure and target parser/validator/planner unsupported from a prover result;
only `status=ready` permits submission to the prover.

Schemas are independently lowered through SQLGlot into MySQL syntax for
SQLSolver's DDL parser. This is a DDL frontend adaptation: for example, unbounded
`VARCHAR` declarations are emitted as MySQL `TEXT` rather than `VARCHAR(255)`, so
the generated schema does not introduce an artificial string length bound.

To regenerate both SQLSolver benchmark subsets from one benchmark-facing entrypoint,
run:

```bash
benchmarks/scripts/materialize --tool sqlsolver --target all --force
```

New benchmark preprocessing commands should live under `benchmarks/scripts/`.

For QED runs, generate the parser-facing input profile with:

```bash
benchmarks/scripts/materialize --tool qed --target all --force
```

This writes:

```text
benchmarks/core/.generated/qed/wetune-issues/<issue-id>/
  qed.sql
  qed.json          # present when PaperTools/scripts/qed-parser accepts qed.sql
  metadata.json

benchmarks/core/.generated/qed/nonwetune-flat/<benchmark>__<case>/
  qed.sql
  qed.json          # present when PaperTools/scripts/qed-parser accepts qed.sql
  metadata.json
```

The QED profile emits a single `qed.sql` file per case, with simplified `CREATE TABLE`
declarations followed by the two queries. Every selected relation retains its complete
row type, including the column order observed by `SELECT *`; columns are never replaced
by a guessed dummy projection. `qed.sql` passes through exactly representable `NOT NULL`
constraints but deliberately withholds every PRIMARY/UNIQUE key while Calcite plans the
queries. This avoids QED parser's declaration-order versus name-sorted key-index bug from
changing a query before serialization. Safe primary keys and all-non-NULL unique keys are
instead recorded in `constraintCoverage.postParseKeys` (with `renderedKeys` retained as a
compatibility alias) and injected by column name only after the parser fixes the final
JSON field order. A key whose table or column was pruned is conservatively dropped and
recorded. Foreign keys, unattested checks, and nullable unique keys are likewise omitted;
`constraintCompatibility` records every conservative relaxation. Calcite/QED interval
precision spelling is patched where needed.

QED-specific query normalization is enabled only by an explicit
`solverMaterialization.qed` policy; absence keeps the historical output path
byte-for-byte unchanged. For an exact, unique, full positional base-table
column-alias list, the policy reorders aliases into QED's lexicographically
sorted base-column order while preserving each source-column-to-alias binding.
If either query side activates the policy, an unqualified SELECT-list star is
expanded pairwise only over a complete row of direct schema-attested base
relations, in source `FROM`/column order. Qualified alias stars, whole-row uses,
partial or ambiguous lists, CTE shadowing, and derived/NATURAL/USING star scopes
fail closed. Every admitted reorder and star expansion is recorded under
`normalizationForSolverRun.<side>.qedBaseTableColumnAliasOrder`, then the actual
QED parser/planner performs the frontend preflight.

The runner always tries that complete-row `qed.sql` first. If QED's name-sorted
table representation makes a relational star disagree with an explicit
source-order projection, an exact `qed-equivalence-star-expanded.sql` retry
rewrites only the exact root-star source span, without pruning the schema or
changing operators. Admission closes three independent order facts: syntactic
source `FROM` order and direct derived-table lineage, Calcite's direct `$N`
output lineage, and QED's final direct-column lineage after its name-sorted
schema representation. A same-typed column permutation therefore still fails
closed. The same retry may follow an EQ-only `NOT NULL VARCHAR` relaxation when
QED's charset bug is encountered first.

For VARCHAR-only equality fragments, a separate fallback uses an injective
encoding of every VARCHAR schema value into INTEGER while preserving NULL. A
direct `LIKE`/`NOT LIKE` over a VARCHAR column and a backslash-free literal,
with no `ESCAPE`, may be represented by one nullable uninterpreted Boolean
function: equality for every interpretation of that function implies equality
for PostgreSQL's concrete strict LIKE interpretation. Other string operations
fail closed. If live but unobserved columns instead keep the parser blocked,
`qed-equivalence-projected.sql` pushes projections and reports the combined
base-column dependency closure. It may remove only unused, direct `Column`
outputs from a derived SELECT; calls, casts, arithmetic, top-level outputs,
whole-row references, NATURAL JOIN, and JOIN USING fail closed. Consequently a
top-level `SELECT *` still has the original arity and order, while an unobserved
column on an auxiliary relation can be omitted. A query whose derived outputs
were not changed retains its normalized source text instead of being needlessly
reserialized.

Both the raw and normalized source sides must contain exactly one query
statement. Generated JSON is accepted only when it contains one complete pair
whose ordered output type vector and source-AST output arity agree. Metadata
keeps immutable `sourceConstraintCoverage` alongside each variant's active
coverage, and binds the source SQL, Calcite authority, generated SQL, and active
JSON by digest so a stale fallback cannot be replayed against new input. Every
relaxation or fallback is EQ-only; a non-EQ outcome from such a profile is
reported as non-authoritative.

For Cosette runs, generate the DSL-facing profile with:

```bash
benchmarks/scripts/materialize --tool cosette --target all --force
```

`benchmarks/scripts/cosette-preflight` checks the emitted DSL with the pinned
Cosette image's actual Coq and Rosette parser/translators. It calls only
`solver.gen_coq` and `solver.gen_rosette`, records each stage and exact input
digest, and never invokes `solver.solve` or either prover. Parser/translator
unsupported and timeout/resource outcomes therefore remain distinct from a
Cosette proof result. Because Cosette's own `solver.solve` lowercases the entire
DSL before those generators—including protected SQL strings—the preflight
faithfully mirrors that target-builtin normalization but records its before/after
digests and does not claim it preserves source semantics.

This writes:

```text
benchmarks/core/.generated/cosette/wetune-issues/<issue-id>/
  case.cos
  metadata.json

benchmarks/core/.generated/cosette/nonwetune-flat/<benchmark>__<case>/
  case.cos
  metadata.json
```

The Cosette profile is generated from the same `schema.sql`, `sql1.sql`, and
`sql2.sql` layout used by the SQLSolver profile, then rendered as Cosette DSL:

```text
schema ...
table ...
query q1 `...`;
query q2 `...`;
verify q1 q2;
```

This adapter is a tool-facing frontend profile. Cosette's public DSL exposes `int`
and `string` scalar sorts, so richer SQL scalar types are lowered into those two
sorts for frontend testing. Constraints not expressible in the DSL remain in the
source metadata and cause a semantic-profile blocker rather than being silently
treated as Cosette assumptions. IR-backed lowering starts only after the current
source SQL and ordered schema are bound to the generated Calcite artifacts. The
binding accepts exact SQL, or the closed WeTune presentation bridge authorized
by `metadata.json#/renamedIdentifiers`: injective simple-ASCII identifier
unquoting/renaming plus independently checked keyword/identifier case and
optional `AS` spelling. It never infers a rename from similar text. The current
typed Calcite `conditionRex`, `projectRex`, `aggCallDetails`, slice, and VALUES
payloads are validated before exposing their exact textual digests to the
older closed Cosette compiler; this is a checked representation view, not a
semantic rewrite.

TPC-DS's T-SQL-like `date + N days` spelling has one additional pair-level
bridge. It is admitted only when raw source, normalized SQLSolver input, the IR
frontend-input digests, and Calcite's embedded SQL agree on the complete
`BETWEEN` date/day multiset; exactly one whole source side must carry the unit,
the complete ordered source/IR schema must preserve every declared type, and
both sides are replayed as the same explicit DAY interval. An IR that collapses
declared `CHAR` to `VARCHAR`, as well as protected or unrelated lookalikes,
fails closed. These authority bridges can make a previously rejected query
available to the closed compatibility compiler without clearing its independent
semantic-profile obligations. Syntax or profile flags never pre-filter the run:
all emitted cases remain in the experimental denominator.

## Calcite IR Ingestion

Machine-readable ingestion rules live in:

```text
ingestion.json
```

The config records how each benchmark family should be exported to Logos' final Calcite JSON IR benchmark. The core generated layout is:

```text
benchmarks/core/.generated/calcite-ir/<benchmark-id>/<case-id>/
  before.calcite-ir.json
  after.calcite-ir.json
  metadata.json
```

`metadata.json` records source case information, schema scope, frontend adapter choice, dialects, feature tags, and constraints. Intermediate SQL files, normalized SQL, and normalization reports are debug-only artifacts and are not part of the core IR benchmark unless a runner explicitly enables `keepIntermediate`.

Export the configured benchmarks with:

```bash
scripts/export-benchmark-ir
```

Useful development options:

```bash
scripts/export-benchmark-ir --benchmark tpcds-variants --limit 1 --keep-intermediate
scripts/export-benchmark-ir --benchmark verieql-literature --case ex1sigmod92
```

## Sources

- VeriEQL: `https://github.com/VeriEQL/VeriEQL`
  - Commit: `493cbb81000205e33b0623cfd1c39106fa035fae`
  - Files: `benchmarks/literature/literature-rewrite.jsonlines`, `benchmarks/calcite/calcite2.jsonlines`
- R-Bot / LLM4Rewrite: `https://github.com/curtis-sun/LLM4Rewrite`
  - Commit: `c9c90e5d7867888c3aaba86e4fc9e6d48f53b375`
  - Files: `tpch/`, `dsb/`
- TPC-DS Kit: `https://github.com/gregrahn/tpcds-kit`
  - Commit: `5a3a817`
  - Files: generated from `tools/tpcds.sql`, `query_templates/queryN.tpl`, and `query_variants/queryNa.tpl`
- WeTune-code: `https://github.com/WeTune/WeTune-code`
  - Commit: `f99ee9ea0a1a4aa37d2a6f29f120fdaa92809bd4`
  - Files: `wtune_data/issues/issues`, relevant files from `wtune_data/schemas/`
