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

The `literature` subset contains compact rewrite examples from prior query-equivalence literature. The `calcite` subset contains rewrite examples derived from Apache Calcite optimizer tests.

Only the standard-SQL subset is vendored here. Tool-specific VeriEQL inputs were removed, including symbolic predicates such as `B1(x)`, Calcite-internal dollar identifiers such as `$cor0.$f`, unquoted reserved identifiers such as `USER` and `YEAR`, and cases rejected by Calcite's standard SQL parser/validator as ambiguous or malformed. The upstream files originally contained 64 literature pairs and 397 Calcite pairs; this benchmark seed keeps 30 literature pairs and 236 Calcite pairs.

### R-Bot TPC-H and DSB

Directories:

```text
rbot/tpch/
rbot/dsb/
```

These are workload-level benchmark directories. Each workload has one shared schema file and multiple before/after query files:

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
query*_0.sql -> before query
query*_1.sql -> after query
create_tables.sql -> shared schema for every pair in the workload
```

So R-Bot is **workload-level schema**:

```text
TPC-H schema -> 22 query pairs
DSB schema  -> 37 query pairs
```

These pairs come from the R-Bot query rewrite benchmark and are intended to represent optimizer-style rewrites over decision-support workloads.

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

The variants include rewrites such as manual `ROLLUP` expansion, `EXISTS`/`UNION ALL` rewrites, and window-function rewrites. The generated SQL may include dialect features such as `TOP`, `ROLLUP`, `GROUPING`, window functions, `FULL OUTER JOIN`, and `INTERSECT`; solver runners should consult `manifest.tsv` and normalize unsupported dialect constructs before invoking a solver.

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
scripts/wetune-schema-sanitize --all
```

The generated `*.schema.sql` files are tool-facing frontend DDL. They keep `CREATE TABLE` declarations, columns, lowered scalar types, `NOT NULL`, `PRIMARY KEY`, and `UNIQUE` constraints in a form accepted by baseline parsers. Simple `CREATE UNIQUE INDEX ... (col, ...)` declarations are also exposed as uniqueness constraints. This frontend DDL may lower source types such as `DECIMAL`, `UUID`, `JSONB`, `INET`, or dialect-specific arrays to simpler parser-facing types.

The benchmark-level schema semantics are preserved in sibling sidecar files:

```text
wetune/schemas/core/<app_name>.base.schema.constraints.json
wetune/schemas/core/<app_name>.opt.schema.constraints.json
```

The sidecar records each column's original declaration, original source type, nullability, default, generated/auto-increment flags, and the parser-facing lowered type. It also preserves semantic constraints that baseline DDL parsers do not uniformly accept, such as `FOREIGN KEY`, `CHECK`, and partial or expression unique indexes. Dump/runtime DDL such as `SET`, `CREATE EXTENSION`, `CREATE SEQUENCE`, `ALTER SEQUENCE`, `DROP TABLE`, ordinary non-unique indexes, table storage options, and MySQL versioned comments is stripped because it does not define the query-pair schema semantics.

Each generated schema also has a sibling `*.report.json` audit file with retained table/column/key counts, type-lowering counts, extracted semantic-constraint counts, unsupported semantic-constraint counts, and non-semantic dropped-item counts. For a semantics-preserving benchmark interpretation, consumers must treat the normalized `*.schema.sql` file and its `*.schema.constraints.json` sidecar as one schema environment. If a baseline solver cannot consume the sidecar column types or constraints, that is recorded as a frontend/tool limitation rather than removed from the benchmark semantics.

The current schema subset contains only the applications referenced by `issues.tsv`, not the full WeTune schema collection.

SQLSolver has a narrower SQL frontend than Calcite and QED: it does not accept quoted
identifiers, and several ordinary application column names are reserved by its grammar
(`key`, `type`, `ref`, `value`, and similar names). For SQLSolver runs, generate a
separate materialized profile with:

```bash
scripts/wetune-sqlsolver-materialize --force
```

This writes solver inputs under:

```text
benchmarks/core/.generated/sqlsolver/wetune-issues/<issue-id>/
  schema.sql
  sql1.sql
  sql2.sql
  metadata.json
```

The SQLSolver profile is a semantics-preserving frontend adaptation. It first normalizes
each query with the same per-application SQLGlot reader as the Calcite ingestion path,
then consistently alpha-renames unsafe table and column identifiers in both the full
application core schema and the two queries. `metadata.json` records the source issue,
read dialect, materialized tables, semantic constraint counts, and every identifier
rename. SQLSolver's DDL frontend does not support the full constraint vocabulary, so
foreign keys and checks remain in the benchmark sidecar metadata instead of being
lowered into SQLSolver's input DDL.

The materializer also audits type lowerings against the actual query text. It only
generates runnable SQLSolver inputs when the observed lowerings are known to preserve
the query's equivalence result, for example identifier alpha-renaming or a lowered
column used only in `IS NULL` / `IS NOT NULL`. If a query observes a lowered
precision-sensitive, temporal, unsigned, or domain-specific type, such as
`DOUBLE PRECISION`, `DECIMAL`, `TIMESTAMP`, `DATETIME`, unsigned integer types,
`BYTEA`, `JSONB`, or `UUID`, the case is left as metadata-only with
`status: "unsupported"`. Such cases are counted as SQLSolver frontend limitations,
not as benchmark rewrites with weakened semantics.

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
