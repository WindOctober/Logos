# Logos

Logos is a Rocq-based theorem-proving workspace for LLM-assisted verification of SQL schema rewrite equivalence. The intended trust boundary is explicit: LLMs may propose rewrites, lemmas, proof plans, and proof scripts, but equivalence claims must be checked by Rocq.

## Formal SQL Semantics

Logos builds on the existing SQLCoq/SQLFormalSemantics development instead of redefining SQL semantics from scratch:

- `vendor/FormalSQL`: a Rocq-modernized fork of SQLCoq/SQLFormalSemantics. It provides SQL abstract syntax, bag semantics, SQLAlgebra, and semantic functions such as `eval_sql_query` and `eval_query`.

The verification layer is expected to generate proof goals against those definitions. A typical theorem shape is:

```coq
forall instance env,
  well_sorted_sql_table T basesort instance ->
  eval_sql_query env q_before =BE= eval_sql_query env q_after.
```

For rewrites that are easier to reason about algebraically, Logos should translate SQL queries through SQLCoq's `SQLAlgebra` layer and prove equivalence over `eval_query`.

Logos does not vendor SQLToNRACert, DBCert, or the Q*Cert NRAEnv-to-JavaScript compilation path. Those components target certified SQL-to-JavaScript compilation, while Logos focuses on SQL rewrite equivalence.

## Counterexample Semantics

The deterministic counterexample checker currently executes candidate witnesses with PostgreSQL semantics. This is a deliberate engineering boundary, not a claim that PostgreSQL is the SQL standard itself.

In principle, query equivalence should be stated against a precise SQL semantics. In practice, there is no widely used, executable, full standard-SQL reference interpreter that covers the benchmark dialects we use. Existing tools and benchmark sources each expose their own accepted SQL subset or dialect. Logos therefore uses PostgreSQL as the concrete execution semantics for counterexample validation: inputs are normalized toward PostgreSQL-compatible SQL, and a validated counterexample means the two queries differ under PostgreSQL's interpretation.

The checker treats positional output types as part of query equivalence. If the two queries return different numbers of columns or incompatible PostgreSQL output types, Logos records this as a verified output-schema mismatch. Output column names are not part of the comparison; columns are compared by ordinal position.

The proof path remains separate: when Logos lowers queries into FormalSQL/Rocq, equivalence obligations are checked against the formal semantics available there. PostgreSQL-based counterexamples are used as deterministic evidence for non-equivalence in the executable frontend pipeline, while Rocq proof obligations are the intended trust boundary for formal equivalence claims.

The CLI reflects this distinction in its result display. `NOT EQUIVALENT` is shown as a red terminal result when a PostgreSQL witness is validated. A proof-agent run that exits successfully is reported as `proof_agent_run_completed`, but the overall solver result remains `equivalence_verification_incomplete` unless Logos has actually identified and checked a complete equivalence theorem. Machine consumers should use `--output json`; the default `--output pretty` is intended for interactive terminal use.

## Submodules

The SQLCoq dependency is pinned as a Git submodule:

```bash
git submodule update --init --recursive
```

Current configuration:

```text
vendor/FormalSQL  git@github.com:WindOctober/FormalSQL.git  branch master
```

## Build

Logos uses the Rocq-compatible SQLCoq fork in `vendor/FormalSQL`. The workspace `.envrc` exports `ROCQ_OPAM_SWITCH`, `OPAM_SWITCH`, `ROCQLIB`, and `OCAMLFIND_CONF` for the Rocq 9.2 environment. Rocq build targets require `ROCQ_OPAM_SWITCH` or `OPAM_SWITCH`; run `direnv allow` at the workspace root or set one of those variables explicitly before invoking `make formal-sql` or `make smoke`.

```bash
make submodules
make formal-sql
make smoke
```

The smoke test compiles `theories/Smoke.v` and checks that Logos can import the SQLCoq `SQLFS` semantics library.

If a compatible Rocq environment is already available and you only want to inspect the submodule state, run:

```bash
make submodules
make status
```

## Calcite Frontend Prototype

Logos includes a minimal Apache Calcite CLI wrapper for testing whether a Java frontend can turn SQL schemas and queries into an intermediate representation suitable for later Rocq code generation. The wrapper is a small Maven-managed Java project; its `pom.xml` declares the Calcite dependency, Java version, and CLI entry point.

The wrapper lives in:

```text
frontend/calcite-wrapper
```

Run the bundled example with:

```bash
make calcite-ir
```

The Makefile target runs the default ingestion pipeline, which normalizes SQL through the SQLGlot dialect adapter and then invokes Calcite. To bypass dialect normalization and invoke the Calcite wrapper directly:

```bash
scripts/calcite-ir \
  --schema frontend/calcite-wrapper/examples/schema.sql \
  --sql frontend/calcite-wrapper/examples/query.sql
```

The command emits JSON with two main views:

- `sqlAst`: Calcite's `SqlNode` syntax tree, useful for inspecting parser output.
- `rel`: Calcite's validated `RelNode` algebra tree, intended as the primary input for a future FormalSQL `SQLAlgebra` emitter.

The current DDL reader only covers simple `CREATE TABLE (...)` declarations. It exists to bootstrap Calcite validation and is not part of the trusted semantics. Logos should treat Calcite output as frontend IR, then generate explicit FormalSQL/Rocq definitions, theorems, and obligations for kernel checking.

## SQLGlot Dialect Adapter

Logos also includes an optional SQLGlot adapter for translating vendor SQL dialects into Calcite-friendly SQL before invoking the Calcite wrapper. This adapter is intended for benchmark and ingestion compatibility; it is not part of the trusted semantics.

The adapter lives in:

```text
frontend/sqlglot-adapter
```

Normalize a SQL file explicitly:

```bash
benchmarks/scripts/sqlglot-normalize \
  --input input.sql \
  --output normalized.sql \
  --report normalized.report.json \
  --read tsql \
  --write postgres \
  --identify
```

Or run the full SQLGlot-to-Calcite pipeline:

```bash
scripts/calcite-ir-sqlglot \
  --schema path/to/schema.sql \
  --sql path/to/query.sql \
  --read tsql \
  --write postgres \
  --normalized-output normalized.sql \
  --report normalized.report.json
```

The adapter currently performs three kinds of work:

- SQLGlot transpilation, for example translating T-SQL-style `SELECT TOP n` into Calcite-accepted `LIMIT n`.
- Identifier quoting via `--identify`, which avoids parser conflicts with aliases such as `year` or `returns`.
- Small Calcite-compatibility patches for TPC-DS date arithmetic, such as `+/- n days` and simple date-column `+/- integer` expressions.

See `frontend/sqlglot-adapter/README.md` for the current patch list. These patches are frontend compatibility rewrites, not trusted proof rules.

The generated report records adapter-side normalizations. Downstream proof generation should preserve that metadata so that Logos can distinguish between full SQL semantics and normalized frontend compatibility.

## Benchmarks

The initial core rewrite benchmark seed lives in:

```text
benchmarks/core
```

It contains selected VeriEQL, R-Bot, and WeTune cases for frontend and equivalence-pipeline development without vendoring the full upstream repositories. See `benchmarks/core/README.md` for source commits, file layout, and size notes.

## SQLCoq Maintenance Status

The upstream SQLCoq repository is not currently maintained as a modern Rocq stack:

- The upstream `sqlformalsemantics` project targets Coq 8.11.2.
- `vendor/FormalSQL` tracks `WindOctober/FormalSQL` on branch `master`, forked from `formaldata/sqlformalsemantics`, with the goal of supporting Rocq 9.2 while preserving the original formal SQL semantics.

Accordingly, Logos currently depends only on FormalSQL's SQL semantics and SQLAlgebra definitions.
