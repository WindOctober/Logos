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

Logos uses the Rocq-compatible SQLCoq fork in `vendor/FormalSQL`. By default, the Makefile expects a Rocq 9.2 opam switch at `../FormalSQL/.opam-rocq`. Override `OPAM_SWITCH` if your switch lives elsewhere.

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

Or invoke the wrapper directly:

```bash
scripts/calcite-ir \
  --schema frontend/calcite-wrapper/examples/schema.sql \
  --sql frontend/calcite-wrapper/examples/query.sql
```

The command emits JSON with two main views:

- `sqlAst`: Calcite's `SqlNode` syntax tree, useful for inspecting parser output.
- `rel`: Calcite's validated `RelNode` algebra tree, intended as the primary input for a future FormalSQL `SQLAlgebra` emitter.

The current DDL reader only covers simple `CREATE TABLE (...)` declarations. It exists to bootstrap Calcite validation and is not part of the trusted semantics. Logos should treat Calcite output as frontend IR, then generate explicit FormalSQL/Rocq definitions, theorems, and obligations for kernel checking.

## SQLCoq Maintenance Status

The upstream SQLCoq repository is not currently maintained as a modern Rocq stack:

- The upstream `sqlformalsemantics` project targets Coq 8.11.2.
- `vendor/FormalSQL` tracks `WindOctober/FormalSQL` on branch `master`, forked from `formaldata/sqlformalsemantics`, with the goal of supporting Rocq 9.2 while preserving the original formal SQL semantics.

Accordingly, Logos currently depends only on FormalSQL's SQL semantics and SQLAlgebra definitions.
