# Logos

Logos is a proof-producing verifier for SQL query rewrites. It lowers a
PostgreSQL-oriented SQL fragment to FormalSQL, uses LLM agents to search for
proofs or countermodels, and accepts a result only after an isolated Rocq
kernel check.

Logos is a research prototype. Unsupported or insufficiently justified SQL
features fail closed instead of being approximated as equivalent.

## What Logos Provides

- **Unbounded verification.** Equivalence theorems quantify over every finite
  database satisfying the modeled schema constraints.
- **Order-sensitive semantics.** Queries denote all legal ordered results, so
  nested `ORDER BY`, `OFFSET`, `FETCH`/`LIMIT`, ties, rank, and windows remain
  observable.
- **Reusable bag reasoning.** Proven `BagClosed` boundaries allow local use of
  multiplicity-based bag proofs without erasing order globally.
- **Typed PostgreSQL behavior.** The modeled fragment includes SQL NULL,
  three-valued predicates, typed scalar and aggregate operations, selected
  temporal and string behavior, and observable runtime errors.
- **Proof-producing outcomes.** Both equivalence and data-dependent
  non-equivalence require Rocq certificates. An LLM response or one PostgreSQL
  execution is never a verdict.

## How It Works

```text
schema.sql + source.sql + target.sql
                 |
                 v
     SQLGlot normalization (optional)
                 |
                 v
      Calcite relational/Rex IR
       + source provenance data
                 |
                 v
      validated Rust IR and lowering
                 |
                 v
       FormalSQL query expressions
       + schema and proof obligations
                 |
          +------+------+
          |             |
          v             v
   proof search   counterexample search
      (LLM)       (LLM + typed DB export)
          |             |
          +------+------+
                 v
       isolated Rocq kernel check
                 |
                 v
      certified EQ, certified NEQ,
        timeout, or fail-closed error
```

## Requirements

The repository is developed with:

- Rust with Edition 2024 support;
- JDK 17 and Maven for the Calcite frontend;
- Python 3 and SQLGlot for dialect normalization;
- Rocq 9.2, Rocq standard library 9.1, Flocq 4.2.2, and Zarith 1.14.

A complete agent-driven verification run additionally requires:

- PostgreSQL 17 in the configured SQL environment;
- Docker and Linux `bubblewrap` (`bwrap`);
- an authenticated Codex configuration under `CODEX_HOME`;
- the pinned proof-checking image used by the benchmark runner.

Do not point witness materialization at a shared production database. A
rollback cleans up ordinary database changes, but it is not a sandbox for
external functions, triggers, foreign data wrappers, or operating-system side
effects.

## Quick Start

Clone the repository with its FormalSQL submodule:

```bash
git clone --recurse-submodules https://github.com/WindOctober/Logos.git
cd Logos
```

Configure machine-local paths and activate the environment:

```bash
cp .env.example .env
$EDITOR .env
set -a
. ./.env
set +a
```

Build the Rust workspace and run the frontend smoke example:

```bash
cargo build --workspace
make calcite-ir
```

Build FormalSQL and the smallest Logos/Rocq integration check:

```bash
make smoke
```

Materialize one benchmark pair through the repository-owned Logos profile:

```bash
benchmarks/scripts/materialize \
  --tool logos \
  --target nonwetune \
  --benchmark rbot-tpch \
  --case '^query1$'
```

Generate and validate its FormalSQL/Rocq workspace without starting a proof or
counterexample agent:

```bash
benchmarks/scripts/run-logos-transform \
  --case nonwetune-flat__rbot-tpch__query1 \
  --jobs 1
```

For a complete proof/countermodel run, configure `LOGOS_POSTGRES_URL`,
`CODEX_HOME`, `LOGOS_ROCQ_OPAM_SWITCH`, and the proof image, then run:

```bash
benchmarks/scripts/run-logos \
  --case nonwetune-flat__rbot-tpch__query1 \
  --jobs 1 \
  --verification-mode outcome-unconditional
```

The complete environment contract, immutable proof-stack policy, and batch
options are documented in
[`benchmarks/scripts/README.md`](benchmarks/scripts/README.md).

## Verification Modes

`logos-solver check` supports three proof modes:

| Mode | Maturity | Obligation |
| --- | --- | --- |
| `safe-unconditional` | Supported | Both queries always succeed and have the same exact ordered observations. It shares most of the default proof path but imposes a stronger safety obligation. |
| `outcome-unconditional` | Primary/default | Both queries expose the same successful observations and modeled runtime-error categories. This is the main evaluated workflow. |
| `conditional` | Experimental/TBD | Error-preserving equivalence under an audited structured input condition. Condition synthesis, coverage, and proof automation remain incomplete. |

Conditional results are reported separately as `CONDITIONAL-DERIVED` when the
condition follows from the input contract and `CONDITIONAL-EXTERNAL` when it is
an additional satisfiable assumption. The interface is implemented, but the
conditional mode is not yet considered feature-complete or as mature as the
two unconditional modes. Static output-type or modeled
parse-analysis mismatches may terminate before proof search; all
data-dependent `EQ` and `NEQ` results use the Rocq acceptance path.

## Semantic Model

FormalSQL provides one compositional query syntax and one exact relational
semantics over ordered row-list outcomes:

- the public query relation ranges over every legal Boolean evaluation
  schedule;
- `ORDER BY`, slicing, rank, windows, and nested top-k consume exact lists;
- SQL runtime failures are outer `SqlError` outcomes, not SQL NULL values;
- bag semantics is a proved local abstraction, not a competing evaluator;
- schema conformance covers modeled types, NULL constraints, keys, foreign
  keys, checks, and supported unique indexes;
- unsupported types, operators, locale behavior, coercions, and provenance
  shapes are rejected conservatively.

The main FormalSQL modules are:

| Module | Responsibility |
| --- | --- |
| `SqlQuerySyntax.v` | Typed compositional query and scalar syntax |
| `SqlQuerySemantics.v` | Exact ordered-outcome relation |
| `SqlQueryWellFormed.v` | Conservative structural admission rules |
| `SqlBagAbstraction.v` | Possible-bag abstraction and `BagClosed` bridge |
| `SqlQueryFacts.v` | Order, bag-reuse, and semantic soundness facts |
| `SqlQueryContexts.v` | Typed substitution and context congruence |
| `SchemaConstraints.v` | Concrete database integrity contract |

See [`vendor/FormalSQL/README.md`](vendor/FormalSQL/README.md) for the formal
library and [`theories/FormalSQL/catalog/INDEX.md`](theories/FormalSQL/catalog/INDEX.md)
for the Logos proof-facing theorem catalog.

## Project Layout

| Path | Purpose |
| --- | --- |
| `crates/logos-ir` | Structured Calcite IR, provenance, and validation |
| `crates/logos-solver` | Lowering, proof orchestration, reports, and CLI |
| `frontend/calcite-wrapper` | Java/Calcite SQL frontend |
| `frontend/sqlglot-adapter` | Audited dialect normalization |
| `vendor/FormalSQL` | Pinned Rocq semantics submodule |
| `theories/FormalSQL` | Logos-owned reusable proof facts and facade |
| `tests/rocq` | Cross-repository Rocq smoke and regression checks |
| `benchmarks/core` | Versioned benchmark inputs and authority metadata |
| `benchmarks/scripts` | Materialization and reproducible batch runners |

## Build and Test

Useful development targets are:

```bash
# Rust unit and integration tests
cargo test --workspace

# Calcite, Rust importer, SQLGlot, and materializer tests
make frontend-tests

# FormalSQL plus the production Logos theorem closure
make logos-formal-sql-lemmas

# Complete Rocq regression suite
make logos-formal-sql-checks

# Isolated trusted-checker regression
make trusted-rocq-sandbox-test

# Reject theorem catalog/source drift
python3 scripts/generate-formal-sql-catalog.py --check
```

`make logos-formal-sql-lemmas` deliberately excludes examples. The larger
`logos-formal-sql-checks` target compiles Logos-owned regression modules and
the integration smoke test.

## Benchmarks

The checked-in benchmark corpus and its source provenance are described in
[`benchmarks/core/README.md`](benchmarks/core/README.md). Materialize the Logos
profile and run a selected case with:

```bash
benchmarks/scripts/materialize --tool logos --target all --force

benchmarks/scripts/run-logos \
  --case nonwetune-flat__verieql-calcite__calcite-148
```

Use `benchmarks/scripts/run-logos --list` to inspect a cohort without running
it. Do not construct publication campaigns from retained `var/` state; the
versioned authority files under `benchmarks/core/authority/` define campaign
membership and proof gates.

## Citation

```bibtex
@misc{ke2026logos,
  title = {Logos: Certified Order-Sensitive SQL Rewrites with Mechanized
           Semantics and LLM Guidance},
  author = {Jingyu Ke and Jingyang Li and Guoqiang Li},
  year = {2026},
  eprint = {2608.15709},
  archivePrefix = {arXiv},
  primaryClass = {cs.DB},
  url = {https://arxiv.org/abs/2608.15709}
}
```

## License

Logos-authored code is distributed under the [MIT License](LICENSE).
