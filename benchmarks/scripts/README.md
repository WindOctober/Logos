# Benchmark materialization and runs

Run these commands from the `sql-logos-workflow` root after `direnv allow`.

## Run the complete Logos pipeline

`Logos/benchmarks/scripts/run-logos` is the canonical full-pipeline benchmark
runner.  It invokes `logos-solver check` once per case, so every case follows
the normal counterexample, lowering, proof-agent, and trusted Rocq-check path.
With no case selector, it runs all generated cases:

```bash
Logos/benchmarks/scripts/run-logos --jobs 16 --case-timeout 70m
```

Run one case, one source benchmark, or an explicit case batch with:

```bash
Logos/benchmarks/scripts/run-logos \
  --case nonwetune-flat__verieql-calcite__calcite-148

Logos/benchmarks/scripts/run-logos \
  --benchmark verieql-calcite \
  --jobs 8

Logos/benchmarks/scripts/run-logos \
  --case-file selected-cases.txt \
  --jobs 8
```

Use `--list` with the same selectors to inspect a cohort without running it.
`--case` and entries in `--case-file` are exact aliases; `--match` accepts a
regular expression.  Repeated selectors form a batch, and `--limit` truncates
the stable, sorted selection.

The default input is
`Logos/benchmarks/core/.generated/sqlsolver`.  Despite the historical profile
name, this is the current generated SQL case layout consumed by Logos: each
case has `schema.sql`, `sql1.sql`, `sql2.sql`, and authoritative integrity
metadata.  Regenerate it before a clean run with:

```bash
Logos/benchmarks/scripts/materialize --tool sqlsolver --target all --force
```

The runner performs an incremental `cargo build -p logos-solver` unless
`--no-build` is given.  Results go to a fresh timestamped directory under
`Logos/var/logos-solver/benchmark-runs/`.  Each case has its complete solver
artifacts plus `stdout.log`, `stderr.log`, and `runner-result.json`;
`runner-summary.json` is atomically refreshed as cases finish.  A timed-out or
nonzero case is recorded and does not stop the remaining cohort.

The default verification mode is `outcome-unconditional`.  The internal proof
budget is 3600 seconds across all proof repair rounds, while the runner's
default 70-minute case timeout covers the complete pipeline and leaves time to
write the final report.  The runner never creates or resumes agent sessions:
counterexample rounds, proof repair, and `codex exec resume` remain owned by
`logos-solver`.  On timeout or interruption, the runner terminates the whole
case process group; the proof launcher separately removes any Docker container
identified by its `cidfile`.

## Reproduce external baselines

The wrappers use the locally configured QED parser/prover and the pinned
Cosette container. The recipe regenerates the solver-neutral
`Logos/benchmarks/core/.generated/sqlsolver` case layout because Cosette uses
that common `schema.sql`/`sql1.sql`/`sql2.sql` layout as its source. This is
input preprocessing only: the SQLSolver JAR is not executed and no SQLSolver
result is produced.

### Reproduce QED and Cosette in one invocation

```bash
direnv exec . bash -euo pipefail -c '
  Logos/benchmarks/scripts/materialize \
    --tool sqlsolver \
    --target all \
    --force

  Logos/benchmarks/scripts/materialize \
    --tool qed \
    --target all \
    --force \
    --skip-parser

  Logos/benchmarks/scripts/materialize \
    --tool cosette \
    --target all \
    --force

  test "$(find Logos/benchmarks/core/.generated/sqlsolver -name metadata.json -type f | wc -l)" -eq 389
  test "$(find Logos/benchmarks/core/.generated/qed -name metadata.json -type f | wc -l)" -eq 389
  test "$(find Logos/benchmarks/core/.generated/qed -name qed.sql -type f | wc -l)" -eq 389
  jq -e ".discovered == 389 and .emitted == 389 and .failed == 0" \
    Logos/benchmarks/core/.generated/cosette/manifest.json >/dev/null

  RUN_LABEL="${RUN_LABEL:-final-qed-cosette-$(date +%Y%m%d-%H%M%S)}"
  PaperTools/scripts/run-benchmark-tools \
    --tool qed-cosette \
    --qed-parse-missing \
    --run-label "$RUN_LABEL" \
    --jobs 6 \
    --timeout 14400 \
    --memory-gb 16 \
    --cores 4 \
    --cosette-image \
      shumo/cosette-frontend@sha256:184fb5eb5217b8cd2d53f513610747e046d927f8fc31602652c9addf23ffdad9

  test "$(wc -l < "var/tool-runs/$RUN_LABEL/qed/results.jsonl")" -eq 389
  test "$(wc -l < "var/tool-runs/$RUN_LABEL/cosette/results.jsonl")" -eq 389
  jq -e ".cases == 389" "var/tool-runs/$RUN_LABEL/qed/summary.json" >/dev/null
  jq -e ".cases == 389" "var/tool-runs/$RUN_LABEL/cosette/summary.json" >/dev/null
  printf "results: var/tool-runs/%s\n" "$RUN_LABEL"
'
```

QED parsing is deliberately performed by the runner via
`--qed-parse-missing`; this keeps parser failures in the same 389-case result
cohort instead of silently omitting cases without `qed.json`. A nonzero or
unsupported result for an individual case is recorded as experimental output
and does not stop the other tool from running.

The resource flags are tool-specific in the current local runner. Both tools
use six concurrent cases and a 14,400-second wall-clock timeout. Cosette runs
inside Docker with the requested 4-CPU and 16-GiB per-case limits. QED runs as
a host process: those two Docker limits are not applied to it, so its actual
CPU and peak RSS are recorded per case instead. Do not interpret the root
manifest's `cpuCores`/`memoryGb` fields as enforced QED limits.

The Cosette adapter emits every case for audit. Its metadata reports syntax
compatibility and semantic-profile compatibility separately; those labels do
not pre-filter the runner denominator. Likewise, QED metadata distinguishes
constraints applied exactly from constraints conservatively omitted because
the public frontend cannot represent them. QED PRIMARY/UNIQUE keys are withheld
from parser planning to avoid its key-index bug, then injected by attested column
name into the finalized JSON; a key pruned by the parser is reported as a
conservative relaxation.

Raw runner output is written once under
`var/tool-runs/<RUN_LABEL>/{qed,cosette}`. Canonical paper artifacts should be
copied into the single-tool roots under `FinalExperiment/`; do not create
parallel `latest/` or `run/` result aliases. Each canonical tool root has one
`logs/` evidence subtree; it is not a second result cohort.

### Canonical tool revisions

The canonical local run uses QED prover commit
`31f4b6c271440942ecaca1e1111d4beeabf1f14c` and QED parser commit
`684daf23e5c2595726d3411ff3dc04b1c38a4409`. The built prover and parser
artifacts have SHA-256 values
`365111b7f047743fd827c64439a3efca5f0dfe8ce3cb03e8100d06bb5d8403a9`
and `d64b9a22fd1bccb359458f547e70f56b0dafbb00af894627ae5ae205c707ec48`,
respectively. The Cosette image is addressed by digest directly in the command
above.

The parser runs on Temurin JDK `19.0.2+7`. QED's external solvers are cvc5
`1.3.1-dev.12.58cda4cdc` (git `58cda4cdc`, SHA-256
`9404b79e9b599375d0ebe7f0d8df4c13132fc106e939bbc82dc95f7d7867775e`)
and Z3 `4.16.0` (SHA-256
`a06c2a851d58c5f5a7c1e5de188fd0e1b1135e778112aee83ffd1a433685516b`).
On another machine, set `CVC5_BIN` and `Z3_BIN` to those pinned executables.

This one-click command is a workflow-level recipe, not a standalone Logos-only
checkout command. The canonical local runner wrappers have SHA-256 values:

- `PaperTools/scripts/run-benchmark-tools`:
  `dcf52153948a455236cf4085b06358dc23e4536f8df784e4e2de047bd0dc3a6f`
- `PaperTools/scripts/run-qed-benchmark`:
  `3acce45e90ae288a13c12baed615f4928738e34826a17b565974b2d70c6a183a`
- `PaperTools/scripts/run-cosette-benchmark`:
  `fb99b14235b0b2af7555490888c7deadef0174af793adae4b7ee3cf6bee9b4e5`
- `PaperTools/scripts/qed-parser`:
  `8585d29b0f60fdbecedbde63b1883736ad3c034893a3ed55b2197481f87691e5`
- `PaperTools/scripts/qed-prover`:
  `d268b62383d94dcb5527514abc3b98fdc8c6cb25e99fca8c1698511909498308`
