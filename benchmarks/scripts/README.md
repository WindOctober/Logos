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
artifacts plus `stdout.log`, `stderr.log`, `time.txt`, `status.json`,
`usage.json`, and `runner-result.json`;
`runner-summary.json` is atomically refreshed as cases finish.  A timed-out or
nonzero case is recorded and does not stop the remaining cohort.

The default verification mode is `outcome-unconditional`.  The internal proof
budget reserves the last 300 seconds of the selected total case timeout for
counterexample work, cleanup, and final report materialization. The runner's
default 70-minute case timeout covers the complete pipeline. The runner never
creates or resumes agent sessions:
counterexample rounds, proof repair, and `codex exec resume` remain owned by
`logos-solver`.  On timeout or interruption, the runner terminates the whole
case process group; the proof launcher separately removes any Docker container
identified by its `cidfile`.

Both Codex stages use `gpt-5.6-sol` and JSONL output. Each invocation must end
with a structured `turn.completed.usage` record; missing, malformed, or
inconsistent usage fails closed. Resumed proof turns are summed once per
invocation rather than reusing cumulative session counters. `inputTokens`
includes cached input and the runner verifies `totalTokens = inputTokens +
outputTokens`. The API-price equivalent uses the public standard rates current
on 2026-07-22: USD 5/M input, USD 0.50/M cached input, and USD 30/M output,
following <https://developers.openai.com/api/docs/pricing>.

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
  IR_LOG="$(mktemp)"
  cleanup_ir_log() {
    rm -f -- "$IR_LOG"
  }
  trap cleanup_ir_log EXIT

  IR_STATUS=0
  Logos/scripts/export-benchmark-ir \
    --force \
    --continue-on-error 2>"$IR_LOG" || IR_STATUS=$?
  cat "$IR_LOG" >&2

  IR_FAILURE_COUNT="$(grep -c -- "^failed " "$IR_LOG" || true)"
  if test "$IR_STATUS" -eq 0; then
    test "$(grep -Fxc -- "summary: exported=389 failed=0" "$IR_LOG" || true)" -eq 1
    test "$IR_FAILURE_COUNT" -eq 0
    EXPECTED_IR_CASES=389
  else
    test "$IR_STATUS" -eq 1
    test "$(grep -Fxc -- "summary: exported=388 failed=1" "$IR_LOG" || true)" -eq 1
    test "$IR_FAILURE_COUNT" -eq 1
    test "$(grep -Ec -- "^failed wetune-issues/44:" "$IR_LOG" || true)" -eq 1
    EXPECTED_IR_CASES=388
  fi

  for artifact in before.calcite-ir.json after.calcite-ir.json metadata.json; do
    test "$(find Logos/benchmarks/core/.generated/calcite-ir \
      -type f -name "$artifact" | wc -l)" -eq "$EXPECTED_IR_CASES"
  done

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

The QED runner treats JSON serialization and the parser's legacy Racket export
as separate stages. It accepts a JSON artifact after a fresh parse only when it
contains exactly two complete Calcite plans whose reconstructed output type
vectors agree; a later Racket-only failure is retained as a warning. Before any
parser attempt, both the raw and normalized forms must contain exactly one query
statement on each side. A multi-statement side fails closed rather than allowing
the parser to compare a different pair.

When the exact mismatch is QED's name-sorted handling of a relational star, a
star-only retry is admitted only by a three-stage provenance proof. The source
AST must identify the exact root-star span and its direct derived-table outputs
in source `FROM` order; the authoritative Calcite IR must expose the matching
direct `$N` output lineage and ordered types; and the fresh QED JSON must expose
the same direct output-column lineage. Missing or indirect lineage, including a
same-typed reorder, rejects the retry. The resulting rewrite makes the already
attested source output order explicit without changing the constraint profile.

If exact `NOT NULL VARCHAR` DDL instead triggers QED/Calcite's null-charset bug,
the runner may retry a full-row profile that removes only the affected
`NOT NULL` declarations. A projected-schema fallback may remove only attested dead
direct-column outputs; top-level stars and whole-row uses remain complete, and
NATURAL JOIN, JOIN USING, or removal of calls, casts, or arithmetic fails closed.
The opaque-VARCHAR fallback replaces its closed VARCHAR equality fragment with
an injective integer-domain encoding. Plain LIKE is bridged only for attested
direct VARCHAR operands and a backslash-free quoted pattern, through a nullable
uninterpreted `QED_VARCHAR_LIKE` function; ESCAPE, ILIKE, and dynamic patterns
are rejected. This bridge proves only that concrete LIKE is one interpretation
of the generated function. Character-family admission is authorized by the
digest-bound raw source DDL, not by Calcite's lossy schema types, and an exact
base-column-use closure must prove that every retained character use is
VARCHAR; a live source `CHAR` use fails closed.

`sourceConstraintCoverage` is copied from the source profile and remains
immutable while retries select an active coverage profile. Any attempt whose
constraints are conservatively omitted, and every relaxed, projected,
star-expanded, opaque-string, or keyless fallback, is EQ-only: an EQ result over
the enlarged or abstracted domain may transfer to the source pair, but a non-EQ
result becomes UNKNOWN rather than a source counterexample.

The canonical JSON receives name-attested keys. The repair step also restores
the common type of direct NULL branches under UNION/INTERSECT/EXCEPT when QED's
serializer emits a polymorphic `NULL` type; no non-NULL expression is changed.
If the keyed prover process itself fails, a second full-output keyless JSON may
be tried under the same EQ-only rule. Reusing any preexisting variant rebuilds
its attestations and requires exact source-input, variant-input, Calcite IR, and
canonical JSON digests together with the recorded active policy. Every attempt,
selected variant, constraint relaxation, output signature, repair, and digest is
recorded in case metadata or the runner result.

The resource flags are tool-specific in the current local runner. Both tools
use six concurrent cases and a 14,400-second wall-clock timeout. Cosette runs
inside Docker with the requested 4-CPU and 16-GiB per-case limits. QED runs as
a host process: those two Docker limits are not applied to it, so its actual
CPU and peak RSS are recorded per case instead. Do not interpret the root
manifest's `cpuCores`/`memoryGb` fields as enforced QED limits.

The Cosette adapter emits every case for audit. Its metadata reports syntax
compatibility and semantic-profile compatibility separately; those labels do
not pre-filter the runner denominator. Its admitted compatibility lowering is
bound to the current source SQL/schema through generated Calcite IR digests and
records rule-specific side conditions. The adapter validates each current typed
Rex envelope before constructing the checked legacy text-digest view consumed
by the closed Cosette compiler; missing, malformed, or conflicting typed and
legacy fields fail closed, and the rich typed payload remains intact.

IR reserialization is also rejected when Calcite's aggregate result type
disagrees with PostgreSQL (for example, `SUM(INTEGER)` must be `BIGINT`) or when
Calcite has folded a source `CASE`/`NULL` fragment without an exact, closed
source-to-Rex rewrite attestation. In either situation the original SQL stays
visible to Cosette's independent parser and compatibility reporting.

Calcite-embedded SQL must either match the source exactly or pass a closed
source binding: quotes may be removed only from simple ASCII identifiers,
alpha-renames must come from the integrity-bound metadata map and remain
case-fold injective, and only separately attested ASCII case and optional alias
`AS` spelling differences are admitted. The ordered Calcite schema must also
bind completely to the source schema. For the affected TPCDS date predicates,
the `+ N days` replay is allowed only when raw source SQL, SQLSolver-facing SQL,
Calcite export metadata, and both sides' complete occurrence inventories agree;
the complete ordered schema binding, including `CHAR` versus `VARCHAR`, must
also remain exact. Only then is the explicit `INTERVAL 'N' DAY` spelling used.
An older IR that erases a declared character type, a missing IR (currently
`wetune-issues/44`), a stale digest, an unmatched identifier or date occurrence,
or an unsupported/unproved operator or error-sensitive shape remains unchanged
and is reported as a fail-closed residual.

The Cosette runner records `rawSolverResult` as the solver's result for the
emitted Cosette profile. It copies that value to `sourceAuthorizedResult` only
when metadata marks the semantic profile compatible. If omitted constraints,
NULL/Bool3 behavior, finite-width overflow, or richer scalar semantics flag the
profile, its completed raw outcome is retained under
`audit-only-profile-outcome` while `sourceAuthorizedResult` is UNKNOWN; it is
baseline evidence, not a conclusion about the source PostgreSQL pair. Likewise,
QED metadata distinguishes
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
  `feae5c564cc6ae4ba6349af1fd00d8496dc5b5de42b6e02d89789e3e8321fb35`
- `PaperTools/scripts/run-cosette-benchmark`:
  `8381f837adc373c6a839505e43d28e168fae66a88b0171f2d08b5776220afc54`
- `PaperTools/scripts/qed-parser`:
  `8585d29b0f60fdbecedbde63b1883736ad3c034893a3ed55b2197481f87691e5`
- `PaperTools/scripts/qed-prover`:
  `d268b62383d94dcb5527514abc3b98fdc8c6cb25e99fca8c1698511909498308`
