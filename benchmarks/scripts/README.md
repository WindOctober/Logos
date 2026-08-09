# Benchmark materialization and runs

Run these commands from the `Logos` repository root after copying
`.env.example` to `.env` and running `direnv allow`. For non-interactive or
detached runs, invoke the runner as `direnv exec . benchmarks/scripts/run-logos
...`; the Python runner does not parse `.env` itself. Complete the environment
preflight in the root README before starting a multi-hour batch.

## Run the complete Logos pipeline

`Logos/benchmarks/scripts/run-logos` is the canonical full-pipeline benchmark
runner.  It invokes `logos-solver check` once per case, so every case follows
the normal counterexample, lowering, proof-agent, and trusted Rocq-check path.
The frozen 389-case launch is accepted only after an exact 16-case gate made by
the same framework, executable, trusted stack, model, resource
policy, SQL environment, and immutable Docker image:

```bash
Logos/benchmarks/scripts/run-logos \
  --input-root Logos/benchmarks/core/.generated/logos \
  --jobs 32 \
  --case-timeout 4h \
  --verification-mode outcome-unconditional \
  --proof-agent-memory-limit-mib 6144 \
  --proof-agent-storage-limit-mib 2048 \
  --statement-timeout-seconds 600 \
  --max-counterexample-rounds 3 \
  --proof-check-timeout-seconds 420 \
  --proof-docker-image sha256:bba804128f28ee6948ed601afac7bd158bab3617d784e2479ef588d03a97459b \
  --proof-rocq-opam-switch Logos/.opam-rocq \
  --postgres-url postgresql://logos@127.0.0.1:55490/postgres \
  --sql-time-zone UTC \
  --sql-default-collation C \
  --sql-character-classification C \
  --sql-locale-provider libc \
  --sql-server-encoding UTF8 \
  --cohort16-gate-summary Logos/var/logos-solver/<gate-run>/runner-summary.json
```

The runner rejects a frozen full launch with any different concurrency,
timeout, verification mode, missing gate, or pipeline-short-circuiting solver
argument. Selectors may still be used for controlled cohorts and local diagnostics.

Run one case, one source benchmark, or an explicit case batch with:

Every actual execution, including a selected subset, requires either
`--postgres-url` or `LOGOS_POSTGRES_URL`. `--list` only inspects inputs and does
not require PostgreSQL or Codex configuration.

```bash
export LOGOS_POSTGRES_URL=postgresql://logos@127.0.0.1:55490/postgres

Logos/benchmarks/scripts/run-logos \
  --case nonwetune-flat__verieql-calcite__calcite-148

Logos/benchmarks/scripts/run-logos \
  --benchmark verieql-calcite

Logos/benchmarks/scripts/run-logos \
  --case-file selected-cases.txt
```

Use `--list` with the same selectors to inspect a cohort without running it.
`--case` and entries in `--case-file` are exact aliases; `--match` accepts a
regular expression.  Repeated selectors form a batch, and `--limit` truncates
the stable, sorted selection.

Long partial campaigns may opt out of failing solely because the aggregate
framework worktree digest changes after launch with
`--allow-framework-source-drift`. This is an explicitly recorded
`record-only` policy: the starting source manifest remains immutable and the
terminal summary reports the observed digest and whether drift occurred. It
does not relax input, solver-binary, trusted Rocq stack, SQL frontend, Docker
image, provider, or PostgreSQL checks, and it is rejected for the exact frozen
389-case campaign. In particular, it never changes the Rocq code seen by a
worker: every run uses the immutable authority snapshot described below. The
default remains strict source-digest equality.

The Logos-facing generated input is
`Logos/benchmarks/core/.generated/logos`. Each case has `schema.sql`,
`sql1.sql`, `sql2.sql`, and authoritative integrity metadata. Regenerate it
independently of the external-tool profiles with:

```bash
Logos/benchmarks/scripts/materialize --tool logos --target all --force
```

The legacy `.generated/sqlsolver` root remains the immutable input of the older
frozen 389-case campaign. It is not the source of the Logos profile and must not
be overwritten while checking the current campaign baseline. For R-Bot, the
Logos profile binds the frozen manifest and preserves the schema and both query
files byte-for-byte, including quoted identifiers. Both workload schemas and
all 59 manifest rows are digest-pinned before materialization. Filtered R-Bot
materialization is allowed only after the complete configured exporter has
matched that frozen superset. The full runner independently checks every native
metadata/input/Calcite-authority binding; selecting both R-Bot benchmarks must
produce exactly 59 cases. For non-R-Bot cases, a
source-derived frozen renderer reproduces the campaign-start bytes. Verify all
1,320 non-R-Bot files in a fresh scratch root with:

```bash
Logos/benchmarks/scripts/materialize \
  --tool logos \
  --target all \
  --output-root <fresh-scratch-root> \
  --force \
  --verify-non-rbot-baseline
```

The frozen Calcite-derived `VARCHAR`-to-`INTEGER` compatibility cast is admitted
only from exact metadata, embedded-query, source-span, and source-text evidence;
missing or stale authority is rejected.

## Generate trusted proof workspaces without agents

`run-logos-transform` runs the same Calcite-to-IR and solver-lowering boundary
without counterexample search or a proof agent. It defaults to the independent
`.generated/logos` input and accepts the same case, case-file, benchmark, match,
limit, and list selectors as the full runner. For the complete R-Bot cohort:

```bash
Logos/benchmarks/scripts/run-logos-transform \
  --benchmark rbot-dsb \
  --benchmark rbot-tpch \
  --jobs 32 \
  --case-timeout 20m
```

Each selected case receives an atomically written `status.json` and
`runner-result.json`. The result binds exact `schema.sql`, `sql1.sql`,
`sql2.sql`, and `metadata.json` digests, the solver report, and the generated
FormalSQL/Rocq workspace files. `runner-summary.json` becomes `complete` only
after every selected case has a terminal record and an end-of-run integrity
check rehashes the inputs, frontend, source tree, solver, runner, reports, and
workspace evidence. A complete summary may still contain explicit failed or
timed-out cases; a successful all-case lowering therefore additionally requires
`counts.completed == counts.selected`.

The runner performs an incremental `cargo build -p logos-solver` unless
`--no-build` is given. Before scheduling any case it resolves an immutable,
content-addressed Rocq runtime and FormalSQL/Logos authority closure. A cache
miss forces a fresh source build; a hit verifies and reuses the same read-only
bytes. `--no-rocq-build` is retained only for CLI compatibility and cannot
bypass this resolution. After the one-time Rust
build, the runner atomically copies `logos-solver` to the run-private,
read-only `runtime/logos-solver` path. Every queued worker and every resume uses
that exact snapshot; a later external `cargo build` cannot change the binary
used by the campaign, while mutation of the snapshot itself still fails
integrity verification. The runner likewise captures every admitted
FormalSQL/Logos `.v` source and its matching `.vo` object into one shared,
content-addressed authority bundle before it starts any worker.
Files are mode `0444`, directories are mode `0555`, hardlinks and symlinks are
rejected, and a canonical manifest binds the exact path set, byte counts, and
SHA-256 digests. Proof-agent staging, diagnostic compilation, and the final
trusted checker all receive this directory as `--logos-repo-root`; per-run
references bind its key and manifest digest, and a concurrent
build in the working tree therefore cannot mix Rocq generations within a run.
The checker also caches its minimal ELF closure by the exact `rocq`, `bwrap`,
worker, native-helper, and OCaml-stub contents. The first diagnostic records
the `ldd`/`readelf` result as an immutable digest-checked bundle; later cases
mount that same bundle instead of repeating dependency discovery and copying
system libraries. Generated `Schema.v`/`Queries.v`/`Witness.v` objects are
cached separately by authority and source digests, and a successful problem
diagnostic retains a prefix-bound `Problem.vo` for final certification. Every
reuse path still performs its independent source/object and kernel checks.
Capture performs a second live-closure scan and aborts if a build races the
copy. Results go to a fresh
timestamped directory under `Logos/var/logos-solver/benchmark-runs/`. Each case has its complete solver
artifacts plus `stdout.log`, `stderr.log`, `time.txt`, `status.json`,
`usage.json`, and `runner-result.json`;
`runner-summary.json` is atomically refreshed as cases finish.  A timed-out or
nonzero case is recorded and does not stop the remaining cohort.

The runner always passes `--force-llm-assessment`, so every newly scheduled
case receives a fresh counterexample assessment even when a debug solver would
otherwise reuse its assessment cache. The summary records the model, caller
`solverArgs`, effective solver arguments, PostgreSQL URL fingerprint, complete
SQL environment, and exact solver/provider launch policies in its
`configuration` object. `--max-counterexample-rounds` is an explicit recorded
pipeline parameter rather than an implicit solver default. The solver process starts from an empty environment
with a manifest-bound Codex/Node PATH, fixed locale/home/temp values, and only
the isolated Codex and frontend contract variables. The counterexample command
then clears its environment again. Ambient provider URLs, credentials, proxy
variables, shell startup state, exported functions, and loader/language paths
therefore cannot silently change the pinned treatment; runner-owned solver
options cannot be passed again through `--solver-arg`.

Every run also freezes canonical full and selected input manifests containing
the exact `schema.sql`, `sql1.sql`, and `sql2.sql` digests; the dirty source-tree
manifest; the solver executable digest; the configured Rocq and bubblewrap
executables; FormalSQL source/object pairs; Rocq standard-library objects and
runtime plugins; proof/checker scripts; and the resolved proof-agent image ID.
The SQL-to-IR frontend is runner-owned as well: the runner compiles Calcite
once, constructs a runtime-only classpath, and invokes the bound Java classes
directly on the exact PostgreSQL input bytes for each query. This avoids an
unnecessary same-dialect serializer changing source token structure before the
typed frontend binds source spans. Its manifest covers the exact absolute Bash
invocation and clear-then-fixed environment, wrapper and Maven scripts, their
fixed shell/tools and ELF closures, the JDK, compiled classes, and every
runtime jar. Each per-query frontend child independently clears inherited
state before restoring only the frozen JDK/Maven/classpath contract. Ambient
frontend commands, shell startup/functions, Java/Maven/Python overrides,
loader paths, and classpaths cannot enter semantic lowering.

The LLM treatment uses a runner-generated minimal Codex configuration containing
only the pinned model, medium effort, selected provider, nonsecret endpoint, and
wire settings. A temporary mode-0700 Codex home supplies that same immutable
configuration and copied credentials to both counterexample and proof stages;
plugins, remote plugins, hooks, skill dependency installation, ambient provider
URLs, and the user's session/history tree are excluded. The manifest binds the
sanitized configuration, endpoint identity, lexical Codex wrapper,
`/usr/bin/env` and Node interpreter/runtime closure, package closure, fixed
solver PATH, counterexample child policy, and all three exact Codex commands.
Credential bytes and their hashes are never written to run or publication
artifacts.

When PostgreSQL is configured, the runner also records and rechecks its actual
server profile. Frozen runs require PostgreSQL 17.4, UTC, C collation and
character classification, the libc provider, UTF8, and 96 maximum connections;
the connection URL itself is represented only by a digest.
Each result repeats its effective configuration and input bindings and records
host diagnostic counts/times, proof rounds, context sizes, proof bytes, and
report digests. The runner rehashes all of these authorities before it may
write a complete summary.

An interrupted run can be continued in its original directory with `--resume`.
The caller must supply the same input selection and exact configuration; a
complete run, missing summary, changed case ID, jobs/timeout/mode/path/model,
SQL environment, PostgreSQL URL, or solver argument is rejected. Resume loads
the preserved run-private solver and validates and reuses the content-addressed Rocq
authority snapshot without reading or rebuilding current FormalSQL sources;
missing files, extra files, byte/permission/link drift, or a changed snapshot
manifest fail before any worker starts. It also requires the same runner
script digest even under the source-drift record-only policy. Terminal
`runner-result.json` files are loaded without invoking the solver again. A case
directory without a terminal result was already started, so it is preserved
and finalized as an explicit interrupted `failed` result; authoritative usage
is recovered only from structured provider records. Only a case with no case
directory is scheduled. The original `startedAt`, cumulative elapsed time,
per-invocation provenance, and continuation counts are retained while each
summary update is atomically merged.

Nonzero solver exits without `report.json` retain a bounded UTF-8 stderr tail
in `runnerError`/`reason`, including PostgreSQL SQLSTATE diagnostics.

The default verification mode is `outcome-unconditional`.  The internal proof
budget reserves the last 300 seconds of the selected total case timeout for
counterexample work, cleanup, and final report materialization. The runner's
default 70-minute case timeout covers the complete pipeline. The runner's
in-place benchmark continuation never creates or resumes Codex agent sessions:
counterexample rounds, proof repair, and `codex exec resume` remain owned by
`logos-solver`.  On timeout or interruption, the runner terminates the whole
case process group; the proof launcher separately removes any Docker container
identified by its `cidfile`.

Both Codex stages use `gpt-5.6-sol` at medium reasoning effort and JSONL output.
The first proof invocation receives the complete remaining proof-search budget
after reserving the configured final-check timeout and bounded process-kill
cleanup; there is no 1,800-second soft split. Diagnostics are sequential and
share the same invocation deadline. A request may choose any positive timeout,
which the host clips only to the remaining invocation time; there is no
completed-check or broker-request quota. The host alone
checks the post-container snapshot and records diagnostic telemetry. The same
Codex session is resumed after an explicit handoff, process failure, or failed
host checkpoint/final check, for at most 16 unsuccessful invocations. The next
invocation then starts one fresh bounded session from
the audited `Problem.v` plus the latest host feedback, preventing an unbounded
repair transcript while preserving proof state. Every generation and restart
is recorded and session IDs may not be reused. The host also mounts a distinct
private `CODEX_HOME` for every generation; earlier session/history trees remain
outside the later generation's container. Each invocation must end
with a structured `turn.completed.usage` record; missing, malformed, or
inconsistent usage fails closed. Resumed proof turns are summed once per
bounded session by retaining its latest componentwise-monotonic cumulative
snapshot; independent counterexample invocations are each added once. `inputTokens`
includes cached input and the runner verifies `totalTokens = inputTokens +
outputTokens`. The API-price equivalent uses the public standard rates current
on 2026-07-22: USD 5/M input, USD 0.50/M cached input, and USD 30/M output,
following <https://developers.openai.com/api/docs/pricing>.

## Run the fixed 16-case Logos regression cohort

Use the stable core cohort for proof-framework changes before scheduling all
389 cases:

```bash
Logos/benchmarks/scripts/run-logos-regression
```

The wrapper selects `logos-regression-core.txt`, runs 16 cases concurrently,
uses `OUTCOME-UNCONDITIONAL`, and gives each complete counterexample-to-proof
pipeline one hour. Normal `run-logos` options override these defaults because
they are appended after the wrapper defaults, for example:

```bash
Logos/benchmarks/scripts/run-logos-regression \
  --jobs 4 \
  --run-dir Logos/var/logos-solver/my-regression

Logos/benchmarks/scripts/run-logos-regression --list
```

The cohort deliberately spans small, medium, and large queries. It covers
schema/NOT NULL reasoning, output-signature rejection, SQL three-valued logic,
CASE/IN, ORDER BY/FETCH, empty and UNION ALL bags, EXISTS and correlated
subqueries, DISTINCT aggregates, outer joins, character typmods, WeTune
PK/FK/UNIQUE sidecars, and large DSB/TPC-H/TPC-DS plans. Both proof and validated
counterexample paths are represented; the cohort is a regression workload, not
a collection selected only because every case is currently easy to certify.

## Reproduce external baselines

The wrappers use the locally configured QED parser/prover and the pinned
Cosette container. The recipe regenerates the solver-neutral
`Logos/benchmarks/core/.generated/sqlsolver` case layout because Cosette uses
that common `schema.sql`/`sql1.sql`/`sql2.sql` layout as its source. This is
input preprocessing only: the SQLSolver JAR is not executed and no SQLSolver
result is produced.

SQLSolver materialization has its own target policy, independent of the Calcite
ingestion adapter. For enabled corpora it records guarded identifier lowering and
runs the actual SQLSolver preprocess/parser/validator/planner before writing
`solverFrontendStatus`. `ready` means both SQL sides planned and every
materialization preservation obligation closed; `Unsupport` is a frontend result,
not prover `UNKNOWN`, while a bounded preflight resource failure remains
`Timeout`. The parser/planner-only probe is also available directly:

```bash
Logos/benchmarks/scripts/sqlsolver-preflight \
  --schema <case>/schema.sql \
  --sql1 <case>/sql1.sql \
  --sql2 <case>/sql2.sql
```

Cosette has a matching proof-free target check. It runs the pinned image's two
actual DSL parser/translators, records exact input digests and stage outcomes,
and never calls `solver.solve`. It mirrors and explicitly reports Cosette's own
whole-input lowercasing, which is a target limitation rather than an attested
source-semantic rewrite:

```bash
Logos/benchmarks/scripts/cosette-preflight \
  --input-root <generated-cosette-root> \
  --report <new-var-run>/report.json
```

Filtered repair work should materialize into a new `var/` output root. Do not use
`--force` with a filtered benchmark against the canonical generated root: the
materializers own broader output directories and may remove unrelated cases or
rewrite shared manifests.

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
  elif test "$IR_FAILURE_COUNT" -eq 1; then
    test "$IR_STATUS" -eq 1
    test "$(grep -Fxc -- "summary: exported=388 failed=1" "$IR_LOG" || true)" -eq 1
    test "$(grep -Ec -- "^failed wetune-issues/44:" "$IR_LOG" || true)" -eq 1
    EXPECTED_IR_CASES=388
  else
    test "$IR_STATUS" -eq 1
    test "$(grep -Fxc -- "summary: exported=350 failed=39" "$IR_LOG" || true)" -eq 1
    test "$IR_FAILURE_COUNT" -eq 39
    test "$(grep -Ec -- "^failed wetune-issues/44:" "$IR_LOG" || true)" -eq 1
    test "$(grep -Ec -- "^failed rbot-(tpch|dsb)/" "$IR_LOG" || true)" -eq 38
    EXPECTED_IR_CASES=350
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

The deterministic R-Bot targets are required to round-trip through R-Bot's
pinned Calcite parser/serializer, but 38 of them do not satisfy Logos's newer,
stricter source-AST-to-relational-node provenance reconstruction. Their missing
Logos Calcite IR is recorded as a compatibility limitation: the common SQL,
QED, and Cosette materializers still emit all 59 R-Bot pairs, and the baseline
runners record parser or profile failures instead of dropping those cases.

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
copied into the destination configured by `LOGOS_FINAL_EXPERIMENT_DIR`; do not create
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
