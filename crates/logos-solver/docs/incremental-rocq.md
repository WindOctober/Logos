# Incremental Rocq diagnostics

Session retention is **disabled by default**. Explicit prefix probes still use
transient sandboxed `rocq repl -emacs` sessions; full checks go directly to the
ordinary compiler, including retries after a rejection.

When retention is explicitly enabled, the host diagnostic broker lazily retains
a bounded pool of sessions per agent round. A full check without an existing session goes directly
to the compiler; an ordinary compiler rejection (exit code 1) enables automatic
REPL startup on subsequent revisions. Explicit probes can also start a session.
Environment failures and timeouts do not warm one. Cold first-try full-check
successes therefore do not pay for a second check.

The session retains the successfully executed sentence prefix. A changed suffix
uses `BackTo` to restore the exact common-prefix state, then runs only the new
sentences. Failures include current goals when available. Full checks with an apparent REPL success
go through ordinary compilation before they can publish a `.vo` or
advance a checkpoint. Final independent kernel checking is unchanged.

Rewinding across a proof-closing command rebuilds the REPL and replays the
requested prefix: Rocq may acknowledge `BackTo` with an old prompt without
reopening a proof after `Qed.`. Rewinds within an open proof retain prefix reuse.

## Explicit prefix probes versus full checks

The same `run-rocq-check.sh` interface accepts `--operation check` (default) or
`--operation probe --stop-after N`, for each of problem/module/scratch modes.
`N` counts complete sentences from the start, including imports, declarations,
`Proof.`, tactics, `Qed.`, standalone bullets and focus braces; it is not a line
number. For example, `Lemma p : True. Proof. exact I. Qed.` at N=2 returns the
open goal, at N=3 stops before Qed, and at N=4 still does not publish anything.

A probe starts a REPL even when cold, reuses/rewinds its validated prefix when retention is enabled, and
returns `Show.` goals (including hypotheses) when a proof is open. Framing stops
at the selected complete sentence, so an incomplete or unsupported suffix cannot
block it. Only that prefix is source-audited; all token/import restrictions
remain, but an open module/scratch proof need not already contain `Qed.`.
Unsupported framing, protocol errors, or a missing environment produce a probe
error, **never full-compiler fallback**. Timeouts discard the session as usual.

Probe success grants no compile authority: no module source installation or
publication, no successful-scratch retention, no checkpoint advancement, and no
final certification. A later explicit full check audits and compiles the complete
candidate, including the previously unselected suffix. Existing checks retain
their original behavior; the agent chooses when it wants only local feedback.

Wire schema v2 adds an optional `probe: {stopAfter: N}` to the existing request;
absence means full check. The whole uploaded candidate remains digest-bound in
the diagnostic snapshot. Accepted probe invocations/responses carry
`probe: {stopAfter, prefixBytes, passed}` identifying the exact audited/executed
prefix. `compilePassed`, `problemCompilePassed`, and `compileCheckpointAdvanced`
are always false for probes, including exit code 0. Broker evidence validation
reconstructs the prefix, and benchmark validation distinguishes advisory success
from compile/publication success. Probe calls still count as diagnostic requests
and share the round's time budget.

The request/checkpoint boundary is implemented in
[`proof_stage/diagnostics.rs`](../src/engine/proof_stage/diagnostics.rs), compiler
fallback in [`proof_stage/checker.rs`](../src/engine/proof_stage/checker.rs), and
the retained sentence state in [`rocq_session.rs`](../src/engine/rocq_session.rs).
An LLM session restart, a proof-agent invocation/round, and a fixed-witness
workspace generation are distinct lifetimes: the Rocq session lasts only for
one broker/round, even if the same LLM session is resumed next round.

## Bounded session retention

The default is **zero retained sessions (disabled)**. The process-tree RSS budget
defaults to **1024 MiB per broker** and applies when retention is enabled, with
least-recently-used eviction. Configure the solver with
`--rocq-session-pool-size N` (0 disables retention, maximum 16) and
`--rocq-session-pool-rss-mib M`. The corresponding solver environment variables
are `LOGOS_ROCQ_SESSION_POOL_SIZE` and `LOGOS_ROCQ_SESSION_POOL_RSS_MIB`.
For example, `--rocq-session-pool-size 2` enables a two-session pool.
The effective values are recorded in `proofAgentConfiguration`. Neither option
depends on the benchmark worker count. These limits do not make requests parallel:
one broker still executes one diagnostic at a time.

Identity includes the candidate path, logical module and full dependency manifest.
Thus two scratch files (both compiled as `LogosGenerated.Problem`) no longer evict
each other's prefixes merely because they share a logical compilation name.
Cold-start eligibility still follows only the most recent ordinary compiler
failure; old failure hints are not pooled. Pooling those hints caused redundant
REPL-plus-compiler work for later successes in historical replay.
A timeout/protocol failure discards that candidate's session, not unrelated sessions.
Unknown/dead process state is discarded, not reused.

The RSS budget counts descendants (launcher, bubblewrap and Rocq), using `/proc`
without spawning metadata tools. It is enforced at request boundaries, including
after a tactic changes the process size. It is a **retention budget**, not a hard
memory limit during an active tactic; active compiler and agent limits are separate.
Before ordinary compilation, the matching REPL is released and an additional
LRU slot is freed if necessary, avoiding N idle REPLs plus an extra compiler.
With retention disabled, explicit probes still work in a transient session.

Any dependency-manifest change still invalidates all prior snapshot sessions;
no approximate import analysis is used. Sessions also remain round-scoped:
the broker thread owns their parent-death handling and isolated temporary files.
They are reaped before that thread exits. Cross-round reuse would require a
generation-owned long-lived service, not moving child handles to a new thread.

## Isolation and invalidation

- The existing empty-root bubblewrap sandbox holds an isolated dependency snapshot.
  Agent-controlled code never executes in an unsandboxed REPL.
- The process-local session key compares the exact trusted dependency manifest
  bytes, logical module name and candidate path, without rehashing the manifest. The manifest is
  reread on each request; a changed manifest cannot reuse the old session.
  The enclosing broker binds the authority, runtime and workspace generation.
  Module publication or a new generation/round cannot reuse old state. A different
  candidate selects its own LRU entry if its dependency manifest is unchanged.
- Every request shares one deadline across REPL execution and any compiler fallback.
  Timeout destroys the session. Protocol errors, unsupported lexical framing and
  response-size limits fall back to compilation for full checks; explicit probes
  return an error without compiling the suffix.
- The host tokenizer is deliberately conservative (for example, selector/term
  braces inside a sentence use the compiler). It is not a replacement Rocq parser.
- Session process groups are terminated and reaped on drop. Parent-death signaling
  plus bubblewrap's `--die-with-parent` prevents a killed solver from leaving a
  running interactive proof behind.
- Scratch compilation has a separate checker mode and cannot replace the main
  `Problem.v` compiled-object cache.

The upload, source audit and evidence snapshot are still performed per request.
Automatic REPL use targets repeated **failing** revisions; explicit probes also
avoid full compilation for successful local experiments. Neither eliminates
successful publication compilation or promise a whole-benchmark speedup.

## Shared diagnostic inputs

`Schema.v`, `Queries.v`, `WitnessData.v`, `Witness.v`, `Goal.v`, and the
`WitnessModules` sources/order are copied once per workspace generation into
`proof-stage/proof-agent/diagnostic-inputs/<generation>/`. The host creates this
private snapshot before launching the agent, marks its files read-only, and
atomically publishes it with a digest-bound `manifest.json`. Reopening a broker
in the same generation compares the snapshot against the trusted workspace;
drift fails closed rather than rewriting earlier evidence. A witness-generation
change gets a separate snapshot.

Each diagnostic's `checked-workspace` retains the existing regular-file layout
using hard links **only to that host-owned snapshot**, never to the live workspace.
`shared-inputs.json` binds the shared manifest by case-relative path, size and
SHA-256. Candidate uploads remain independent files. Module diagnostics also
retain a separate copy of the current mutable `Problem.v`; it is not shared.
An incomplete diagnostic workspace is discarded before it can become evidence.

Neither the agent nor the Rocq sandbox can write these shared inodes: they are
outside the agent's writable mounts, and the checker mounts source inputs
read-only while using separate writable compiler outputs. Deleting one diagnostic
does not remove the shared contents or affect other diagnostics. The layout uses
same-filesystem hard links under the case artifact root; failure to create a link
is an error, not a fallback to a live-workspace link. This changes source storage,
not the REPL success boundary, compiled-object cache, or final kernel checking.

## Evidence and tests

### Broker-scoped environment validation

The host creates a fresh, private `DiagnosticEnvironment` for each broker and
passes its temporary receipt directory explicitly as
`LOGOS_ROCQ_VALIDATION_SESSION`. It is not inherited from ambient environment,
mounted into the agent, or reused on a later broker/process startup. Normal
shutdown removes it; a stale directory after a crash is never selected again.

Within this serialized lifetime, the first checker validates the authority,
runtime bundle and generated/module prefix. Later checks reuse:

- the authority closure validation, without scanning every source/object pair;
- the shared runtime's host-generated launch bindings, without repeating driver
  comparisons, ELF hashing, file scans or the shared runtime lock;
- the prefix validation while its exact manifest bytes match the receipt.

Runtime bindings are retained only when a persistent shared runtime cache is
configured. Without it, invocation-private runtime staging still runs normally;
no receipt can point into a previously deleted checker scratch directory.

Successful module publication carries forward existing validated digests and
hashes only the new `.v`, `.vo`, and `ProofModules/ORDER`, preserving the full
manifest format. It refreshes the prefix receipt only after atomic publication.
An unknown manifest transition or an interrupted publication without a matching
receipt takes the full validation path. A new broker or witness generation starts
without receipts. Standalone checks default to full validation; preflight and final
certification ignore receipts even if the variable is supplied explicitly.

This is an experiment-runtime ownership contract, not protection against arbitrary
external modification of host files: the host exclusively manages these inputs
and serialized publications during the broker lifetime. Shared source snapshots
fix the workspace generation. Candidate source audits, isolated compilation,
module immutability, crash recovery and final independent kernel checks remain
unchanged. `LOGOS_ROCQ_ENVIRONMENT_REUSE component=authority|runtime|prefix`
records actual reuse in checker stderr (REPL startup output remains internal to
the session transport).

### Running checks

Diagnostic stderr records `LOGOS_ROCQ_INCREMENTAL` with `cold`, `fallback`,
`reused_sentences`, `executed_sentences`, `compiler_required`, or `timed_out` fields
as applicable. Existing per-invocation elapsed time includes the incremental path
and any ordinary compilation. These messages are retained in digest-bound evidence.

Run from the Logos repository root:

```bash
RUST_MIN_STACK=67108864 cargo test -p logos-solver --bin logos-solver rocq_session -- --include-ignored
RUST_MIN_STACK=67108864 cargo test -p logos-solver --bin logos-solver engine::proof_stage:: -- --include-ignored --skip real_incremental_sandbox_diagnostics
bash crates/logos-solver/tests/test-trusted-rocq-check-sandbox.sh
```

The Rust session/broker tests use local Unix sockets and process groups. The
shell regression additionally requires Rocq 9.2, compiled dependencies, and
bubblewrap user namespaces. These tests do not call a model or use the network.

For the end-to-end broker and timing test, build the Rust test executable with
`cargo test -p logos-solver --bin logos-solver --no-run`, then set
`LOGOS_ROCQ_BROKER_TEST_BIN` to the printed `target/debug/deps/logos_solver-...`
executable when running the shell sandbox test. The shell supplies an immutable
authority and checked generated-prefix fixture. It compares five failing revisions
against ordinary compilation (including cold startup), then checks repair,
publication, final kernel acceptance, dependency invalidation, unfinished proofs,
timeouts, process cleanup, and real broker requests. Timings are informational;
there is no machine-dependent speed threshold in the regression test.

Local measurement on 2026-10-16 with Rocq 9.2: five failing revisions importing
`ProofAgentFacade` took 6,377 ms with separate compiler invocations versus 2,502 ms
with lazy incremental diagnostics (about 61% less time). This includes the first
ordinary failure and the cold REPL startup, and measures the host checker path,
not model calls or the upload/audit path. The test also separately exercises actual
broker uploads. This small fixture is not a benchmark-wide speedup estimate.
