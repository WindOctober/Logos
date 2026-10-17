# Incremental Rocq diagnostics

The host diagnostic broker lazily retains one sandboxed `rocq repl -emacs`
session per agent round. A cold candidate goes directly to the existing compiler;
only an ordinary compiler rejection (exit code 1) enables incremental checking
on subsequent revisions. Environment failures and timeouts do not warm a session.
First-try successes therefore do not pay for a second check.

The session retains the successfully executed sentence prefix. A changed suffix
uses `BackTo` to restore the exact common-prefix state, then runs only the new
sentences. Failures include current goals when available. An apparent REPL success
**always** goes through ordinary compilation before it can publish a `.vo` or
advance a checkpoint. Final independent kernel checking is unchanged.

The request/checkpoint boundary is implemented in
[`proof_stage/diagnostics.rs`](../src/engine/proof_stage/diagnostics.rs), compiler
fallback in [`proof_stage/checker.rs`](../src/engine/proof_stage/checker.rs), and
the retained sentence state in [`rocq_session.rs`](../src/engine/rocq_session.rs).
An LLM session restart, a proof-agent invocation/round, and a fixed-witness
workspace generation are distinct lifetimes: the Rocq session lasts only for
one broker/round, even if the same LLM session is resumed next round.

## Isolation and invalidation

- The existing empty-root bubblewrap sandbox holds an isolated dependency snapshot.
  Agent-controlled code never executes in an unsandboxed REPL.
- The process-local session key compares the exact trusted dependency manifest
  bytes and logical module name, without rehashing the manifest. The manifest is
  reread on each request; a changed manifest cannot reuse the old session.
  The enclosing broker binds the authority, runtime and workspace generation.
  Module publication, a new generation/round, or a different logical module cannot
  reuse old state. At most one session is retained per broker.
- Every request shares one deadline across REPL execution and any compiler fallback.
  Timeout destroys the session. Protocol errors, unsupported lexical framing and
  response-size limits fall back to compilation, not a successful check.
- The host tokenizer is deliberately conservative (for example, selector/term
  braces inside a sentence use the compiler). It is not a replacement Rocq parser.
- Session process groups are terminated and reaped on drop. Parent-death signaling
  plus bubblewrap's `--die-with-parent` prevents a killed solver from leaving a
  running interactive proof behind.
- Scratch compilation has a separate checker mode and cannot replace the main
  `Problem.v` compiled-object cache.

The upload, source audit and evidence snapshot are still performed per request.
The optimization targets repeated **failing** revisions; it does not eliminate
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
