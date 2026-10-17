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
