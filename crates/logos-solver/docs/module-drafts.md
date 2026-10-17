# Develop helpers under their final module name

Reusable helpers no longer need a successful scratch check followed by a
second module check. Pick their final name at the start, write the draft at
`scratch/ProofModules/CoreBridge.v`, and submit:

```bash
# Inside the generated agent workspace, where the wrapper is materialized:
bash run-rocq-check.sh \
  --mode module \
  --candidate scratch/ProofModules/CoreBridge.v \
  --purpose semantic-equivalence \
  --timeout-seconds 60
```

The client uploads the draft's exact bytes with the existing v2 broker identity
`mode=module, candidatePath=ProofModules/CoreBridge.v`. The host applies its
normal strict module audit, checks under
`LogosGenerated.ProofModules.CoreBridge`, and atomically publishes the exact
source/object pair in its ordered, manifest-bound cache on success. The client
does not copy a source into the trusted workspace, manufacture objects, or
publish a directory through the container handoff.

After success, import immediately:

```coq
From LogosGenerated.ProofModules Require Import CoreBridge.
```

There is no second promotion command and no `.vo` renaming. This reuses the
existing module publication transaction instead of introducing a second cache
or a separate provisional-object trust mechanism.

This is a publication optimization, separate from
[incremental negative diagnostics](incremental-rocq.md). Failed revisions may
reuse a live sentence prefix; a new module publication still requires ordinary
compiler success. An identical already-published module can reuse its validated
object. Source/cache transactions live in
[`proof_stage/workspace.rs`](../src/engine/proof_stage/workspace.rs).

## Lifecycle and boundaries

- Failed drafts remain editable under the same name and persist between rounds
  through the ordinary untrusted scratch mechanism. They are not importable
  dependencies. The existing module-mode audit applies even though the file
  lives beneath `scratch/`; no source-audit rules are weakened.
- The first successful module check immediately publishes and freezes the name.
  Neither a modified draft nor a direct `ProofModules/Name.v` submission can
  replace it. Further work needs a new successor name. Identical resubmissions
  use the existing checked object without recompiling it.
- Local drafts can remain in scratch after publication, but are not authority.
  The host workspace/cache contains the published exact source; future rounds
  receive its ordinary `ProofModules/Name.v` source seed. Editing a local draft
  cannot change what later checks import.
- A new fixed-witness generation still discards scratch and the old module
  dependency context. No cross-generation reuse is added.
- Module success does not advance the `Problem.v` checkpoint. The root must
  still consume the helper, compile, and pass the unchanged final kernel checks.
- Direct `--mode module --candidate ProofModules/Name.v` remains supported.
  Ordinary scratch mode remains available for disposable probes and is not
  silently converted into publication. Its old objects cannot be reused under
  a different logical name.

The agent prompt now uses module mode from the first reusable-helper attempt,
rather than instructing it to scratch-check and then recompile a copied module.
Existing sessions with old instructions are not retroactively rewritten.

## Regression checks

[`test_module_draft_client.py`](../tests/test_module_draft_client.py) checks canonical wire identity, exact byte upload,
failure/revision, response mismatch rejection, invalid paths/symlinks, and
legacy modes using local Unix sockets. Engine tests cover draft round retention
without publication. The real broker/sandbox regression exercises failed draft
repair, publication, identical object reuse, immutable-name rejection, subsequent
root import, and final kernel checking:

```bash
# From the Logos repository root:
python3 -m unittest discover -s crates/logos-solver/tests -p test_module_draft_client.py -v
RUST_MIN_STACK=67108864 cargo test -p logos-solver --bin logos-solver engine:: -- --include-ignored --skip real_incremental_sandbox_diagnostics
cargo test -p logos-solver --bin logos-solver --no-run
# Set LOGOS_ROCQ_BROKER_TEST_BIN to the executable printed by --no-run above.
LOGOS_ROCQ_BROKER_TEST_BIN=/absolute/path/to/test-binary \
  bash crates/logos-solver/tests/test-trusted-rocq-check-sandbox.sh
```

The real regression also guards against a pre-existing rejection-path bug:
immutable-name conflicts must be rejected before creating the next numbered
diagnostic snapshot, otherwise that unused snapshot can break the next request.

This removes one successful full helper compilation from the old
scratch-then-module workflow. It does not claim that all historical duplicated
check time is recoverable or measure an end-to-end benchmark speedup.
