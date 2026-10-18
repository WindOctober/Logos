# Lemma-library ablations

`logos-solver check` accepts two independent switches, both **on by default**:

| `--bag-lemmas` | `--other-lemmas` | Available pre-proved facts |
| --- | --- | --- |
| `on` | `on` | Full library; existing prompts and normal compiler path |
| `off` | `on` | Remaining facts, excluding bag-dependent wrappers |
| `on` | `off` | Bag facts and their public wrappers |
| `off` | `off` | No inventoried FormalSQL/Logos library lemmas |

For example, append `--bag-lemmas=off --other-lemmas=on` to a normal solver
invocation. With the benchmark runner, use
`--solver-arg=--bag-lemmas=off --solver-arg=--other-lemmas=on`.
Always use a fresh run directory for a different selection. Do not reuse agent
sessions, published modules, or proof checkpoints across treatments.

## What belongs to each group

The host inventories theorem declarations in the pinned `vendor/FormalSQL/src`
and `theories/FormalSQL` authority. This includes local and transparent theorem
declarations, not only the public opaque lemmas advertised by ordinary search.

The **bag** group is deliberately broader than BagClosed-to-list lifting:
bag algebra, bag equality/permutation reasoning, operator-level bag composition,
bag closure, and bag-to-observation lifting are included. The reproducible
classification seeds declarations whose names or statements contain bag
vocabulary (`bag`, `Bag`, `Febag`), bag equality notation, `alpha`/`gamma`
abstraction, or query/TNull permutation vocabulary; primitive finite-bag modules
are included as well. It then
closes over source-level theorem dependencies: wrappers using bag facts belong
to this group too. Ambiguous short names are grouped conservatively together.
All remaining inventoried theorems belong to **other**.

This is a broad, syntactic, versioned resource ablation, **not** a claim that a
semantic classifier has recognized every mathematically possible use of bags.
Audit the per-declaration grouping in the host-only `lemma-policy.json` before
publishing experiment results. The file records the exact authority digest and
the grouping, rather than relying on a fixed historical theorem count.

## Fixed foundation and enforcement

The SQL AST/evaluator, verification goals, definitions, constructors, Rocq
standard library, and exact generated admission/introduction scaffolding remain
unchanged. Agents may prove new helpers themselves. “Both off” therefore means
**no supplied library facts**, not “no semantics, no constructors, no tactics”.
Foundational definitions may internally use proofs; their implementation is not
removed. Enabled lemmas are checked library leaves: their private proofs may
use other facts. These switches control the agent's supplied proof interfaces,
not a re-foundation of FormalSQL without those mathematical facts.

For an ablated run:

- The agent receives only a source navigation view and a filtered declaration
  index; no original library proof bodies, `.vo` objects, catalogs, or full
  repository mount. Generated read-only context is also rendered as a navigation
  view; original exact files remain on the host for compilation and auditing.
- A lemma-independent primer and compact ablation instructions replace the
  full-library discovery/proof-route sections. The operational contract is shared
  with the standard prompt, so module publication and final claims do not diverge.
- Every diagnostic (including prefix probes) and final source audit rejects
  disabled identifiers. Introspection/hint registration and implicit unnamed or
  program-generated declarations are unavailable in this mode; use explicit
  named lemmas. Short-name checks are conservative, so avoid shadowing a disabled
  library name in local variables/declarations.
- Full candidate compilation privately prints and checks elaborated named
  declarations. This detects disabled constants inserted by tactics such as
  `auto`, even without explicit source references. Private proof-term frames are
  removed from the returned diagnostics. A probe is still only exploratory,
  never an accepted proof or published module.
- Module publication occurs only after this check. Final `Problem.v` is inspected
  again rather than using the full-library fast-path checkpoint shortcut.

The full authority is still compiled on the host. This is an experimental
proof-resource policy, not a sandbox against a deliberately adversarial prover
or a semantic prohibition against rediscovering an equivalent proof.

## Provenance and comparisons

`proofAgentConfiguration.lemmaAvailability` records the selection. Context
manifest version 9 binds `lemma-availability.json`, the selected primer and the
search helper. The host's `proof-stage/proof-agent/trusted-launcher/` contains the
full policy, authority digest, generated source surface and filtered index.
The benchmark runner fingerprints `effectiveSolverArgs`, checks the selection
against the context manifest, and continues to read historical version-8
contexts. Proof-tail recovery accepts version 9 and checks ablation policy
provenance before rechecking.

Hold the model, budgets, inputs and concurrency fixed across treatments. Ablated
runs have a different navigation/prompt surface and additional proof-term
inspection overhead; report these alongside solve rates and token/time costs.
Do not describe the results as a change to SQL equivalence semantics.
