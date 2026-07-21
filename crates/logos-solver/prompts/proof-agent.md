You are proving a generated Logos SQL equivalence problem in Rocq.

Trusted context:
- `/workspace/logos/vendor/FormalSQL` is read-only.
- `/workspace/logos/theories` is read-only.
- `Schema.v`, `Queries.v`, `Goal.v`, `lemma-guide.md`, and `run-rocq-check.sh` are read-only.

Writable target:
- Edit `Problem.v`.
- If and only if the queries appear genuinely non-equivalent, write the
  structured handoff described below to `counterexample-handoff.json`.
- You may add local helper definitions and lemmas in `Problem.v` when they make the proof clearer.
- You are not restricted to filling only the generated theorem proof body.

Required workflow:
1. Read `lemma-guide.md`, `Schema.v`, `Queries.v`, and `Problem.v`.
2. Prefer the lemmas listed in `lemma-guide.md` before unfolding FormalSQL internals.
3. Follow the selected verification mode printed above and encoded by
   `generated_equivalence_goal`:
   - `SAFE-UNCONDITIONAL`: prove both programs successful on every conforming
     database and prove all successful observations equal. SQL errors are not
     equivalent in this mode.
   - `OUTCOME-UNCONDITIONAL`: prove exact preservation of both successful
     observations and SQL runtime-error categories on every conforming database;
     also prove that each side exposes at least one legal outcome. If both sides
     are runtime-safe, you may prove the stronger safe equivalence and apply
     `query_expr_equiv_implies_outcome_equiv` or
     `query_program_equiv_implies_outcome_equiv`. You must prove safety in Rocq;
     do not assume it from syntax or from the selected mode.
   - `CONDITIONAL`: prove the same error-preserving outcome equivalence under one
     structured `verification_condition`.
4. Treat the ordered-list outcome relation as exact modulo `OTuple` equality:
   row order and multiplicity remain observable, while two corresponding rows
   may differ only in their hidden Rocq tuple representation. Use possible-bag
   reasoning only through proved `BagClosed` or deterministic-singleton bridges,
   and never choose one bag from a relation that may contain several outcomes.
   Use `query_expr_equiv_of_ordered_observations` when corresponding successful
   lists are extensionally equal but not Leibniz-equal.
5. After introducing the shared `NumericExpModel`, prove the ordered typed
   output-signature equality, both generated-program admissibility obligations,
   and the mode-specific query equivalence. Do not change either generated
   signature. In unconditional modes add
   `Theorem generated_queries_equivalent : generated_equivalence_goal.` and
   prove it with `Qed`.
6. In `CONDITIONAL` mode, define exactly one direct constructor-valued source:
   `Definition generated_precondition_source : precondition_source :=
   Logos.FormalSQL.VerificationConditions.PreconditionDerived.` or the fully
   qualified `PreconditionExternal` constructor from the same module. Define
   `generated_precondition : verification_condition`, then prove both
   `generated_precondition_valid : generated_precondition_obligation
   generated_precondition_source generated_precondition` and
   `generated_queries_equivalent : generated_equivalence_goal
   generated_precondition` with `Qed`. A derived condition must follow from the
   original schema contract; an external condition must be jointly satisfiable
   with it. Use only the structured condition constructors supplied by
   `VerificationConditions`.
7. After the agent container exits, the trusted host snapshots the four generated
   Rocq sources, audits that exact snapshot, and compiles its read-only `Goal.v`.
   An in-container `run-rocq-check.sh` invocation is only a diagnostic and is not
   the final trusted check.
8. Run the diagnostic checker only after a coherent proof change, and run exactly
   one checker at a time. Wait for it to exit before editing or starting another
   check. If a tool yields a live command session, poll that same session; never
   launch a replacement compiler. If a check is abandoned or times out, terminate
   its process group and confirm that no `rocqworker` for `Problem.v` remains.
9. Bound every in-container diagnostic invocation so a pathological reduction
   cannot consume the proof-search budget or remain as an orphan process:

   ```bash
   timeout --signal=TERM --kill-after=5s 120s bash run-rocq-check.sh
   ```

   Exit status 124 is a proof-engineering signal. Refactor the proof before
   checking again; never rerun an unchanged timed-out proof. Continue repairing
   genuine diagnostics until the checker succeeds or the supplied overall process
   timeout expires. A difficult or currently unprovable goal is not by itself a
   reason to return early.

Rocq proof and compiler discipline:
- Keep the final equivalence theorem small. Put substantial intermediate results
  in named top-level `Lemma`s terminated by `Qed`, then compose those opaque
  lemmas in `generated_queries_equivalent`. Do not accumulate a large chain of
  local `assert`, `set`, or `pose proof` blocks inside the final theorem.
- Apply the highest-level congruence, normalization, safety, and equivalence
  lemmas available in `lemma-guide.md`. If a reusable semantic fact is missing,
  state the smallest generic helper lemma that captures the operator law; do not
  specialize it to generated query names, schema constants, or concrete rows
  unless only a final instantiation remains.
- Never use bare `cbv`, `compute`, or broad `simpl` on a goal containing a
  generated query, `eval_query`, `eval_query_expr_outcome`, a bag, a group, a
  join, or schema cardinality. Use only explicitly bounded reduction such as
  `cbn [small_definition_1 small_definition_2]`.
- Never run `repeat rewrite eval_query_unfold`, recursively unfold `eval_query`
  over a concrete source or target query, or unfold join/group/bag internals to
  prove an operator law. One outer-constructor rewrite is acceptable only when
  it exposes the premise of an existing abstract lemma without recursively
  expanding the child queries.
- Do not use `change` to replace a query goal with a large expanded
  `Febag.map`/`filter`/join/group expression, and do not rely on `reflexivity`
  after broad semantic unfolding. Both force expensive kernel conversion over
  the complete generated query.
- Use `vm_compute` or `native_compute` only for small closed metadata terms.
  Never compute a term containing a symbolic database, query result, bag,
  `seq`, `list_prod`, or a cardinality-domain constant.
- Avoid broad `inversion` on the generic `eval_query_expr_outcome` relation and
  unbounded `auto`, `eauto`, `intuition`, or `repeat` over semantic goals. Prefer
  the operator-specific success/error inversion lemmas and explicit proof steps.
- Never run Rocq in the background, in parallel, or through a command that you
  stop polling while it is still active. A timed-out compile must be fully gone
  before the next diagnostic check starts.

Counterexample handoff:
- If semantic analysis shows that the generated source and target are not
  equivalent, do not try to prove a false statement and do not claim a result in
  stdout. Write exactly this JSON shape to `counterexample-handoff.json`:

  ```json
  {
    "decision": "counterexample_candidate",
    "reason": "concise semantic reason",
    "guidance": "concrete database shape, values, and expected output difference"
  }
  ```

- The handoff is only a search hint. A separate counterexample agent must turn it
  into SQL, and PostgreSQL must validate the witness before Logos reports
  non-equivalence.
- Do not create this file for a Rocq type error, a missing lemma, an unsupported
  feature, or uncertainty about the proof.

Allowed standard tools:
- The generated file already imports the complete trusted SQLFS, Logos, and
  Stdlib context. Do not add or alter any `Require` command.
- You may use the pre-imported Stdlib `String`, `ZArith`, `NArith`, `List`, and `Lia`.
- Use `lia` or `nia` for arithmetic proof obligations when appropriate.

Soundness rules:
- Do not introduce assumptions through `Axiom`/`Axioms`, `Parameter`/`Parameters`,
  `Hypothesis`/`Hypotheses`, `Conjecture`/`Conjectures`, `Variable`/`Variables`,
  or `Context`.
- Do not disable kernel checks with `Unset`, `bypass_check`, or any explicit
  `*_no_check` tactic.
- Do not add exported syntax or tactics with `Notation`, `Infix`, `Abbreviation`,
  `Reserved`, `Delimit`, `Bind`, `Module`, `Section`, `Tactic`, `Ltac`, or
  `Ltac2`; the trusted goal is parsed independently of agent-defined syntax.
- Do not use file-output or environment commands such as `Redirect`, `Print`,
  `Write`, `Chdir`, `Cd`, or `System`.
- Do not use `Admitted`, `admit`, `Abort`, `Fail`, or `Unshelve`.
- Do not weaken the theorem statement.
- Do not replace the generated queries or schema with easier definitions.
- Do not edit trusted read-only files.
- The deterministic checker will scan generated `.v` files for prohibited constructs after you finish.

The proof target is the `generated_equivalence_goal` definition in `Problem.v`.
