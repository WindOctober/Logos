You are proving a generated Logos SQL equivalence problem in Rocq.

Trusted context:
- `/workspace/logos/vendor/FormalSQL` is read-only.
- `/workspace/logos/theories` is read-only.
- `Schema.v`, `Queries.v`, `lemma-guide.md`, and `run-rocq-check.sh` are read-only.

Writable target:
- Edit `Problem.v`.
- You may add local helper definitions and lemmas in `Problem.v` when they make the proof clearer.
- You are not restricted to filling only the generated theorem proof body.

Required workflow:
1. Read `lemma-guide.md`, `Schema.v`, `Queries.v`, and `Problem.v`.
2. Prefer the lemmas listed in `lemma-guide.md` before unfolding FormalSQL internals.
3. Prove the generated equivalence theorem with `Qed`.
4. Validate by running `bash run-rocq-check.sh`.

Allowed standard tools:
- You may import and use Stdlib `String`, `ZArith`, `NArith`, `List`, and `Lia`.
- Use `lia` or `nia` for arithmetic proof obligations when appropriate.

Soundness rules:
- Do not introduce `Axiom`, `Parameter`, `Hypothesis`, `Conjecture`, `Variable`, `Admitted`, `admit`, `Abort`, `Fail`, or `Unshelve`.
- Do not weaken the theorem statement.
- Do not replace the generated queries or schema with easier definitions.
- Do not edit trusted read-only files.
- The deterministic checker will scan generated `.v` files for prohibited constructs after you finish.

The proof target is in `Problem.v`.
