You are helping Logos check whether two SQL queries are equivalent.

Your task is to synthesize a small concrete database that may separate the two
queries. Use the supplied schema exactly. The host uses PostgreSQL only to
type-check your DML, enforce integrity constraints, and freeze the database
into a typed FormalSQL witness. It does not execute the query pair or derive an
EQ/NEQ verdict. Do not include CREATE TABLE statements.

The shared FormalSQL observation model appears before this request. Apply it
when designing the candidate, especially around tied ORDER BY keys, unordered
top-k (OFFSET/FETCH), and DISTINCT ON peer selection. The trusted Rocq selector
will decide whether the fixed database is a countermodel.

Write exactly one JSON object to this file:

{{OUTPUT_JSON_PATH}}

Do not put the final JSON answer in stdout. Stdout/stderr are treated only as
debug logs by the deterministic framework.

Allowed decisions:
- "counterexample_candidate": you found a candidate database. The host will
  materialize it, then the trusted Rocq selector must prove complete outcome
  separation before Logos can report NEQ.
- "no_candidate": you did not find a counterexample candidate and the pair should proceed to
  equivalence verification in the same proof session.
- "needs_review": you believe there is a counterexample, but it cannot be
  expressed as a compact executable PostgreSQL witness for the current
  framework. Unknown observation uniqueness alone is not a reason to discard a
  usable witness; the host can retain it only as proof-search feedback.

JSON schema:
{
  "decision": "counterexample_candidate" | "no_candidate" | "needs_review",
  "reason": "short explanation",
  "witnessSql": "non-empty direct INSERT/UPDATE/DELETE statements for a counterexample_candidate; otherwise an empty string",
  "notes": "optional extra details"
}

Rules:
- The witnessSql must be valid PostgreSQL SQL.
- A `counterexample_candidate` must contain a non-empty `witnessSql`. If no
  finite executable witness can be constructed, return `needs_review` instead.
- Every top-level witnessSql statement must begin directly with INSERT, UPDATE,
  or DELETE. CTE-prefixed statements, transaction control, SET, DDL, CALL, and
  DO are rejected by the deterministic checker.
- Use small table instances unless a larger instance is required.
- Prefer INSERT statements.
- The host executes only the schema and witnessSql in a fresh PostgreSQL
  schema. It never executes source or target as part of counterexample
  acceptance, because a physical plan may choose only one legal observation.
- Construct the database from SQL semantics, including multiplicity, ties,
  NULLs, runtime errors, and integrity constraints. A candidate is useful even
  when PostgreSQL execution order would be underspecified: FormalSQL/Rocq, not
  the executor, decides whether all required outcomes are separated.
- Prefer a candidate over `needs_review` whenever a compact executable
  database can be supplied. Use `needs_review` only when it cannot.
- Logos canonicalizes final output labels by ordinal before comparing a query
  pair. A difference only in the spelling of a final SELECT alias is not a
  counterexample; positional arity, types, and typmods are handled separately
  by the host's static output preflight, while rows and errors require the
  trusted FormalSQL selector.
- If a previous attempt failed, use the feedback below to repair the instance.
- If the two queries appear equivalent, use "no_candidate".

Schema:
```sql
{{SCHEMA_SQL}}
```

Authoritative benchmark integrity contract (this includes constraints carried
outside the parser-facing DDL; the PostgreSQL materializer enforces it):

```text
{{INTEGRITY_CONTRACT}}
```

Source query:
```sql
{{SOURCE_SQL}}
```

Target query:
```sql
{{TARGET_SQL}}
```

Provider invocation {{ROUND}} of at most {{MAX_ROUNDS}}. The semantic
witness-attempt budget is {{SEMANTIC_ROUND_BUDGET}}. Treat it as the total
budget for witness reasoning and several short experiments, not as permission
to spend the entire attempt on one command. A small witness in a fresh schema
should normally make an individual check finish in roughly 30--90 seconds;
about two or three minutes is a strong practical upper bound before you should
simplify the witness or change the experiment instead of merely waiting longer.
This is proof-search guidance, not a host-enforced deadline. The larger provider
bound only reserves at most one same-session contract-repair turn per semantic
attempt, and a repair does not create another independent witness opportunity.

Previous checker feedback:
{{FEEDBACK}}
