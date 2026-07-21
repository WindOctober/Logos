You are helping Logos check whether two SQL queries are equivalent.

Your task is to construct a small concrete PostgreSQL instance that makes the
two queries return different results. Use the supplied schema exactly as the
database schema. If you can find a counterexample, output SQL statements that
insert the counterexample data. Do not include CREATE TABLE statements.

Write exactly one JSON object to this file:

{{OUTPUT_JSON_PATH}}

Do not put the final JSON answer in stdout. Stdout/stderr are treated only as
debug logs by the deterministic framework.

Allowed decisions:
- "counterexample_candidate": you found a candidate witness instance.
- "no_candidate": you did not find a counterexample candidate and the pair should proceed to
  symbolic equivalence checking or a proof attempt.
- "manual_review": you believe there is a counterexample, but it cannot be
  expressed compactly or deterministically checked by the current framework.

JSON schema:
{
  "decision": "counterexample_candidate" | "no_candidate" | "manual_review",
  "reason": "short explanation",
  "witnessSql": "SQL INSERT/UPDATE/DELETE statements for the witness instance, or empty string",
  "notes": "optional extra details"
}

Rules:
- The witnessSql must be valid PostgreSQL SQL.
- Every top-level witnessSql statement must begin directly with INSERT, UPDATE,
  or DELETE. CTE-prefixed statements, transaction control, SET, DDL, CALL, and
  DO are rejected by the deterministic checker.
- Use small table instances unless a larger instance is required.
- Prefer INSERT statements.
- The deterministic checker will execute the schema, then witnessSql, then both
  queries in a fresh PostgreSQL schema.
- If a previous attempt failed, use the feedback below to repair the instance.
- If the two queries appear equivalent, use "no_candidate".

Schema:
```sql
{{SCHEMA_SQL}}
```

Authoritative benchmark integrity contract (this includes constraints carried
outside the parser-facing DDL; the deterministic validator enforces it):

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

Attempt {{ROUND}} of {{MAX_ROUNDS}}.

Previous checker feedback:
{{FEEDBACK}}
