# SQLGlot Adapter

This adapter normalizes source SQL dialects into Calcite-friendly frontend SQL before `scripts/calcite-ir` exports Calcite JSON IR.

`scripts/calcite-ir-sqlglot` reads PostgreSQL by default. Other source
dialects must opt in with `--read`; this prevents an omitted flag from
silently changing PostgreSQL behavior such as ascending NULL placement.

The adapter is not part of Logos' trusted SQL semantics. Its output is frontend input for Calcite only; semantic authority remains the later Logos/FormalSQL translation and Rocq checking pipeline.

## Compatibility Patches

In addition to SQLGlot transpilation, `normalize.py` applies only
syntax-preserving compatibility patches needed by the parser boundary:

- SQLGlot interval literals such as `INTERVAL '14 DAY'` are normalized to `INTERVAL '14' DAY`.
- TPC-DS-style output aliases nested in an `ORDER BY` expression are expanded
  only when the alias is pure `GROUPING` arithmetic; standalone aliases remain
  unchanged and unknown function expressions fail closed.
- PostgreSQL timestamp-with-time-zone type nodes are rendered through a
  SQLGlot PostgreSQL generator using Calcite's spelling. Identifiers named
  `timestamptz` are never treated as types. Source `TIMESTAMP WITH LOCAL TIME
  ZONE` type nodes recognized by the configured input dialect are rejected
  structurally before rendering, independently of the selected output dialect,
  because they have different semantics.

Ambiguous text such as `1 + 2 days`, date-plus-integer expressions, and
identifier-name heuristics are never reinterpreted as intervals. If Calcite
cannot accept the source meaning, ingestion fails conservatively. Applied
patches are recorded in the optional normalization report.
