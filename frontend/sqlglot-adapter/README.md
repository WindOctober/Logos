# SQLGlot Adapter

This adapter normalizes source SQL dialects into Calcite-friendly frontend SQL before `scripts/calcite-ir` exports Calcite JSON IR.

The adapter is not part of Logos' trusted SQL semantics. Its output is frontend input for Calcite only; semantic authority remains the later Logos/FormalSQL translation and Rocq checking pipeline.

## Compatibility Patches

In addition to SQLGlot transpilation, `normalize.py` applies small compatibility patches for syntax patterns that appear in benchmark SQL and are otherwise rejected by Calcite:

- `+/- n days` is normalized to `+/- INTERVAL 'n' DAY`.
- SQLGlot interval literals such as `INTERVAL '14 DAY'` are normalized to `INTERVAL '14' DAY`.
- `CAST(... AS DATE) +/- integer` is normalized to `CAST(... AS DATE) +/- INTERVAL 'n' DAY`.
- Simple date-column arithmetic, such as `d_date + 14`, is normalized to `d_date + INTERVAL '14' DAY`.

These patches are recorded in the optional normalization report. They should be treated as frontend compatibility rewrites, not as proof rules.
