# TPC-DS Query Variants

This directory contains materialized TPC-DS base/variant query pairs. The raw TPC-DS kit is not required at benchmark runtime.

## Layout

```text
create_tables.sql          shared TPC-DS schema
manifest.tsv               pair metadata and feature tags
queryNNN/queryNNN_0.sql    base query generated from query_templates/queryN.tpl
queryNNN/queryNNN_1.sql    variant query generated from query_variants/queryNa.tpl
```

The schema is workload-level metadata:

```text
create_tables.sql -> 14 base/variant query pairs
```

## Generation

These files were generated from `gregrahn/tpcds-kit` commit `5a3a817` with `dsqgen` using:

```bash
dsqgen -PATH_SEP / \
  -DIRECTORY ../query_templates \
  -TEMPLATE <template> \
  -DIALECT ansi \
  -SCALE 1 \
  -COUNT 1 \
  -OUTPUT_DIR <output-dir>
```

For each pair, the base query uses `query_templates/queryN.tpl` and the rewrite uses `query_variants/queryNa.tpl`.

## Notes

These are official TPC-DS query variants, not solver-normalized inputs. Many cases include SQL features such as `TOP`, `ROLLUP`, `GROUPING`, window functions, `FULL OUTER JOIN`, and `INTERSECT`. Solver runners should record these feature tags and may need dialect normalization before invoking SQLSolver or QED.
