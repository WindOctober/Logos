# WeTune Core Schemas

This directory contains generated frontend schemas and semantic schema sidecars derived
from the raw WeTune application schema dumps in `../`.

Regenerate the files with:

```bash
scripts/wetune-schema-sanitize --all
```

The sanitizer is intentionally conservative and auditable:

- keeps `CREATE TABLE` declarations in parser-facing normalized DDL;
- keeps column names, lowered frontend scalar types, and `NOT NULL` in that DDL;
- preserves each column's original declaration, source type, nullability, default,
  generated flag, auto-increment flag, and frontend-lowered type in the matching
  `*.schema.constraints.json` sidecar;
- keeps `PRIMARY KEY` and `UNIQUE` constraints when they are declared inline or
  through PostgreSQL `ALTER TABLE ... ADD CONSTRAINT`;
- keeps simple `CREATE UNIQUE INDEX ... (col, ...)` declarations as uniqueness
  constraints;
- extracts `FOREIGN KEY`, `CHECK`, and partial or expression unique index
  constraints into `*.schema.constraints.json` sidecars instead of silently
  dropping them;
- strips deployment/runtime DDL such as `SET`, `CREATE EXTENSION`,
  `CREATE SEQUENCE`, `ALTER SEQUENCE`, `DROP TABLE`, ordinary non-unique
  indexes, table storage options, and MySQL versioned dump comments.

Each `*.report.json` file records the number of retained tables, columns, type
lowerings, keys, unique constraints, extracted semantic constraints, unsupported
semantic constraints, and non-semantic dropped table-level items for the corresponding
source schema.

The normalized DDL alone is not the full schema semantics. Consumers that need
semantics-preserving verification should load both `*.schema.sql` and the matching
`*.schema.constraints.json` sidecar. The sidecar's source declarations and constraints
are authoritative for benchmark semantics; the normalized DDL is a baseline frontend
lowering. If a baseline tool cannot consume those sidecar types or constraints, report
that as a tool limitation.
