# Rocq declaration search cache

[`search-rocq-declarations.py`](../scripts/search-rocq-declarations.py) caches the **complete** parsed declaration
index across CLI processes by default. Exact filters, lexical ordering, source
locations, statements, result JSON, and pagination are unchanged. There is no
query-specific shortlist, ranking, or truncation.

## Binding and failure behavior

- The SHA-256 key covers the helper's bytes, index schema, relative source paths,
  logical module prefixes, and every selected `.v` file's contents. Source bytes
  are read and hashed on every query; neither timestamps nor a caller-supplied
  digest can authorize reuse. Added, deleted, renamed, or edited files invalidate
  the index, including edits with unchanged size and modification time.
- Cold builds parse the exact bytes captured for the key, avoiding a second read
  between hashing and parsing. The existing source selection and duplicate-FQN
  checks remain in place. Mutable standalone trees are supported; a consistent
  concurrent-write snapshot is not promised (the proof authority is immutable).
- The cache contains JSON, not executable pickle data. Readers check the key,
  schema, payload checksum, record types, source membership, ordering, and FQN
  uniqueness. Missing, incompatible, corrupt, or inaccessible caches fall back
  to parsing; actual source/parser errors are still reported.
- Private, user-owned directories and no-follow cache reads avoid accepting
  another user's cache or following cache-file symlinks. Atomic replacement
  prevents partial reads. Concurrent cold processes may independently build the
  same index, but do not block on a persistent lock.
- This is disposable navigation data, **not proof evidence or a security boundary
  against its owning agent**. Its checksum detects corruption, not malicious
  same-user replacement. Agents must still inspect reported source statements;
  trusted compiler/kernel checks and immutable authority mounts are unchanged.

## Location and lifecycle

The default is `tempfile.gettempdir()/logos-rocq-declarations-<uid>` (normally
`$TMPDIR/logos-rocq-declarations-<uid>`). The existing Docker launcher sets
`TMPDIR=/workspace/tmp`, so queries within one agent container reuse the index
without a writable authority or host mount. It counts against the existing
workspace tmpfs quota and disappears with that container; there is no cross-case
or cross-container persistence by default. A new container pays one cold build.

Use `--cache-dir PATH` for an explicit private directory, or `--no-cache` to
bypass both reads and writes. A pre-existing group/world-accessible cache
directory is rejected without changing permissions, and search falls back to
parsing. Outside Docker, content-addressed entries remain until the temporary
directory is cleaned; there is no background eviction service.

## Validation and local measurement

Run from `Logos/`:

```bash
python3 -m unittest discover -s crates/logos-solver/tests -p test_search_rocq_declarations.py -v
```

Local measurement on 2026-10-16, 3,437 declarations, five independent CLI
processes per mode querying the same exact FQN with `--show-statement`:

| Mode | Median wall time |
| --- | ---: |
| `--no-cache` | 2,149 ms |
| Warm cache | 98 ms |

First index construction took 2,151 ms. Outputs were byte-identical. These times
include Python startup, source enumeration/read/hash, index deserialization and
validation, filtering, and JSON output. The warm CLI was about 22× faster; this
is **not** an end-to-end proof/benchmark speedup measurement. Repeated parsing
has been removed, but source enumeration and hashing deliberately remain.
