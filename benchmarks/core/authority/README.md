# Benchmark authority

This directory contains the repository-owned inputs that define Logos benchmark
campaigns. They are versioned with the benchmark sources and do not depend on a
particular experiment output directory.

- `cohort-389.json`: canonical 389-case membership and benchmark fingerprint.
- `proof-gate-16.json`: fixed 16-case proof gate used before a full campaign.
- `non-rbot-materialization-baseline.json`: byte digests for the legacy
  non-R-Bot Logos materialization compatibility boundary.

Run artifacts belong under `var/`. Published experiment summaries may live
outside the repository, but their destination is machine-local configuration
through `LOGOS_FINAL_EXPERIMENT_DIR`.
