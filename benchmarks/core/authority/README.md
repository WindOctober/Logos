# Benchmark authority

This directory contains the repository-owned inputs that define Logos benchmark
campaigns. They are versioned with the benchmark sources and do not depend on a
particular experiment output directory.

- `cohort-389.json`: canonical 389-case membership and benchmark fingerprint.
- `non-rbot-materialization-baseline.json`: byte digests for the legacy
  non-R-Bot Logos materialization compatibility boundary.
Run artifacts belong under the repository-local `var/` tree and are not part
of benchmark authority.

Input authority defines the selected data, not experiment scheduling policy.
Concurrency and timeouts are configurable independently of cohort membership;
no prior experiment gate is required. See the
[runner selection contract](../../scripts/README.md#run-the-complete-logos-pipeline).
