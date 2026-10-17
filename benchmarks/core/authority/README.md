# Benchmark authority

This directory contains the repository-owned inputs that define Logos benchmark
campaigns. They are versioned with the benchmark sources and do not depend on a
particular experiment output directory.

- `cohort-389.json`: canonical 389-case membership and benchmark fingerprint.
- `proof-gate-16.json`: fixed 16-case authority for the legacy frozen full-run
  gate; the runner also validates treatment identity and recorded outcomes.
- `non-rbot-materialization-baseline.json`: byte digests for the legacy
  non-R-Bot Logos materialization compatibility boundary.
Run artifacts belong under the repository-local `var/` tree and are not part
of benchmark authority.

Membership alone does not enable the gate. Current enforcement is specific to
the exact legacy `.generated/sqlsolver` 389-case selection; a new run on
`.generated/logos` is a different input profile. The default development
regression wrapper is not automatically a valid frozen gate. See the
[runner selection contract](../../scripts/README.md#run-the-complete-logos-pipeline)
for required timeouts, the explicit ungated override, and matching requirements.
