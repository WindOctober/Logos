#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SOURCE_LOGOS_ROOT="$(cd "$SCRIPT_DIR/../../.." && pwd)"
CHECKER="$SCRIPT_DIR/run-trusted-rocq-check.sh"
ROCQ_SWITCH="${LOGOS_ROCQ_OPAM_SWITCH:-$SOURCE_LOGOS_ROOT/.opam-rocq}"
ROCQ_BIN="$ROCQ_SWITCH/_opam/bin/rocq"
TEST_ROOT="$(mktemp -d "${TMPDIR:-/tmp}/logos-rocq-sandbox-regression.XXXXXX")"
LOGOS_REPO_ROOT="${LOGOS_TRUSTED_AUTHORITY_ROOT:-$TEST_ROOT/authority}"
WORKDIR="$TEST_ROOT/workspace"
CACHE_PARENT="$TEST_ROOT/cache-parent"
CACHE_DIR="$CACHE_PARENT/cache"
SHARED_PREFIX_CACHE="$TEST_ROOT/shared-prefix-cache"
SHARED_CHECKER_RUNTIME_CACHE="$TEST_ROOT/shared-checker-runtime-cache"
OUTSIDE_FILE="$TEST_ROOT/outside.v"
AMBIENT_HOME="$TEST_ROOT/ambient-home"
AMBIENT_ROCQPATH="$TEST_ROOT/ambient-rocqpath"
CLEAN_HOME="$TEST_ROOT/clean-home"
mkdir -p \
  "$WORKDIR" "$CACHE_PARENT" "$AMBIENT_HOME" "$AMBIENT_ROCQPATH" "$CLEAN_HOME"
cleanup_test_root() {
  chmod -R u+w "$TEST_ROOT/authority" "$TEST_ROOT/shared-prefix-cache" \
    "$TEST_ROOT/shared-checker-runtime-cache" \
    2>/dev/null || true
  rm -rf "$TEST_ROOT"
}
trap cleanup_test_root EXIT

if [[ -z "${LOGOS_TRUSTED_AUTHORITY_ROOT:-}" ]]; then
  mkdir -p "$LOGOS_REPO_ROOT/vendor/FormalSQL/src" \
    "$LOGOS_REPO_ROOT/theories/FormalSQL"
  while IFS= read -r -d '' source; do
    relative="${source#"$SOURCE_LOGOS_ROOT/vendor/FormalSQL/src"/}"
    install -D -m 444 "$source" \
      "$LOGOS_REPO_ROOT/vendor/FormalSQL/src/$relative"
    install -D -m 444 "${source%.v}.vo" \
      "$LOGOS_REPO_ROOT/vendor/FormalSQL/src/${relative%.v}.vo"
  done < <(find "$SOURCE_LOGOS_ROOT/vendor/FormalSQL/src" -type f -name '*.v' \
    ! -path '*/Examples/*' ! -path '*/examples/*' -print0)
  while IFS= read -r -d '' source; do
    relative="${source#"$SOURCE_LOGOS_ROOT/theories/FormalSQL"/}"
    install -D -m 444 "$source" \
      "$LOGOS_REPO_ROOT/theories/FormalSQL/$relative"
    install -D -m 444 "${source%.v}.vo" \
      "$LOGOS_REPO_ROOT/theories/FormalSQL/${relative%.v}.vo"
  done < <(find "$SOURCE_LOGOS_ROOT/theories/FormalSQL" -maxdepth 1 \
    -type f -name '*.v' ! -name '*Example.v' ! -name '*Examples.v' -print0)
  find "$LOGOS_REPO_ROOT" -type d -exec chmod 555 {} +
fi

if [[ ! -x "$ROCQ_BIN" ]]; then
  echo "Rocq binary is missing: $ROCQ_BIN" >&2
  exit 2
fi

# Positive control: without -q, this ambient rcfile is observable.  The
# trusted checker below receives the same hostile HOME but must neither run nor
# disclose it.
cat >"$AMBIENT_HOME/.coqrc" <<'EOF'
Definition AMBIENT_ROCQRC_SENTINEL_59B667D1 : nat := 73.
Print AMBIENT_ROCQRC_SENTINEL_59B667D1.
EOF
cat >"$TEST_ROOT/RcControl.v" <<'EOF'
Theorem rc_control : True.
Proof. exact I. Qed.
EOF
set +e
HOME="$AMBIENT_HOME" \
  ROCQPATH="$AMBIENT_ROCQPATH" \
  COQPATH="$AMBIENT_ROCQPATH" \
  "$ROCQ_BIN" compile -noglob -o "$TEST_ROOT/RcControl.vo" \
  "$TEST_ROOT/RcControl.v" \
  >"$TEST_ROOT/rc-control.stdout" 2>"$TEST_ROOT/rc-control.stderr"
rc_control_status="$?"
set -e
if ! grep -Fq 'AMBIENT_ROCQRC_SENTINEL_59B667D1' \
  "$TEST_ROOT/rc-control.stdout" "$TEST_ROOT/rc-control.stderr"; then
  echo "unsafe rcfile positive control did not expose its sentinel (status $rc_control_status)" >&2
  sed -n '1,20p' "$TEST_ROOT/rc-control.stderr" >&2
  exit 1
fi

cat >"$WORKDIR/Schema.v" <<'EOF'
From SQLFS Require Import SqlSyntax GenericInstance.
Definition sandbox_schema_marker : Prop := True.
EOF
cat >"$WORKDIR/Queries.v" <<'EOF'
From LogosGenerated Require Import Schema.
Definition sandbox_query_marker : Prop := sandbox_schema_marker.
EOF
cat >"$WORKDIR/Witness.v" <<'EOF'
From LogosGenerated Require Import Schema.
Definition sandbox_witness_marker : Prop := sandbox_schema_marker.
EOF
cat >"$WORKDIR/WitnessData.v" <<'EOF'
From LogosGenerated Require Import Schema.
Definition sandbox_witness_data_marker : Prop := sandbox_schema_marker.
EOF
mkdir -m 700 "$WORKDIR/WitnessModules"
: >"$WORKDIR/WitnessModules/ORDER"
cat >"$WORKDIR/Problem.v" <<'EOF'
From LogosGenerated Require Import Schema Queries Witness.
Theorem sandbox_problem_marker : sandbox_query_marker.
Proof. exact I. Qed.
EOF
cat >"$WORKDIR/Goal.v" <<'EOF'
From LogosGenerated Require Import Schema Queries Witness Problem.
Theorem sandbox_goal_marker : sandbox_query_marker.
Proof. exact sandbox_problem_marker. Qed.
EOF

checker_environment=(
  env
  "HOME=$AMBIENT_HOME"
  "ROCQPATH=$AMBIENT_ROCQPATH"
  "COQPATH=$AMBIENT_ROCQPATH"
  "LOGOS_REPO_ROOT=$LOGOS_REPO_ROOT"
  "LOGOS_PROOF_WORKDIR=$WORKDIR"
  "LOGOS_TRUSTED_ROCQ_CACHE_DIR=$CACHE_DIR"
  "LOGOS_SHARED_ROCQ_PREFIX_CACHE_DIR=$SHARED_PREFIX_CACHE"
  "LOGOS_SHARED_ROCQ_CHECKER_RUNTIME_CACHE_DIR=$SHARED_CHECKER_RUNTIME_CACHE"
  "LOGOS_TRUSTED_ROCQ_AUTHORITY_SHA256=$(printf 'authority-fixture' | sha256sum | awk '{print $1}')"
  "PATH=$ROCQ_SWITCH/_opam/bin:/usr/bin:/bin"
)

if ! timeout 180 "${checker_environment[@]}" bash "$CHECKER" --preflight \
  >"$TEST_ROOT/preflight.stdout" 2>"$TEST_ROOT/preflight.stderr"; then
  cat "$TEST_ROOT/preflight.stderr" >&2
  exit 1
fi
if [[ "$(find "$SHARED_PREFIX_CACHE" -mindepth 1 -maxdepth 1 -type d | wc -l)" != 1 ]]; then
  echo "initial preflight did not publish exactly one shared generated prefix" >&2
  exit 1
fi

schema_object_before="$(sha256sum "$CACHE_DIR/Schema.vo" | awk '{print $1}')"
queries_object_before="$(sha256sum "$CACHE_DIR/Queries.vo" | awk '{print $1}')"
cat >"$WORKDIR/Witness.v" <<'EOF'
From LogosGenerated Require Import Schema.
Definition sandbox_witness_marker : Prop := sandbox_schema_marker /\ True.
EOF
timeout 180 "${checker_environment[@]}" bash "$CHECKER" --witness-preflight \
  >"$TEST_ROOT/witness-preflight.stdout" 2>"$TEST_ROOT/witness-preflight.stderr"
if [[ "$(sha256sum "$CACHE_DIR/Schema.vo" | awk '{print $1}')" != "$schema_object_before" ||
      "$(sha256sum "$CACHE_DIR/Queries.vo" | awk '{print $1}')" != "$queries_object_before" ||
      -s "$CACHE_DIR/ProofModules/ORDER" ||
      "$(find "$SHARED_PREFIX_CACHE" -mindepth 1 -maxdepth 1 -type d | wc -l)" != 2 ]]; then
  echo "witness-only preflight did not preserve Schema/Queries and replace its generation" >&2
  exit 1
fi

mv "$CACHE_DIR" "$CACHE_PARENT/cache-before-shared-hit"
timeout 180 "${checker_environment[@]}" bash "$CHECKER" --preflight \
  >"$TEST_ROOT/shared-hit-preflight.stdout" \
  2>"$TEST_ROOT/shared-hit-preflight.stderr"
if [[ "$(sha256sum "$CACHE_DIR/Schema.vo" | awk '{print $1}')" != "$schema_object_before" ||
      "$(sha256sum "$CACHE_DIR/Queries.vo" | awk '{print $1}')" != "$queries_object_before" ]]; then
  echo "shared generated-prefix cache hit changed Schema/Queries objects" >&2
  exit 1
fi
if ! grep -Fq 'LOGOS_TRUSTED_ROCQ_PREFIX_CACHE hit=true' \
  "$TEST_ROOT/shared-hit-preflight.stderr"; then
  echo "second preflight did not report a shared generated-prefix cache hit" >&2
  exit 1
fi
rm -rf "$CACHE_PARENT/cache-before-shared-hit"

mkdir -m 700 "$WORKDIR/ProofModules"
cat >"$WORKDIR/ProofModules/CoreFacts.v" <<'EOF'
From LogosGenerated Require Import Schema Queries Witness.
Theorem sandbox_core_marker : sandbox_query_marker.
Proof. exact I. Qed.
EOF
if ! timeout 90 "${checker_environment[@]}" \
  bash "$CHECKER" --module-diagnostic \
    --candidate ProofModules/CoreFacts.v --timeout-seconds 30 \
  >"$TEST_ROOT/module-core.stdout" 2>"$TEST_ROOT/module-core.stderr"; then
  cat "$TEST_ROOT/module-core.stderr" >&2
  exit 1
fi
core_object_sha256="$(sha256sum "$CACHE_DIR/ProofModules/CoreFacts.vo" | awk '{print $1}')"
core_manifest_sha256="$(sha256sum "$CACHE_DIR/SHA256SUMS" | awk '{print $1}')"
if ! timeout 90 "${checker_environment[@]}" \
  bash "$CHECKER" --module-diagnostic \
    --candidate ProofModules/CoreFacts.v --timeout-seconds 30 \
  >"$TEST_ROOT/module-core-idempotent.stdout" \
  2>"$TEST_ROOT/module-core-idempotent.stderr"; then
  cat "$TEST_ROOT/module-core-idempotent.stderr" >&2
  exit 1
fi
if ! grep -Fq 'LOGOS_TRUSTED_ROCQ_CHECKER_RUNTIME_CACHE hit=true' \
  "$TEST_ROOT/module-core-idempotent.stderr"; then
  echo "repeated module diagnostic did not reuse the checker runtime closure" >&2
  exit 1
fi
if ! grep -Fq 'already_cached=true' "$TEST_ROOT/module-core-idempotent.stderr" ||
   [[ "$(grep -Fxc 'CoreFacts.v' "$CACHE_DIR/ProofModules/ORDER")" != 1 ]] ||
   [[ "$(sha256sum "$CACHE_DIR/ProofModules/CoreFacts.vo" | awk '{print $1}')" != \
      "$core_object_sha256" ]] ||
   [[ "$(sha256sum "$CACHE_DIR/SHA256SUMS" | awk '{print $1}')" != \
      "$core_manifest_sha256" ]]; then
  echo "byte-identical module promotion was not cache-idempotent" >&2
  exit 1
fi
cat >"$WORKDIR/ProofModules/MoreFacts.v" <<'EOF'
From LogosGenerated Require Import Queries.
From LogosGenerated.ProofModules Require Import CoreFacts.
Theorem sandbox_more_marker : sandbox_query_marker.
Proof. exact sandbox_core_marker. Qed.
EOF
if ! timeout 90 "${checker_environment[@]}" \
  bash "$CHECKER" --module-diagnostic \
    --candidate ProofModules/MoreFacts.v --timeout-seconds 30 \
  >"$TEST_ROOT/module-more.stdout" 2>"$TEST_ROOT/module-more.stderr"; then
  cat "$TEST_ROOT/module-more.stderr" >&2
  exit 1
fi
if [[ "$(sha256sum "$CACHE_DIR/ProofModules/CoreFacts.vo" | awk '{print $1}')" != \
      "$core_object_sha256" ]]; then
  echo "a later module diagnostic replaced an earlier checked object" >&2
  exit 1
fi

# A checked module name is immutable even when replacement bytes also compile.
cp "$WORKDIR/ProofModules/CoreFacts.v" "$TEST_ROOT/CoreFacts.good.v"
cat >"$WORKDIR/ProofModules/CoreFacts.v" <<'EOF'
From LogosGenerated Require Import Schema Queries Witness.
Theorem sandbox_core_marker : sandbox_query_marker.
Proof. exact I. Qed.
Theorem forbidden_same_name_replacement : True.
Proof. exact I. Qed.
EOF
set +e
timeout 90 "${checker_environment[@]}" \
  bash "$CHECKER" --module-diagnostic \
    --candidate ProofModules/CoreFacts.v --timeout-seconds 30 \
  >"$TEST_ROOT/module-replace.stdout" 2>"$TEST_ROOT/module-replace.stderr"
module_replace_status="$?"
set -e
if ((module_replace_status == 0 || module_replace_status == 86 ||
     module_replace_status == 124 || module_replace_status == 137)); then
  echo "immutable module replacement was not rejected normally (status $module_replace_status)" >&2
  exit 1
fi
cp "$TEST_ROOT/CoreFacts.good.v" "$WORKDIR/ProofModules/CoreFacts.v"

cat >"$WORKDIR/Problem.v" <<'EOF'
From LogosGenerated Require Import Schema Queries Witness.
From LogosGenerated.ProofModules Require Import MoreFacts.
Theorem sandbox_problem_marker : sandbox_query_marker.
Proof. exact sandbox_more_marker. Qed.
EOF
cp "$WORKDIR/Problem.v" "$TEST_ROOT/Problem.good.v"
cat >"$WORKDIR/Goal.v" <<'EOF'
From LogosGenerated Require Import Schema Queries Witness Problem.
Theorem sandbox_goal_marker : sandbox_query_marker.
Proof. exact sandbox_problem_marker. Qed.
EOF
timeout 90 "${checker_environment[@]}" \
  bash "$CHECKER" --problem-diagnostic --timeout-seconds 30 \
  >"$TEST_ROOT/ordinary.stdout" 2>"$TEST_ROOT/ordinary.stderr"
if [[ ! -s "$CACHE_PARENT/problem-compile-cache/Problem.vo" ]]; then
  echo "successful Problem diagnostic did not publish its compiled-object cache" >&2
  exit 1
fi
if [[ "$(sha256sum "$CACHE_DIR/ProofModules/CoreFacts.vo" | awk '{print $1}')" != \
      "$core_object_sha256" ]]; then
  echo "Problem.v diagnostic replaced a checked helper object" >&2
  exit 1
fi
if grep -Fq 'AMBIENT_ROCQRC_SENTINEL_59B667D1' \
  "$TEST_ROOT/preflight.stdout" "$TEST_ROOT/preflight.stderr" \
  "$TEST_ROOT/module-core.stdout" "$TEST_ROOT/module-core.stderr" \
  "$TEST_ROOT/module-more.stdout" "$TEST_ROOT/module-more.stderr" \
  "$TEST_ROOT/ordinary.stdout" "$TEST_ROOT/ordinary.stderr"; then
  echo "ambient Rocq rcfile leaked into the trusted checker" >&2
  exit 1
fi
cat >"$OUTSIDE_FILE" <<'EOF'
Definition HOST_SENTINEL_PAYLOAD_7F8F65C4 : nat := 42.
Print HOST_SENTINEL_PAYLOAD_7F8F65C4.
EOF
cat >"$WORKDIR/Problem.v" <<EOF
From LogosGenerated Require Import Schema Queries Witness.
Load "$OUTSIDE_FILE".
EOF
outside_sha256_before="$(sha256sum "$OUTSIDE_FILE" | awk '{print $1}')"

# Positive control: the exact malicious Problem.v loads and prints the host
# sentinel when compiled without the empty-root sandbox.
UNSAFE_CONTROL="$TEST_ROOT/unsafe-control"
mkdir -p "$UNSAFE_CONTROL"
cp "$CACHE_DIR/Schema.vo" "$CACHE_DIR/Queries.vo" "$CACHE_DIR/Witness.vo" "$UNSAFE_CONTROL/"
mkdir -p "$UNSAFE_CONTROL/ProofModules"
cp "$CACHE_DIR/ProofModules/CoreFacts.vo" "$CACHE_DIR/ProofModules/MoreFacts.vo" \
  "$UNSAFE_CONTROL/ProofModules/"
cp "$WORKDIR/Problem.v" "$UNSAFE_CONTROL/Problem.v"
HOME="$CLEAN_HOME" ROCQPATH= COQPATH= \
  "$ROCQ_BIN" compile -q -noglob -o "$UNSAFE_CONTROL/Problem.vo" \
  -coqlib "$ROCQ_SWITCH/_opam/lib/coq" \
  -Q "$LOGOS_REPO_ROOT/vendor/FormalSQL/src" SQLFS \
  -Q "$LOGOS_REPO_ROOT/theories" Logos \
  -Q "$UNSAFE_CONTROL" LogosGenerated \
  "$UNSAFE_CONTROL/Problem.v" \
  >"$TEST_ROOT/unsafe-control.stdout" 2>"$TEST_ROOT/unsafe-control.stderr"
if ! grep -Fq 'HOST_SENTINEL_PAYLOAD_7F8F65C4' \
  "$TEST_ROOT/unsafe-control.stdout" "$TEST_ROOT/unsafe-control.stderr"; then
  echo "unsafe Load positive control did not expose its sentinel" >&2
  exit 1
fi

set +e
timeout 90 "${checker_environment[@]}" \
  bash "$CHECKER" --problem-diagnostic --timeout-seconds 30 \
  >"$TEST_ROOT/attack.stdout" 2>"$TEST_ROOT/attack.stderr"
attack_status="$?"
set -e
if ((attack_status == 0)); then
  echo "host-only Load unexpectedly succeeded inside the diagnostic sandbox" >&2
  exit 1
fi
if ((attack_status == 86 || attack_status == 124 || attack_status == 137)); then
  echo "sandbox attack failed through environment breakage or timeout, not path isolation" >&2
  exit 1
fi
if grep -Fq 'HOST_SENTINEL_PAYLOAD_7F8F65C4' \
  "$TEST_ROOT/attack.stdout" "$TEST_ROOT/attack.stderr"; then
  echo "host-only sentinel payload leaked through diagnostic checker output" >&2
  exit 1
fi
outside_sha256_after="$(sha256sum "$OUTSIDE_FILE" | awk '{print $1}')"
if [[ "$outside_sha256_after" != "$outside_sha256_before" ]]; then
  echo "host-only sentinel file changed during the sandbox regression" >&2
  exit 1
fi

# Exercise the complete trusted Goal/kernel/axiom path with the benign fixture,
# not only preflight and problem-only compilation.
cp "$TEST_ROOT/Problem.good.v" "$WORKDIR/Problem.v"

expect_final_module_rejection() {
  local label="$1" status
  set +e
  timeout 90 "${checker_environment[@]}" bash "$CHECKER" \
    >"$TEST_ROOT/$label.stdout" 2>"$TEST_ROOT/$label.stderr"
  status="$?"
  set -e
  if ((status == 0 || status == 124 || status == 137)); then
    echo "unsafe final module source state was not rejected normally: $label (status $status)" >&2
    exit 1
  fi
}

cat >"$WORKDIR/ProofModules/Unchecked.v" <<'EOF'
Lemma unchecked : True. Proof. exact I. Qed.
EOF
expect_final_module_rejection final-unchecked-module
rm "$WORKDIR/ProofModules/Unchecked.v"

cp "$WORKDIR/ProofModules/CoreFacts.v" "$TEST_ROOT/CoreFacts.final-good.v"
printf '\n(* modified after promotion *)\n' >>"$WORKDIR/ProofModules/CoreFacts.v"
expect_final_module_rejection final-modified-module
cp "$TEST_ROOT/CoreFacts.final-good.v" "$WORKDIR/ProofModules/CoreFacts.v"

ln -s "$TEST_ROOT/CoreFacts.final-good.v" "$WORKDIR/ProofModules/Symlinked.v"
expect_final_module_rejection final-symlinked-module
rm "$WORKDIR/ProofModules/Symlinked.v"

printf 'agent-produced object bytes\n' >"$WORKDIR/ProofModules/Injected.vo"
expect_final_module_rejection final-agent-object
rm "$WORKDIR/ProofModules/Injected.vo"

mv "$WORKDIR/ProofModules/MoreFacts.v" "$TEST_ROOT/MoreFacts.missing.v"
expect_final_module_rejection final-missing-module
mv "$TEST_ROOT/MoreFacts.missing.v" "$WORKDIR/ProofModules/MoreFacts.v"

write_test_cache_manifest() {
  (
    cd "$CACHE_DIR"
    {
      sha256sum Schema.v Schema.vo Queries.v Queries.vo Witness.v Witness.vo ProofModules/ORDER
      while IFS= read -r file || [[ -n "$file" ]]; do
        [[ -n "$file" ]] || continue
        stem="${file%.v}"
        sha256sum "ProofModules/$file" "ProofModules/$stem.vo"
      done <ProofModules/ORDER
    } >SHA256SUMS
  )
}

# Final assembly reuses only helper objects that the host module diagnostic
# published into the manifest-bound cache. Even an internally rehashed cache
# must fail closed when an object no longer parses as the checked module.
cp "$CACHE_DIR/ProofModules/CoreFacts.vo" "$TEST_ROOT/CoreFacts.good.vo"
cp "$CACHE_DIR/ProofModules/MoreFacts.vo" "$TEST_ROOT/MoreFacts.good.vo"
printf 'not a Rocq object: CoreFacts\n' >"$CACHE_DIR/ProofModules/CoreFacts.vo"
printf 'not a Rocq object: MoreFacts\n' >"$CACHE_DIR/ProofModules/MoreFacts.vo"
write_test_cache_manifest
expect_final_module_rejection final-corrupt-cached-object

cp "$TEST_ROOT/CoreFacts.good.vo" "$CACHE_DIR/ProofModules/CoreFacts.vo"
cp "$TEST_ROOT/MoreFacts.good.vo" "$CACHE_DIR/ProofModules/MoreFacts.vo"
write_test_cache_manifest
timeout 180 "${checker_environment[@]}" bash "$CHECKER" \
  >"$TEST_ROOT/final.stdout" 2>"$TEST_ROOT/final.stderr"
if grep -Fq 'AMBIENT_ROCQRC_SENTINEL_59B667D1' \
  "$TEST_ROOT/final.stdout" "$TEST_ROOT/final.stderr"; then
  echo "ambient Rocq rcfile leaked into the complete trusted check" >&2
  exit 1
fi
if ! grep -Fq 'LOGOS_TRUSTED_ROCQ_PROBLEM_CACHE hit=true' \
  "$TEST_ROOT/final.stderr"; then
  echo "final certification did not reuse the passing Problem diagnostic object" >&2
  exit 1
fi

cp "$CACHE_PARENT/problem-compile-cache/Problem.vo" "$TEST_ROOT/Problem.cached.good.vo"
printf 'corrupt cached Problem object\n' >"$CACHE_PARENT/problem-compile-cache/Problem.vo"
expect_final_module_rejection final-corrupt-problem-cache
cp "$TEST_ROOT/Problem.cached.good.vo" "$CACHE_PARENT/problem-compile-cache/Problem.vo"

echo "trusted Rocq diagnostic sandbox regression passed"
