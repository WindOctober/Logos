#!/usr/bin/env bash
set -euo pipefail

: "${LOGOS_REPO_ROOT:?set LOGOS_REPO_ROOT to the Logos repository root}"

WORKDIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LOGOS_REPO_ROOT="$(cd "$LOGOS_REPO_ROOT" && pwd)"
CHECKDIR="$(mktemp -d "${TMPDIR:-/tmp}/logos-rocq-check.XXXXXX")"
trap 'rm -rf "$CHECKDIR"' EXIT
TRUSTEDDIR="$CHECKDIR/trusted"
PROBLEMDIR="$CHECKDIR/problem"
GOALDIR="$CHECKDIR/goal"
mkdir -p "$TRUSTEDDIR" "$PROBLEMDIR/tmp" "$GOALDIR/tmp"

if ! command -v rocq >/dev/null 2>&1; then
  if [[ -n "${LOGOS_ROCQ_OPAM_SWITCH:-}" ]]; then
    export PATH="$LOGOS_ROCQ_OPAM_SWITCH/_opam/bin:$PATH"
    export ROCQLIB="${ROCQLIB:-$LOGOS_ROCQ_OPAM_SWITCH/_opam/lib/coq}"
    export COQLIB="${COQLIB:-$ROCQLIB}"
    export OCAMLFIND_CONF="${OCAMLFIND_CONF:-$LOGOS_ROCQ_OPAM_SWITCH/_opam/lib/findlib.conf}"
  fi
fi

command -v rocq >/dev/null 2>&1 || {
  echo "rocq not found. Put rocq in PATH or set LOGOS_ROCQ_OPAM_SWITCH." >&2
  exit 127
}
if [[ "${LOGOS_UNTRUSTED_AGENT_CHECK:-0}" != "1" ]]; then
  command -v bwrap >/dev/null 2>&1 || {
    echo "bubblewrap (bwrap) is required to isolate untrusted Rocq compilation." >&2
    exit 127
  }
fi

# The ordered Logos entries are exhaustively checked against the structured
# Rust trusted-theory registry by the proof-stage unit tests.
for file in \
  "$LOGOS_REPO_ROOT/vendor/FormalSQL/src/data/proof_of_concept/SqlSyntax.vo" \
  "$LOGOS_REPO_ROOT/vendor/FormalSQL/src/data/proof_of_concept/GenericInstance.vo" \
  "$LOGOS_REPO_ROOT/vendor/FormalSQL/src/data/proof_of_concept/SchemaConstraints.vo" \
  "$LOGOS_REPO_ROOT/vendor/FormalSQL/src/data/sql/SqlAlgebra.vo" \
  "$LOGOS_REPO_ROOT/vendor/FormalSQL/src/data/sql/SqlOutcome.vo" \
  "$LOGOS_REPO_ROOT/vendor/FormalSQL/src/data/sql/SqlErrorSemantics.vo" \
  "$LOGOS_REPO_ROOT/vendor/FormalSQL/src/data/sql/SqlOrder.vo" \
  "$LOGOS_REPO_ROOT/vendor/FormalSQL/src/data/sql/SqlListFacts.vo" \
  "$LOGOS_REPO_ROOT/vendor/FormalSQL/src/data/sql/SqlQuerySyntax.vo" \
  "$LOGOS_REPO_ROOT/vendor/FormalSQL/src/data/sql/SqlQuerySemantics.vo" \
  "$LOGOS_REPO_ROOT/vendor/FormalSQL/src/data/sql/SqlBagAbstraction.vo" \
  "$LOGOS_REPO_ROOT/vendor/FormalSQL/src/data/sql/SqlQueryFacts.vo" \
  "$LOGOS_REPO_ROOT/vendor/FormalSQL/src/data/sql/SqlQueryContexts.vo" \
  "$LOGOS_REPO_ROOT/vendor/FormalSQL/src/data/sql/SqlQueryWellFormed.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/TNullSyntax.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/VerificationConditions.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/SchemaCardinality.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/QueryCardinality.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/QueryTNullSyntax.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/ErrorFacts.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/NumericFacts.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/BitwiseFacts.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/RewriteSpec.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/OccFacts.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/PiFacts.vo"; do
  if [[ ! -s "$file" ]]; then
    echo "missing or empty trusted Rocq object: $file" >&2
    echo "run 'make logos-formal-sql-lemmas' in LOGOS_REPO_ROOT before proof checking" >&2
    exit 2
  fi
done

cp "$WORKDIR/Schema.v" "$WORKDIR/Queries.v" "$TRUSTEDDIR/"
cp "$WORKDIR/Problem.v" "$PROBLEMDIR/"

rocq compile \
  -Q "$LOGOS_REPO_ROOT/vendor/FormalSQL/src" SQLFS \
  -Q "$LOGOS_REPO_ROOT/theories" Logos \
  -Q "$TRUSTEDDIR" LogosGenerated \
  "$TRUSTEDDIR/Schema.v"

rocq compile \
  -Q "$LOGOS_REPO_ROOT/vendor/FormalSQL/src" SQLFS \
  -Q "$LOGOS_REPO_ROOT/theories" Logos \
  -Q "$TRUSTEDDIR" LogosGenerated \
  "$TRUSTEDDIR/Queries.v"

cat > "$TRUSTEDDIR/TrustedBaseline.v" <<'EOF'
From SQLFS Require Import SqlSyntax GenericInstance Values SqlAlgebra SqlOutcome SqlErrorSemantics SqlListFacts SqlQuerySyntax SqlQuerySemantics SqlQueryWellFormed SqlBagAbstraction SqlQueryFacts SqlQueryContexts FiniteBag FiniteSet Bool3 SchemaConstraints.
From Logos Require Import FormalSQL.TNullSyntax FormalSQL.VerificationConditions FormalSQL.SchemaCardinality FormalSQL.QueryCardinality FormalSQL.QueryTNullSyntax FormalSQL.ErrorFacts FormalSQL.NumericFacts FormalSQL.BitwiseFacts FormalSQL.OccFacts FormalSQL.PiFacts FormalSQL.RewriteSpec.
From LogosGenerated Require Import Schema Queries.
From Stdlib Require Import String ZArith NArith List Lia.

Definition trusted_baseline_marker : Prop := True.
EOF

rocq compile \
  -Q "$LOGOS_REPO_ROOT/vendor/FormalSQL/src" SQLFS \
  -Q "$LOGOS_REPO_ROOT/theories" Logos \
  -Q "$TRUSTEDDIR" LogosGenerated \
  "$TRUSTEDDIR/TrustedBaseline.v"

# Problem.v is agent-controlled Rocq source. The in-container invocation is
# only a development check inside the already disposable agent container. The
# authoritative host invocation never receives this marker and always uses the
# bubblewrap filesystem boundary below.
cp "$TRUSTEDDIR/Schema.vo" "$TRUSTEDDIR/Queries.vo" "$PROBLEMDIR/"
if [[ "${LOGOS_UNTRUSTED_AGENT_CHECK:-0}" == "1" ]]; then
  (
    cd "$PROBLEMDIR"
    TMPDIR="$PROBLEMDIR/tmp" rocq compile \
      -Q "$LOGOS_REPO_ROOT/vendor/FormalSQL/src" SQLFS \
      -Q "$LOGOS_REPO_ROOT/theories" Logos \
      -Q "$PROBLEMDIR" LogosGenerated \
      "$PROBLEMDIR/Problem.v"
  )
else
  bwrap \
    --die-with-parent \
    --new-session \
    --unshare-net \
    --unshare-pid \
    --ro-bind / / \
    --dev /dev \
    --proc /proc \
    --bind "$PROBLEMDIR" "$PROBLEMDIR" \
    --chdir "$PROBLEMDIR" \
    --setenv TMPDIR "$PROBLEMDIR/tmp" \
    rocq compile \
      -Q "$LOGOS_REPO_ROOT/vendor/FormalSQL/src" SQLFS \
      -Q "$LOGOS_REPO_ROOT/theories" Logos \
      -Q "$PROBLEMDIR" LogosGenerated \
      "$PROBLEMDIR/Problem.v"
fi

# Goal.v is copied only after the untrusted compilation has exited.  Its fresh
# directory contains the original trusted dependencies and the kernel-checked
# Problem.vo, so writes inside Problem.v cannot replace the certificate source.
cp "$WORKDIR/Goal.v" "$GOALDIR/"
cp "$TRUSTEDDIR/Schema.vo" "$TRUSTEDDIR/Queries.vo" "$PROBLEMDIR/Problem.vo" "$GOALDIR/"
rocq compile \
  -Q "$LOGOS_REPO_ROOT/vendor/FormalSQL/src" SQLFS \
  -Q "$LOGOS_REPO_ROOT/theories" Logos \
  -Q "$GOALDIR" LogosGenerated \
  "$GOALDIR/Goal.v"

# Recheck the complete generated dependency closure independently of the
# interactive compiler process, and retain its assumption summary for policy
# checks below.  Trusted dependencies use a small number of foundational Rocq
# axioms, but generated modules must never add their own assumptions.
CHECK_CONTEXT="$CHECKDIR/rocq-check-context.txt"
BASELINE_CONTEXT="$CHECKDIR/rocq-check-baseline-context.txt"
rocq check -silent -o \
  -Q "$LOGOS_REPO_ROOT/vendor/FormalSQL/src" SQLFS \
  -Q "$LOGOS_REPO_ROOT/theories" Logos \
  -Q "$TRUSTEDDIR" LogosGenerated \
  LogosGenerated.TrustedBaseline >"$BASELINE_CONTEXT" 2>&1
rocq check -silent -o \
  -Q "$LOGOS_REPO_ROOT/vendor/FormalSQL/src" SQLFS \
  -Q "$LOGOS_REPO_ROOT/theories" Logos \
  -Q "$GOALDIR" LogosGenerated \
  LogosGenerated.Goal 2>&1 | tee "$CHECK_CONTEXT"

if grep -Eq '^[[:space:]]+LogosGenerated\.' "$CHECK_CONTEXT"; then
  echo "generated proof depends on an untrusted axiom" >&2
  exit 3
fi

extract_axioms() {
  awk '
    /^\* Axioms:/ { in_axioms = 1; next }
    /^\* Constants\/Inductives/ { in_axioms = 0 }
    in_axioms && NF == 1 { print $1 }
  ' "$1" | LC_ALL=C sort -u
}

extract_axioms "$BASELINE_CONTEXT" > "$CHECKDIR/baseline-axioms.txt"
extract_axioms "$CHECK_CONTEXT" > "$CHECKDIR/generated-axioms.txt"
comm -13 \
  "$CHECKDIR/baseline-axioms.txt" \
  "$CHECKDIR/generated-axioms.txt" \
  > "$CHECKDIR/untrusted-axioms.txt"
if [[ -s "$CHECKDIR/untrusted-axioms.txt" ]]; then
  echo "generated proof introduced assumptions outside the trusted baseline:" >&2
  cat "$CHECKDIR/untrusted-axioms.txt" >&2
  exit 3
fi

for required in \
  '* Theory: Set is predicative' \
  '* Theory: Rewrite rules are not allowed' \
  '* Constants/Inductives relying on type-in-type: <none>' \
  '* Constants/Inductives relying on unsafe (co)fixpoints: <none>' \
  '* Inductives whose positivity is assumed: <none>'; do
  if ! grep -Fq -- "$required" "$CHECK_CONTEXT"; then
    echo "generated proof uses an unsafe Rocq kernel setting: $required" >&2
    exit 3
  fi
done
