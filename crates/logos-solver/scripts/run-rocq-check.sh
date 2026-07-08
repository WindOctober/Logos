#!/usr/bin/env bash
set -euo pipefail

: "${LOGOS_REPO_ROOT:?set LOGOS_REPO_ROOT to the Logos repository root}"

WORKDIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

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

for file in \
  "$LOGOS_REPO_ROOT/vendor/FormalSQL/src/data/proof_of_concept/SqlSyntax.vo" \
  "$LOGOS_REPO_ROOT/vendor/FormalSQL/src/data/proof_of_concept/GenericInstance.vo" \
  "$LOGOS_REPO_ROOT/vendor/FormalSQL/src/data/sql/SqlAlgebra.vo" \
  "$LOGOS_REPO_ROOT/vendor/FormalSQL/src/data/sql/SqlOrder.vo" \
  "$LOGOS_REPO_ROOT/vendor/FormalSQL/src/data/sql/SqlListAlgebra.vo" \
  "$LOGOS_REPO_ROOT/vendor/FormalSQL/src/data/sql/SqlListFacts.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/TNullSyntax.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/RewriteSpec.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/OccFacts.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/PiFacts.vo"; do
  if [[ ! -f "$file" ]]; then
    echo "missing trusted Rocq object: $file" >&2
    echo "run 'make logos-formal-sql-lemmas' in LOGOS_REPO_ROOT before proof checking" >&2
    exit 2
  fi
done

rm -f \
  "$WORKDIR"/Schema.glob "$WORKDIR"/Schema.vo "$WORKDIR"/Schema.vok "$WORKDIR"/Schema.vos "$WORKDIR"/.Schema.aux \
  "$WORKDIR"/Queries.glob "$WORKDIR"/Queries.vo "$WORKDIR"/Queries.vok "$WORKDIR"/Queries.vos "$WORKDIR"/.Queries.aux \
  "$WORKDIR"/Problem.glob "$WORKDIR"/Problem.vo "$WORKDIR"/Problem.vok "$WORKDIR"/Problem.vos "$WORKDIR"/.Problem.aux \
  "$WORKDIR"/.lia.cache

rocq compile \
  -Q "$LOGOS_REPO_ROOT/vendor/FormalSQL/src" SQLFS \
  -Q "$LOGOS_REPO_ROOT/theories" Logos \
  -Q "$WORKDIR" LogosGenerated \
  "$WORKDIR/Schema.v"

rocq compile \
  -Q "$LOGOS_REPO_ROOT/vendor/FormalSQL/src" SQLFS \
  -Q "$LOGOS_REPO_ROOT/theories" Logos \
  -Q "$WORKDIR" LogosGenerated \
  "$WORKDIR/Queries.v"

rocq compile \
  -Q "$LOGOS_REPO_ROOT/vendor/FormalSQL/src" SQLFS \
  -Q "$LOGOS_REPO_ROOT/theories" Logos \
  -Q "$WORKDIR" LogosGenerated \
  "$WORKDIR/Problem.v"
