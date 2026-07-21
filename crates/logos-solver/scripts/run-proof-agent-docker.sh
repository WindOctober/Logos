#!/usr/bin/env bash
set -euo pipefail

: "${LOGOS_REPO_ROOT:?set LOGOS_REPO_ROOT to the Logos repository root}"
: "${LOGOS_SOLVER_IMAGE:=logos-solver:latest}"
: "${LOGOS_PROOF_AGENT_COMMAND:?set LOGOS_PROOF_AGENT_COMMAND inside the container}"
: "${LOGOS_PROOF_AGENT_CODEX_HOME:?set a persistent per-case Codex home}"
: "${LOGOS_PROOF_AGENT_TIMEOUT:=3600}"
: "${LOGOS_PROOF_AGENT_MEMORY_LIMIT:=6g}"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
if [[ -n "${LOGOS_PROOF_WORKDIR:-}" ]]; then
  WORKDIR="$(cd "$LOGOS_PROOF_WORKDIR" && pwd)"
elif [[ -d "$SCRIPT_DIR/../../formal-sql" ]]; then
  WORKDIR="$(cd "$SCRIPT_DIR/../../formal-sql" && pwd)"
else
  echo "set LOGOS_PROOF_WORKDIR to the generated formal-sql workspace" >&2
  exit 2
fi

LAUNCHER="$(realpath "${BASH_SOURCE[0]}")"
case "$LAUNCHER" in
  "$WORKDIR"|"$WORKDIR"/*)
    echo "refusing to execute a proof-agent launcher from the writable problem workspace" >&2
    exit 2
    ;;
esac

AGENT_STAGE="$(mktemp -d "${TMPDIR:-/tmp}/logos-proof-agent.XXXXXX")"
CONTAINER_CID_FILE="${AGENT_STAGE}.container.cid"

cleanup() {
  if [[ -s "$CONTAINER_CID_FILE" ]]; then
    docker rm -f "$(cat "$CONTAINER_CID_FILE")" >/dev/null 2>&1 || true
  fi
  rm -f "$CONTAINER_CID_FILE"
  rm -rf "$AGENT_STAGE"
}

trap cleanup EXIT
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM
cp "$WORKDIR/Problem.v" "$AGENT_STAGE/Problem.v"

CODEX_HOME_HOST="${LOGOS_SOLVER_CODEX_HOME:-${CODEX_HOME:-$HOME/.codex}}"
if [[ -L "$LOGOS_PROOF_AGENT_CODEX_HOME" ]]; then
  echo "refusing a symlinked proof-agent Codex home" >&2
  exit 2
fi
mkdir -p "$LOGOS_PROOF_AGENT_CODEX_HOME"
chmod 700 "$LOGOS_PROOF_AGENT_CODEX_HOME"
CODEX_HOME_STAGE="$(cd "$LOGOS_PROOF_AGENT_CODEX_HOME" && pwd)"
HOST_UID="$(id -u)"
HOST_GID="$(id -g)"

stage_codex_home() {
  local src="$1"
  local dst="$2"
  [[ -d "$src" ]] || return 1
  mkdir -p "$dst"
  for name in config.toml auth.json credentials.json; do
    rm -f "$dst/$name"
    if [[ -f "$src/$name" ]]; then
      install -m 600 "$src/$name" "$dst/$name"
    fi
  done
}

docker_args=(
  --rm
  --cidfile "$CONTAINER_CID_FILE"
  --network host
  --memory "$LOGOS_PROOF_AGENT_MEMORY_LIMIT"
  --memory-swap "$LOGOS_PROOF_AGENT_MEMORY_LIMIT"
  --user "$HOST_UID:$HOST_GID"
  -e LOGOS_REPO_ROOT=/workspace/logos
  -e LOGOS_PROOF_AGENT_COMMAND="$LOGOS_PROOF_AGENT_COMMAND"
  -e LOGOS_PROOF_AGENT_TIMEOUT="$LOGOS_PROOF_AGENT_TIMEOUT"
  -e LOGOS_UNTRUSTED_AGENT_CHECK=1
  -e HOME=/workspace/problem
  -v "$LOGOS_REPO_ROOT":/workspace/logos:ro
  -v "$AGENT_STAGE":/workspace/problem:rw
  -v "$WORKDIR/Schema.v":/workspace/problem/Schema.v:ro
  -v "$WORKDIR/Queries.v":/workspace/problem/Queries.v:ro
  -v "$WORKDIR/Goal.v":/workspace/problem/Goal.v:ro
  -v "$WORKDIR/proof-agent-prompt.md":/workspace/problem/proof-agent-prompt.md:ro
  -v "$WORKDIR/lemma-guide.md":/workspace/problem/lemma-guide.md:ro
  -v "$WORKDIR/run-rocq-check.sh":/workspace/problem/run-rocq-check.sh:ro
)

if stage_codex_home "$CODEX_HOME_HOST" "$CODEX_HOME_STAGE"; then
  docker_args+=(
    -e CODEX_HOME=/codex-home
    -v "$CODEX_HOME_STAGE":/codex-home:rw
  )
fi

for env_name in OPENAI_API_KEY CODEX_API_KEY OPENAI_BASE_URL CODEX_BASE_URL; do
  if [[ -n "${!env_name:-}" ]]; then
    docker_args+=(-e "$env_name=${!env_name}")
  fi
done

if [[ -n "${LOGOS_ROCQ_OPAM_SWITCH:-}" ]]; then
  docker_args+=(
    -e LOGOS_ROCQ_OPAM_SWITCH=/workspace/rocq-opam
    -v "$LOGOS_ROCQ_OPAM_SWITCH":/workspace/rocq-opam:ro
  )
fi

# The trusted Rocq check runs on a host-created snapshot after this container
# exits.  The agent sees a disposable staging directory; only Problem.v is
# copied back into the generated workspace.
set +e
docker run "${docker_args[@]}" \
  "$LOGOS_SOLVER_IMAGE" \
  bash -lc 'cd /workspace/problem && timeout "$LOGOS_PROOF_AGENT_TIMEOUT" bash -lc "$LOGOS_PROOF_AGENT_COMMAND"'
status=$?
set -e

if [[ -f "$AGENT_STAGE/Problem.v" ]]; then
  cp "$AGENT_STAGE/Problem.v" "$WORKDIR/Problem.v"
fi
if [[ -f "$AGENT_STAGE/counterexample-handoff.json" ]]; then
  cp "$AGENT_STAGE/counterexample-handoff.json" "$WORKDIR/counterexample-handoff.json"
fi
exit "$status"
