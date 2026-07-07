#!/usr/bin/env bash
set -euo pipefail

: "${LOGOS_REPO_ROOT:?set LOGOS_REPO_ROOT to the Logos repository root}"
: "${LOGOS_SOLVER_IMAGE:=logos-solver:latest}"
: "${LOGOS_PROOF_AGENT_COMMAND:?set LOGOS_PROOF_AGENT_COMMAND inside the container}"
: "${LOGOS_PROOF_AGENT_TIMEOUT:=900}"

WORKDIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

CODEX_HOME_HOST="${LOGOS_SOLVER_CODEX_HOME:-${CODEX_HOME:-$HOME/.codex}}"
CODEX_HOME_STAGE="$WORKDIR/.codex-home"
HOST_UID="$(id -u)"
HOST_GID="$(id -g)"

stage_codex_home() {
  local src="$1"
  local dst="$2"
  [[ -d "$src" ]] || return 1
  mkdir -p "$dst"
  for name in config.toml auth.json credentials.json; do
    if [[ -f "$src/$name" ]]; then
      install -m 600 "$src/$name" "$dst/$name"
    fi
  done
}

docker_args=(
  --rm
  --network host
  --user "$HOST_UID:$HOST_GID"
  -e LOGOS_REPO_ROOT=/workspace/logos
  -e LOGOS_PROOF_AGENT_COMMAND="$LOGOS_PROOF_AGENT_COMMAND"
  -e LOGOS_PROOF_AGENT_TIMEOUT="$LOGOS_PROOF_AGENT_TIMEOUT"
  -e HOME=/workspace/problem
  -v "$LOGOS_REPO_ROOT":/workspace/logos:ro
  -v "$WORKDIR":/workspace/problem:rw
  -v "$WORKDIR/Schema.v":/workspace/problem/Schema.v:ro
  -v "$WORKDIR/Queries.v":/workspace/problem/Queries.v:ro
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

docker run "${docker_args[@]}" \
  "$LOGOS_SOLVER_IMAGE" \
  bash -lc 'cd /workspace/problem && timeout "$LOGOS_PROOF_AGENT_TIMEOUT" bash -lc "$LOGOS_PROOF_AGENT_COMMAND"'
