#!/usr/bin/env bash
set -euo pipefail

: "${LOGOS_REPO_ROOT:?set LOGOS_REPO_ROOT to the Logos repository root}"
: "${LOGOS_SOLVER_IMAGE:=logos-solver:latest}"
: "${LOGOS_PROOF_AGENT_COMMAND:?set LOGOS_PROOF_AGENT_COMMAND inside the container}"
: "${LOGOS_PROOF_AGENT_CODEX_HOME:?set the isolated generation Codex home}"
: "${LOGOS_PROOF_AGENT_STAGE:?set the host-created proof-agent stage}"
: "${LOGOS_PROOF_DIAGNOSTIC_SOCKET:?set the host diagnostic broker socket path}"
: "${LOGOS_PROOF_DIAGNOSTIC_NONCE:?set the host diagnostic broker nonce}"
: "${LOGOS_PROOF_WORKDIR:?set LOGOS_PROOF_WORKDIR to the generated formal-sql workspace}"
: "${LOGOS_PROOF_AGENT_TIMEOUT:=3600}"
: "${LOGOS_PROOF_AGENT_MEMORY_LIMIT:=6g}"
: "${LOGOS_PROOF_AGENT_STORAGE_LIMIT_BYTES:=2147483648}"

LOGOS_REPO_ROOT="$(cd "$LOGOS_REPO_ROOT" && pwd)"

# Old checker-mode variables must never cross the agent boundary.  The only
# supported interaction is the bounded host diagnostic broker client.
unset LOGOS_UNTRUSTED_AGENT_CHECK
unset LOGOS_ROCQ_CHECK_DIAGNOSTIC_CHILD
unset LOGOS_ROCQ_CHECK_TIMEOUT_SECONDS
unset LOGOS_TRUSTED_ENVIRONMENT_PREFLIGHT
unset LOGOS_TRUSTED_ROCQ_CHECK_MODE
unset LOGOS_HOST_DIAGNOSTIC_CHECK

case "$LOGOS_PROOF_AGENT_TIMEOUT" in
  ''|*[!0-9]*)
    echo "LOGOS_PROOF_AGENT_TIMEOUT must be a positive integer number of seconds" >&2
    exit 2
    ;;
esac
if ((LOGOS_PROOF_AGENT_TIMEOUT < 1)); then
  echo "LOGOS_PROOF_AGENT_TIMEOUT must be at least one second" >&2
  exit 2
fi
case "$LOGOS_PROOF_AGENT_STORAGE_LIMIT_BYTES" in
  ''|*[!0-9]*)
    echo "LOGOS_PROOF_AGENT_STORAGE_LIMIT_BYTES must be a positive integer number of bytes" >&2
    exit 2
    ;;
esac
if ((LOGOS_PROOF_AGENT_STORAGE_LIMIT_BYTES <= 4096)); then
  echo "LOGOS_PROOF_AGENT_STORAGE_LIMIT_BYTES must exceed 4096 bytes" >&2
  exit 2
fi
# Docker always supplies /dev/shm as a separate writable tmpfs. Keep it at one
# page and subtract that page from the single workspace tmpfs so the sum of all
# writable filesystems exposed to the untrusted process is exactly the recorded
# aggregate quota.
WORKSPACE_STORAGE_LIMIT_BYTES=$((LOGOS_PROOF_AGENT_STORAGE_LIMIT_BYTES - 4096))
# The archive handoff is a host bind rather than part of /workspace. Bound its
# physical size and its extracted filesystem-object count by the same aggregate
# quota so metadata-only output cannot bypass the container storage policy.
HANDOFF_FILE_LIMIT_KIB=$(((LOGOS_PROOF_AGENT_STORAGE_LIMIT_BYTES + 1023) / 1024))
HANDOFF_MEMBER_LIMIT=$((LOGOS_PROOF_AGENT_STORAGE_LIMIT_BYTES / 4096))

WORKDIR="$(cd "$LOGOS_PROOF_WORKDIR" && pwd)"

LAUNCHER="$(realpath "${BASH_SOURCE[0]}")"
case "$LAUNCHER" in
  "$WORKDIR"|"$WORKDIR"/*)
    echo "refusing to execute a proof-agent launcher from the writable problem workspace" >&2
    exit 2
    ;;
esac

for command_name in docker find id install python3 sha256sum sort stat tar; do
  command -v "$command_name" >/dev/null 2>&1 || {
    echo "required proof-agent launcher command is unavailable: $command_name" >&2
    exit 2
  }
done

if [[ -L "$LOGOS_PROOF_AGENT_STAGE" || ! -d "$LOGOS_PROOF_AGENT_STAGE" ]]; then
  echo "proof-agent stage must be an existing non-symlink directory" >&2
  exit 2
fi
AGENT_STAGE="$(cd "$LOGOS_PROOF_AGENT_STAGE" && pwd)"
chmod 700 "$AGENT_STAGE"
DIAGNOSTIC_SOCKET="$LOGOS_PROOF_DIAGNOSTIC_SOCKET"
if [[ "$DIAGNOSTIC_SOCKET" != /* ]]; then
  echo "host diagnostic broker socket path must be absolute" >&2
  exit 2
fi
if [[ ! -S "$DIAGNOSTIC_SOCKET" || -L "$DIAGNOSTIC_SOCKET" ]]; then
  echo "host diagnostic broker socket is missing or invalid" >&2
  exit 2
fi
DIAGNOSTIC_SOCKET_DIR="$(dirname "$DIAGNOSTIC_SOCKET")"
if [[ "$(basename "$DIAGNOSTIC_SOCKET")" != socket || \
      -L "$DIAGNOSTIC_SOCKET_DIR" || ! -d "$DIAGNOSTIC_SOCKET_DIR" ]]; then
  echo "host diagnostic broker must be the socket entry of a real private directory" >&2
  exit 2
fi
if [[ ! "$(basename "$DIAGNOSTIC_SOCKET_DIR")" =~ ^logos-pds-[0-9]+-[A-Za-z0-9._-]+$ ]]; then
  echo "host diagnostic broker directory has an invalid name" >&2
  exit 2
fi
if [[ "$(stat -c '%a' "$DIAGNOSTIC_SOCKET_DIR")" != 700 || \
      "$(stat -c '%u' "$DIAGNOSTIC_SOCKET_DIR")" != "$(id -u)" ]]; then
  echo "host diagnostic broker directory must be mode 0700 and owned by the launcher user" >&2
  exit 2
fi
if [[ -n "$(find "$DIAGNOSTIC_SOCKET_DIR" -mindepth 1 -maxdepth 1 ! -name socket -print -quit)" ]]; then
  echo "host diagnostic broker directory contains an unexpected entry" >&2
  exit 2
fi
case "$LOGOS_PROOF_DIAGNOSTIC_NONCE" in
  ''|*[!0-9a-f]*)
    echo "host diagnostic broker nonce must be lowercase hexadecimal" >&2
    exit 2
    ;;
esac
if [[ "${#LOGOS_PROOF_DIAGNOSTIC_NONCE}" -ne 64 ]]; then
  echo "host diagnostic broker nonce must contain 64 hexadecimal characters" >&2
  exit 2
fi
AGENT_STAGE_PARENT="$(dirname "$AGENT_STAGE")"
AGENT_STAGE_BASENAME="$(basename "$AGENT_STAGE")"
if [[ -L "$AGENT_STAGE_PARENT" || ! -d "$AGENT_STAGE_PARENT" ]]; then
  echo "proof-agent stage parent must be an existing non-symlink directory" >&2
  exit 2
fi

# Keep every host-only staging artifact beside the host-created round stage.
# This makes its storage lifetime and filesystem placement part of the case
# artifact tree instead of silently spilling large proof state into /tmp.
HOST_STAGE_PREFIX="$AGENT_STAGE_PARENT/.${AGENT_STAGE_BASENAME}"
AUTHORITY_STAGE=""
EXPORT_STAGE=""
HANDOFF_STAGE=""
HANDOFF_INCOMING=""
HANDOFF_ARCHIVE=""
DOCKER_STDOUT=""
DOCKER_STDERR=""
CONTAINER_CID_FILE="${HOST_STAGE_PREFIX}.container.cid"
CONTAINER_IDENTITY_FILE="${HOST_STAGE_PREFIX}.container.identity.json"
read -r CONTAINER_CLEANUP_TOKEN _ < <(
  printf '%s\n%s\n' "$CONTAINER_CID_FILE" "$LOGOS_PROOF_DIAGNOSTIC_NONCE" | sha256sum
)
CONTAINER_NAME="logos-proof-${CONTAINER_CLEANUP_TOKEN}"
CONTAINER_MANAGED_LABEL="org.logos.proof-agent.managed"
CONTAINER_TOKEN_LABEL="org.logos.proof-agent.cleanup-token"

cleanup() {
  local saved_status="$?"
  local container_id="" removal_diagnostic="" inspect_diagnostic=""
  local actual_id="" actual_name="" actual_managed="" actual_token="" extra=""
  local container_reclaimed=false
  if [[ -n "$CONTAINER_IDENTITY_FILE" && -f "$CONTAINER_IDENTITY_FILE" && \
        ! -L "$CONTAINER_IDENTITY_FILE" ]]; then
    if inspect_diagnostic="$(docker inspect --format \
        '{{printf "%s|%s|%s|%s" .Id .Name (index .Config.Labels "org.logos.proof-agent.managed") (index .Config.Labels "org.logos.proof-agent.cleanup-token")}}' \
        "$CONTAINER_NAME" 2>&1)"; then
      IFS='|' read -r actual_id actual_name actual_managed actual_token extra \
        <<<"$inspect_diagnostic"
      if [[ -n "$extra" || ! "$actual_id" =~ ^[0-9a-f]{64}$ || \
            "$actual_name" != "/$CONTAINER_NAME" || \
            "$actual_managed" != true || \
            "$actual_token" != "$CONTAINER_CLEANUP_TOKEN" ]]; then
        echo "warning: preserving proof-agent container with mismatched management identity: $inspect_diagnostic" >&2
      elif [[ -s "$CONTAINER_CID_FILE" ]] && \
           { ! container_id="$(cat "$CONTAINER_CID_FILE")" || \
             [[ "$container_id" != "$actual_id" ]]; }; then
        echo "warning: preserving proof-agent container whose cidfile disagrees with its managed identity" >&2
      elif removal_diagnostic="$(docker rm -f "$actual_id" 2>&1)"; then
        container_reclaimed=true
      elif [[ "$removal_diagnostic" == *"No such container"* ]]; then
        container_reclaimed=true
      else
        echo "warning: preserving proof-agent container after Docker cleanup failure for $actual_id: $removal_diagnostic" >&2
      fi
    elif [[ "$inspect_diagnostic" == *"No such object"* || \
            "$inspect_diagnostic" == *"No such container"* ]]; then
      if [[ -e "$CONTAINER_CID_FILE" && ! -s "$CONTAINER_CID_FILE" ]]; then
        # Docker creates an empty --cidfile before ContainerCreate and writes
        # the ID only after the daemon response.  A killed client can therefore
        # leave an in-flight create that is not visible to the first inspect.
        # Preserve the durable identity for the outer bounded retry.
        echo "warning: preserving empty proof-agent cidfile until managed-name creation quiesces" >&2
      else
        container_reclaimed=true
      fi
    else
      echo "warning: preserving proof-agent container identity after Docker inspect failure: $inspect_diagnostic" >&2
    fi
  elif [[ -n "$CONTAINER_CID_FILE" && \
          ( -e "$CONTAINER_CID_FILE" || -L "$CONTAINER_CID_FILE" ) ]]; then
    # A bare cidfile is not management authority: stale or corrupted case
    # state could name an unrelated container.  Current launch ordering writes
    # the name/token/label identity before Docker can create the cidfile and
    # removes the cidfile before that identity, so preserving this anomaly is
    # both fail closed and compatible with every reachable crash state.
    echo "warning: preserving proof-agent cidfile without managed identity; refusing Docker cleanup" >&2
  fi
  if [[ "$container_reclaimed" == true ]]; then
    rm -f -- "$CONTAINER_CID_FILE"
    [[ -z "$CONTAINER_IDENTITY_FILE" ]] || rm -f -- "$CONTAINER_IDENTITY_FILE"
  fi
  [[ -z "$AUTHORITY_STAGE" ]] || rm -rf -- "$AUTHORITY_STAGE"
  [[ -z "$HANDOFF_STAGE" ]] || rm -rf -- "$HANDOFF_STAGE"
  [[ -z "$DOCKER_STDOUT" ]] || rm -f -- "$DOCKER_STDOUT"
  [[ -z "$DOCKER_STDERR" ]] || rm -f -- "$DOCKER_STDERR"
  [[ -z "$EXPORT_STAGE" ]] || rm -rf -- "$EXPORT_STAGE"
  return "$saved_status"
}

trap cleanup EXIT
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM

if [[ -e "$CONTAINER_CID_FILE" || -L "$CONTAINER_CID_FILE" || \
      -e "$CONTAINER_IDENTITY_FILE" || -L "$CONTAINER_IDENTITY_FILE" ]]; then
  echo "refusing pre-existing proof-agent container cid file" >&2
  exit 2
fi
python3 /dev/fd/3 \
  "$CONTAINER_IDENTITY_FILE" \
  "$(basename "$CONTAINER_CID_FILE")" \
  "$CONTAINER_NAME" \
  "$CONTAINER_CLEANUP_TOKEN" \
  "$CONTAINER_MANAGED_LABEL" \
  "$CONTAINER_TOKEN_LABEL" 3<<'PY'
import json
import os
import pathlib
import sys

path = pathlib.Path(sys.argv[1])
cid_file, name, token, managed_label, token_label = sys.argv[2:]
document = {
    "schemaVersion": 1,
    "cidFile": cid_file,
    "containerName": name,
    "cleanupToken": token,
    "labels": {managed_label: "true", token_label: token},
}
payload = (json.dumps(document, sort_keys=True, separators=(",", ":")) + "\n").encode()
pending = path.with_name(f".pending-{path.name}.{os.getpid()}")
descriptor = os.open(pending, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600)
try:
    with os.fdopen(descriptor, "wb") as output:
        output.write(payload)
        output.flush()
        os.fsync(output.fileno())
    os.link(pending, path, follow_symlinks=False)
    os.unlink(pending)
    directory = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
    try:
        os.fsync(directory)
    finally:
        os.close(directory)
finally:
    try:
        os.unlink(pending)
    except FileNotFoundError:
        pass
PY
AUTHORITY_STAGE="$(mktemp -d "${HOST_STAGE_PREFIX}.authority.XXXXXX")"
EXPORT_STAGE="$(mktemp -d "${HOST_STAGE_PREFIX}.export.XXXXXX")"
HANDOFF_STAGE="$(mktemp -d "${HOST_STAGE_PREFIX}.handoff.XXXXXX")"
chmod 700 "$HANDOFF_STAGE"
HANDOFF_INCOMING="$HANDOFF_STAGE/.agent-export.tar.incoming"
HANDOFF_ARCHIVE="$HANDOFF_STAGE/agent-export.tar"
install -m 600 /dev/null "$HANDOFF_INCOMING"
DOCKER_STDOUT="$(mktemp "${HOST_STAGE_PREFIX}.docker-stdout.XXXXXX")"
DOCKER_STDERR="$(mktemp "${HOST_STAGE_PREFIX}.docker-stderr.XXXXXX")"

publish_stage_file() {
  local source="$1"
  local destination="$2"
  local mode="$3"
  local destination_dir
  local destination_base
  local temporary
  [[ -f "$source" && ! -L "$source" ]] || {
    echo "refusing non-regular or symlinked agent output: $source" >&2
    return 1
  }
  destination_dir="$(dirname "$destination")"
  destination_base="$(basename "$destination")"
  temporary="$(mktemp "$destination_dir/.${destination_base}.tmp.XXXXXX")"
  install -m "$mode" "$source" "$temporary"
  mv -fT "$temporary" "$destination"
}

# Replace a live directory without ever exposing an absent or partially copied
# path. Both directories are host-created on the case-local filesystem, and
# Linux renameat2(RENAME_EXCHANGE) makes the swap one atomic namespace update:
# a signal or launcher crash therefore leaves either the complete old tree or
# the complete returned tree at the live path. The displaced tree remains in
# the export staging directory and is removed only by ordinary cleanup.
atomic_exchange_directories() {
  local returned="$1"
  local live="$2"
  for path in "$returned" "$live"; do
    [[ -d "$path" && ! -L "$path" ]] || {
      echo "refusing to exchange a non-directory or symlinked agent state path: $path" >&2
      return 1
    }
  done
  chmod 700 "$returned" "$live" || return 1
  python3 /dev/fd/3 "$returned" "$live" 3<<'PY'
import ctypes
import os
import pathlib
import sys

returned, live = (os.fsencode(value) for value in sys.argv[1:])
libc = ctypes.CDLL(None, use_errno=True)
renameat2 = getattr(libc, "renameat2", None)
if renameat2 is None:
    raise SystemExit("renameat2 is unavailable; refusing non-atomic state publication")
renameat2.argtypes = [
    ctypes.c_int,
    ctypes.c_char_p,
    ctypes.c_int,
    ctypes.c_char_p,
    ctypes.c_uint,
]
renameat2.restype = ctypes.c_int
AT_FDCWD = -100
RENAME_EXCHANGE = 2
if renameat2(AT_FDCWD, returned, AT_FDCWD, live, RENAME_EXCHANGE) != 0:
    error = ctypes.get_errno()
    raise OSError(error, os.strerror(error), os.fsdecode(live))

# Persist the namespace exchange at both parents. A failure here is
# fail-closed, but the live path already contains one complete directory.
for parent in {pathlib.Path(os.fsdecode(returned)).parent,
               pathlib.Path(os.fsdecode(live)).parent}:
    descriptor = os.open(parent, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
PY
}

publish_authority_closure() {
  local authority_closure="$AUTHORITY_STAGE/AUTHORITY-CLOSURE.txt"
  [[ -f "$authority_closure" && ! -L "$authority_closure" ]] || {
    echo "host-generated authority closure manifest is not a regular file" >&2
    return 1
  }
  publish_stage_file \
    "$authority_closure" \
    "$WORKDIR/authority-closure.txt" \
    600
}

for name in Problem.v Schema.v Queries.v Witness.v Goal.v source.sql target.sql query-shape.json ordered-signatures.json \
  observation-certificates.json semantic-primer.md search-rocq-declarations.py context-manifest.json \
  proof-agent-prompt.md run-rocq-check.sh; do
  [[ -f "$WORKDIR/$name" && ! -L "$WORKDIR/$name" ]] || {
    echo "required regular proof-agent context file is missing: $WORKDIR/$name" >&2
    exit 2
  }
done
if [[ -e "$WORKDIR/checker-request.json" || -L "$WORKDIR/checker-request.json" ]]; then
  echo "refusing to launch with a stale checker-request.json in the proof workspace" >&2
  exit 2
fi
if [[ ! -e "$WORKDIR/ProofModules" ]]; then
  mkdir -m 700 "$WORKDIR/ProofModules"
fi
if [[ -L "$WORKDIR/ProofModules" || ! -d "$WORKDIR/ProofModules" ]]; then
  echo "ProofModules must be a real directory" >&2
  exit 2
fi
while IFS= read -r -d '' path; do
  relative="${path#"$WORKDIR/ProofModules/"}"
  if [[ "$relative" == "$path" || "$relative" == */* || \
        ! "$relative" =~ ^[A-Z][A-Za-z0-9_]*\.v$ || \
        ! -f "$path" || -L "$path" ]]; then
    echo "invalid checked proof module in workspace: $path" >&2
    exit 2
  fi
done < <(find "$WORKDIR/ProofModules" -mindepth 1 -print0)
install -m 600 "$WORKDIR/Problem.v" "$AGENT_STAGE/Problem.v"
if [[ -L "$AGENT_STAGE/scratch" || ! -d "$AGENT_STAGE/scratch" ]]; then
  echo "host-created proof-agent scratch stage is missing or symlinked" >&2
  exit 2
fi

[[ ! -e "$WORKDIR/lemma-catalog" && ! -L "$WORKDIR/lemma-catalog" ]] || {
  echo "obsolete routed lemma catalog must not be present in the proof workspace" >&2
  exit 2
}

VENDOR_SOURCE_ROOT="$LOGOS_REPO_ROOT/vendor/FormalSQL/src"
LOGOS_SOURCE_ROOT="$LOGOS_REPO_ROOT/theories/FormalSQL"
for path in "$VENDOR_SOURCE_ROOT" "$LOGOS_SOURCE_ROOT"; do
  [[ -d "$path" && ! -L "$path" ]] || {
    echo "required proof-agent authority source tree is missing or symlinked: $path" >&2
    exit 2
  }
done

# Exact agent authority closure:
#   * every source-backed, non-Example .v/.vo pair below vendor/FormalSQL/src;
#   * every source-backed, non-Example .v/.vo pair directly in
#     theories/FormalSQL (no subdirectories).
# The source must be regular, the object must be regular/nonempty, and the
# object must not predate its source.  Source-less objects, .glob/.aux/.cache,
# build trees, Examples, catalogs, guides, and retained run artifacts are never
# admitted. LOGOS_REPO_ROOT is already the runner's immutable authority
# snapshot, so the exact tree is mounted read-only instead of copied for every
# agent round. AUTHORITY-CLOSURE.txt remains an independently recorded binding.
is_excluded_authority_source() {
  local relative="$1"
  local base="${relative##*/}"
  case "/$relative/" in
    */Examples/*|*/examples/*|*/catalog/*|*/build/*|*/_build/*|*/var/*)
      return 0
      ;;
  esac
  case "$base" in
    *Example.v|*Examples.v)
      return 0
      ;;
  esac
  return 1
}

authority_source_count=0
validate_source_object_pair() {
  local source="$1"
  local source_root="$2"
  local relative="${source#"$source_root"/}"
  local object="${source%.v}.vo"

  [[ "$relative" != "$source" && "$relative" != ../* && "$relative" != */../* ]] || {
    echo "authority source escaped its root: $source" >&2
    exit 2
  }
  [[ -f "$source" && ! -L "$source" ]] || {
    echo "authority source is not a regular non-symlink file: $source" >&2
    exit 2
  }
  [[ -s "$object" && ! -L "$object" ]] || {
    echo "authority source lacks a nonempty regular object: $source" >&2
    exit 2
  }
  if [[ "$source" -nt "$object" ]]; then
    echo "authority object predates its source; rebuild before launching: $object" >&2
    exit 2
  fi

  if [[ "$(stat -c '%a' "$source")" != 444 || "$(stat -c '%a' "$object")" != 444 ]]; then
    echo "authority source/object pair is not immutable: $source" >&2
    exit 2
  fi
  authority_source_count=$((authority_source_count + 1))
}

while IFS= read -r -d '' source; do
  relative="${source#"$VENDOR_SOURCE_ROOT"/}"
  if ! is_excluded_authority_source "$relative"; then
    validate_source_object_pair "$source" "$VENDOR_SOURCE_ROOT"
  fi
done < <(find "$VENDOR_SOURCE_ROOT" -type f -name '*.v' -print0 | LC_ALL=C sort -z)

while IFS= read -r -d '' source; do
  relative="${source#"$LOGOS_SOURCE_ROOT"/}"
  if ! is_excluded_authority_source "$relative"; then
    validate_source_object_pair "$source" "$LOGOS_SOURCE_ROOT"
  fi
done < <(find "$LOGOS_SOURCE_ROOT" -maxdepth 1 -type f -name '*.v' -print0 | LC_ALL=C sort -z)

if ((authority_source_count == 0)); then
  echo "the proof-agent authority closure is empty" >&2
  exit 2
fi

closure_tmp="$AUTHORITY_STAGE/.AUTHORITY-CLOSURE.txt.tmp"
{
  echo '# Logos proof-agent authority closure'
  echo '# schemaVersion: 1'
  echo '# policy: logos-proof-agent-source-object-closure-v1'
  printf '# sourcePairs: %s\n' "$authority_source_count"
  printf '# stagedFiles: %s\n' "$((authority_source_count * 2))"
  echo '# sha256  workspace-relative-path'
  echo '# Only source-backed non-Example .v/.vo pairs are present.'
  (
    cd "$LOGOS_REPO_ROOT"
    while IFS= read -r -d '' relative; do
      sha256sum "$relative"
    done < <(
      find vendor/FormalSQL/src theories/FormalSQL -type f \
        \( -name '*.v' -o -name '*.vo' \) -print0 | LC_ALL=C sort -z
    )
  )
} >"$closure_tmp"
mv -fT "$closure_tmp" "$AUTHORITY_STAGE/AUTHORITY-CLOSURE.txt"

# Publish the fresh, host-generated authority binding before starting the
# untrusted container. If the agent process is killed, the Rust host can still
# audit and record the unchanged Problem.v plus this exact source/object
# closure instead of misclassifying an interrupted search as a trusted
# environment failure. The same binding is atomically restored after Docker.
publish_authority_closure || exit 2

CODEX_HOME_HOST="${LOGOS_SOLVER_CODEX_HOME:-${CODEX_HOME:-$HOME/.codex}}"
CODEX_CONFIG_HOST="${LOGOS_SOLVER_CODEX_CONFIG:-$CODEX_HOME_HOST/config.toml}"
if [[ -L "$LOGOS_PROOF_AGENT_CODEX_HOME" ]]; then
  echo "refusing a symlinked proof-agent Codex home" >&2
  exit 2
fi
if [[ -n "${LOGOS_SOLVER_CODEX_CONFIG:-}" ]] && \
   [[ ! -f "$CODEX_CONFIG_HOST" || -L "$CODEX_CONFIG_HOST" ]]; then
  echo "configured frozen Codex config is missing, non-regular, or symlinked" >&2
  exit 2
fi
mkdir -p "$LOGOS_PROOF_AGENT_CODEX_HOME"
chmod 700 "$LOGOS_PROOF_AGENT_CODEX_HOME"
CODEX_HOME_STAGE="$(cd "$LOGOS_PROOF_AGENT_CODEX_HOME" && pwd)"
HOST_UID="$(id -u)"
HOST_GID="$(id -g)"
if ((HOST_UID == 0)); then
  echo "refusing to run the untrusted proof agent with uid 0" >&2
  exit 2
fi

stage_codex_home() {
  local src="$1"
  local dst="$2"
  local config="$3"
  local canonical_src
  [[ -d "$src" ]] || return 1
  canonical_src="$(cd "$src" && pwd)" || return 1
  [[ "$canonical_src" != "$dst" ]] || return 1
  mkdir -p "$dst" || return 1
  # These names cross the session boundary under host authority. An untrusted
  # prior round may have replaced one with a directory or symlink, so remove
  # the complete lexical entry before installing the frozen regular file.
  rm -rf -- "$dst/config.toml" "$dst/auth.json" "$dst/credentials.json" \
    || return 1
  if [[ -f "$config" && ! -L "$config" ]]; then
    install -m 600 "$config" "$dst/config.toml" || return 1
  fi
  for name in auth.json credentials.json; do
    if [[ -f "$src/$name" && ! -L "$src/$name" ]]; then
      install -m 600 "$src/$name" "$dst/$name" || return 1
    fi
  done
}

extract_agent_archive() {
  local archive="$1"
  local destination="$2"
  local logical_size_limit="$3"
  local member_limit="$4"
  python3 /dev/fd/3 \
    "$archive" "$destination" "$logical_size_limit" "$member_limit" 3<<'PY'
import os
import pathlib
import shutil
import sys
import tarfile

archive, destination, raw_logical_size_limit, raw_member_limit = sys.argv[1:]
logical_size_limit = int(raw_logical_size_limit)
member_limit = int(raw_member_limit)
root = pathlib.Path(destination)
allowed_roots = {"problem", "codex-home", "agent-stdout", "agent-stderr"}
seen = set()
logical_size = 0
member_count = 0

with tarfile.open(archive, mode="r:*") as bundle:
    for member in bundle:
        member_count += 1
        if member_count > member_limit:
            raise SystemExit(
                "proof-agent export exceeds its aggregate filesystem-object quota"
            )
        path = pathlib.PurePosixPath(member.name)
        parts = path.parts
        if (
            not parts
            or path.is_absolute()
            or any(part in ("", ".", "..") for part in parts)
            or parts[0] not in allowed_roots
        ):
            raise SystemExit(f"unsafe proof-agent export path: {member.name!r}")
        if parts[0] == "problem":
            allowed_problem_entry = (
                parts == ("problem",)
                or (len(parts) >= 2 and parts[1] == "scratch")
                or (
                    len(parts) == 2
                    and parts[1] in {"Problem.v", "counterexample-handoff.json"}
                )
            )
            if not allowed_problem_entry:
                raise SystemExit(
                    f"forbidden proof-agent problem export path: {member.name!r}"
                )
        normalized = path.as_posix()
        if normalized in seen:
            raise SystemExit(f"duplicate proof-agent export path: {normalized!r}")
        seen.add(normalized)
        target = root.joinpath(*parts)
        if member.isdir():
            target.mkdir(mode=0o700, parents=True, exist_ok=True)
            os.chmod(target, 0o700)
            continue
        if not member.isreg():
            raise SystemExit(f"non-regular proof-agent export entry: {normalized!r}")
        logical_size += member.size
        if logical_size > logical_size_limit:
            raise SystemExit(
                "proof-agent export exceeds its aggregate writable-storage quota"
            )
        target.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
        descriptor = os.open(
            target,
            os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
            0o600,
        )
        source = bundle.extractfile(member)
        if source is None:
            os.close(descriptor)
            raise SystemExit(f"cannot read proof-agent export entry: {normalized!r}")
        with source, os.fdopen(descriptor, "wb") as output:
            shutil.copyfileobj(source, output, length=1024 * 1024)
PY
}

docker_args=(
  --rm
  --cidfile "$CONTAINER_CID_FILE"
  --name "$CONTAINER_NAME"
  --label "$CONTAINER_MANAGED_LABEL=true"
  --label "$CONTAINER_TOKEN_LABEL=$CONTAINER_CLEANUP_TOKEN"
  --log-driver none
  --network host
  --read-only
  --memory "$LOGOS_PROOF_AGENT_MEMORY_LIMIT"
  --memory-swap "$LOGOS_PROOF_AGENT_MEMORY_LIMIT"
  --shm-size 4096
  --tmpfs "/workspace:rw,nosuid,nodev,size=$WORKSPACE_STORAGE_LIMIT_BYTES,mode=0755,uid=0,gid=0"
  -e LOGOS_REPO_ROOT=/workspace/logos
  -e LOGOS_PROOF_AGENT_COMMAND="$LOGOS_PROOF_AGENT_COMMAND"
  -e LOGOS_PROOF_AGENT_TIMEOUT="$LOGOS_PROOF_AGENT_TIMEOUT"
  -e LOGOS_PROOF_AGENT_STORAGE_LIMIT_BYTES="$LOGOS_PROOF_AGENT_STORAGE_LIMIT_BYTES"
  -e LOGOS_PROOF_AGENT_HANDOFF_FILE_LIMIT_KIB="$HANDOFF_FILE_LIMIT_KIB"
  -e LOGOS_PROOF_DIAGNOSTIC_SOCKET=/seed/diagnostic/socket
  -e LOGOS_PROOF_DIAGNOSTIC_NONCE="$LOGOS_PROOF_DIAGNOSTIC_NONCE"
  -e LOGOS_PROOF_AGENT_UID="$HOST_UID"
  -e LOGOS_PROOF_AGENT_GID="$HOST_GID"
  -e HOME=/workspace/home
  -e TMPDIR=/workspace/tmp
  -v "$LOGOS_REPO_ROOT":/workspace/logos:ro
  -v "$DIAGNOSTIC_SOCKET_DIR":/seed/diagnostic:ro
  -v "$AGENT_STAGE":/seed/problem:ro
  -v "$WORKDIR":/seed/context:ro
  -v "$HANDOFF_INCOMING":/handoff-export:rw
)

if [[ -d "$CODEX_HOME_HOST" ]]; then
  stage_codex_home "$CODEX_HOME_HOST" "$CODEX_HOME_STAGE" "$CODEX_CONFIG_HOST" || {
    echo "failed to stage the isolated proof-agent Codex home" >&2
    exit 2
  }
  docker_args+=(
    -e CODEX_HOME=/workspace/codex-home
    -v "$CODEX_HOME_STAGE":/seed/codex-home:ro
  )
fi

# Credentials may be supplied directly, but provider endpoints come only from
# the staged configuration.  Ambient base-URL variables would otherwise change
# the experimental provider without changing any recorded command or artifact.
for env_name in OPENAI_API_KEY CODEX_API_KEY; do
  if [[ -n "${!env_name:-}" ]]; then
    docker_args+=(-e "$env_name=${!env_name}")
  fi
done

# The container never receives the trusted checker, a Rocq switch, the mutable
# repository, or an agent-writable host bind. It receives only the runner's
# manifest-bound immutable authority snapshot. Its root is read-only and
# all mutable agent state (Problem.v, ProofModules, scratch, Codex state, HOME, TMPDIR, and
# captured output) shares one kernel-enforced tmpfs quota. Context and prior
# state enter through read-only seeds. The sole writable host mount is one
# pre-created regular handoff file: container root makes it root-only before
# dropping privileges, then fills it only after killing the untrusted uid.
# Diagnostic candidates are streamed to the host broker with their exact
# digest, so interactive checking also needs no agent-writable host mount.
CONTAINER_AGENT_SCRIPT="$(cat <<'INNER'
set -euo pipefail

[[ -f /handoff-export && ! -L /handoff-export ]] || {
  echo "proof-agent handoff mount is not a regular file" >&2
  exit 2
}
chown 0:0 /handoff-export

# Once container root has taken ownership, always return the bind-mounted file
# to the launcher user.  Preserve the original status: a failed export remains
# a failed export, while the host independently rejects an unowned or empty
# handoff if either best-effort restoration operation itself fails.
release_handoff_on_exit() {
  local saved_status="$?"
  trap - EXIT
  # An abnormal wrapper exit can occur while the untrusted command still has
  # descendants. Stop them before ownership changes so none can race to open
  # the handoff file after it becomes owned by their numeric uid again.
  pkill -STOP -u "$LOGOS_PROOF_AGENT_UID" >/dev/null 2>&1 || true
  pkill -KILL -u "$LOGOS_PROOF_AGENT_UID" >/dev/null 2>&1 || true
  chmod 0600 /handoff-export >/dev/null 2>&1 || true
  chown "$LOGOS_PROOF_AGENT_UID:$LOGOS_PROOF_AGENT_GID" \
    /handoff-export >/dev/null 2>&1 || true
  exit "$saved_status"
}
trap release_handoff_on_exit EXIT

chmod 0600 /handoff-export
: > /handoff-export

install -d -m 0755 /workspace/problem
install -d -m 0700 /workspace/home /workspace/tmp /workspace/codex-home
install -d -m 0700 /workspace/problem/ProofModules /workspace/problem/scratch
install -m 0600 /seed/problem/Problem.v /workspace/problem/Problem.v
: > /workspace/problem/counterexample-handoff.json

for name in Schema.v Queries.v Witness.v Goal.v source.sql target.sql query-shape.json \
  ordered-signatures.json observation-certificates.json semantic-primer.md \
  search-rocq-declarations.py context-manifest.json proof-agent-prompt.md run-rocq-check.sh; do
  ln -s "/seed/context/$name" "/workspace/problem/$name"
done

if [[ -d /seed/problem/scratch ]]; then
  cp -a /seed/problem/scratch/. /workspace/problem/scratch/
fi
if [[ -d /seed/context/ProofModules ]]; then
  cp -a /seed/context/ProofModules/. /workspace/problem/ProofModules/
fi
if [[ -d /seed/codex-home ]]; then
  cp -a /seed/codex-home/. /workspace/codex-home/
fi

chown -R "$LOGOS_PROOF_AGENT_UID:$LOGOS_PROOF_AGENT_GID" \
  /workspace/home /workspace/tmp /workspace/codex-home \
  /workspace/problem/ProofModules /workspace/problem/scratch
chown "$LOGOS_PROOF_AGENT_UID:$LOGOS_PROOF_AGENT_GID" \
  /workspace/problem/Problem.v /workspace/problem/counterexample-handoff.json

set +e
setpriv \
  --reuid="$LOGOS_PROOF_AGENT_UID" \
  --regid="$LOGOS_PROOF_AGENT_GID" \
  --clear-groups \
  --no-new-privs \
  --bounding-set=-all \
  --inh-caps=-all \
  --ambient-caps=-all \
  env \
    -u LOGOS_UNTRUSTED_AGENT_CHECK \
    -u LOGOS_ROCQ_CHECK_DIAGNOSTIC_CHILD \
    -u LOGOS_ROCQ_CHECK_TIMEOUT_SECONDS \
    -u LOGOS_TRUSTED_ENVIRONMENT_PREFLIGHT \
    -u LOGOS_TRUSTED_ROCQ_CHECK_MODE \
    -u LOGOS_HOST_DIAGNOSTIC_CHECK \
    bash -lc 'cd /workspace/problem && timeout --signal=TERM --kill-after=5s "${LOGOS_PROOF_AGENT_TIMEOUT}s" bash -lc "$LOGOS_PROOF_AGENT_COMMAND"' \
    > /workspace/agent-stdout \
    2> /workspace/agent-stderr
status=$?
set -e

# Stop and kill every process owned by the untrusted uid before exporting. A
# descendant that detached from timeout's process group must not race with the
# trusted root wrapper while it snapshots the workspace.
pkill -STOP -u "$LOGOS_PROOF_AGENT_UID" >/dev/null 2>&1 || true
pkill -KILL -u "$LOGOS_PROOF_AGENT_UID" >/dev/null 2>&1 || true

# Codex's execve/PATH compatibility layer is an invocation-local cache. Newer
# CLIs create helper symlinks below CODEX_HOME/tmp/arg0; those links are neither
# session state nor safe archive members. Discard the complete ephemeral tmp
# namespace only after every untrusted process has been killed. The host still
# rejects every non-regular entry anywhere else in the exported Codex home.
rm -rf -- /workspace/codex-home/tmp

(
  # Bash expresses RLIMIT_FSIZE in KiB. The host applies the exact byte check
  # below before parsing the archive, so rounding cannot expand acceptance.
  ulimit -f "$LOGOS_PROOF_AGENT_HANDOFF_FILE_LIMIT_KIB"
  tar --format=posix --sparse --warning=no-file-ignored --numeric-owner \
    -C /workspace -cf /handoff-export \
    problem/Problem.v \
    problem/counterexample-handoff.json \
    problem/scratch \
    codex-home \
    agent-stdout \
    agent-stderr
)
# ProofModules is intentionally absent from this archive. The untrusted
# container may create candidates there, but only a successful module-mode
# broker request can publish exact checked bytes into the host workspace.
exit "$status"
INNER
)"

set +e
docker run "${docker_args[@]}" \
  "$LOGOS_SOLVER_IMAGE" \
  bash -c "$CONTAINER_AGENT_SCRIPT" \
  >"$DOCKER_STDOUT" \
  2>"$DOCKER_STDERR"
status="$?"
set -e

if [[ ! -f "$HANDOFF_INCOMING" || -L "$HANDOFF_INCOMING" || \
      ! -s "$HANDOFF_INCOMING" || \
      "$(stat -c '%u' "$HANDOFF_INCOMING")" != "$HOST_UID" || \
      "$(stat -c '%g' "$HANDOFF_INCOMING")" != "$HOST_GID" || \
      "$(stat -c '%a' "$HANDOFF_INCOMING")" != 600 || \
      "$(stat -c '%s' "$HANDOFF_INCOMING")" -gt \
        "$LOGOS_PROOF_AGENT_STORAGE_LIMIT_BYTES" ]]; then
  [[ ! -s "$DOCKER_STDOUT" ]] || cat "$DOCKER_STDOUT" >&2
  cat "$DOCKER_STDERR" >&2
  echo "proof-agent container did not return a protected nonempty regular handoff file" >&2
  exit 2
fi
if [[ -e "$HANDOFF_ARCHIVE" || -L "$HANDOFF_ARCHIVE" ]]; then
  echo "refusing a pre-existing published proof-agent handoff archive" >&2
  exit 2
fi
mv -T "$HANDOFF_INCOMING" "$HANDOFF_ARCHIVE"

set +e
extract_agent_archive \
  "$HANDOFF_ARCHIVE" \
  "$EXPORT_STAGE" \
  "$LOGOS_PROOF_AGENT_STORAGE_LIMIT_BYTES" \
  "$HANDOFF_MEMBER_LIMIT"
extract_status="$?"
set -e
if ((extract_status != 0)); then
  [[ ! -s "$DOCKER_STDOUT" ]] || cat "$DOCKER_STDOUT" >&2
  cat "$DOCKER_STDERR" >&2
  echo "proof-agent container produced an unsafe or invalid export archive" >&2
  exit 2
fi

for path in \
  "$EXPORT_STAGE/problem/Problem.v" \
  "$EXPORT_STAGE/agent-stdout" \
  "$EXPORT_STAGE/agent-stderr"; do
  [[ -f "$path" && ! -L "$path" ]] || {
    echo "proof-agent export is missing required regular file: $path" >&2
    exit 2
  }
done
[[ -d "$EXPORT_STAGE/problem/scratch" && ! -L "$EXPORT_STAGE/problem/scratch" ]] || {
  echo "proof-agent export is missing a regular scratch directory" >&2
  exit 2
}
[[ -d "$EXPORT_STAGE/codex-home" && ! -L "$EXPORT_STAGE/codex-home" ]] || {
  echo "proof-agent export is missing a regular Codex home" >&2
  exit 2
}

publish_stage_file "$EXPORT_STAGE/problem/Problem.v" "$AGENT_STAGE/Problem.v" 600 || exit 2
atomic_exchange_directories \
  "$EXPORT_STAGE/problem/scratch" \
  "$AGENT_STAGE/scratch" || exit 2
# Publish the complete session home before exposing agent stdout containing a
# new or resumed session id. If a signal lands after this point, Rust can only
# observe session telemetry together with the matching durable home.
atomic_exchange_directories \
  "$EXPORT_STAGE/codex-home" \
  "$CODEX_HOME_STAGE" || exit 2
if [[ -s "$EXPORT_STAGE/problem/counterexample-handoff.json" ]]; then
  publish_stage_file \
    "$EXPORT_STAGE/problem/counterexample-handoff.json" \
    "$AGENT_STAGE/counterexample-handoff.json" \
    600 || exit 2
else
  rm -f "$AGENT_STAGE/counterexample-handoff.json"
fi

publish_authority_closure || exit 2

publish_stage_file "$AGENT_STAGE/Problem.v" "$WORKDIR/Problem.v" 600 || exit 2
if [[ -e "$AGENT_STAGE/counterexample-handoff.json" || -L "$AGENT_STAGE/counterexample-handoff.json" ]]; then
  publish_stage_file \
    "$AGENT_STAGE/counterexample-handoff.json" \
    "$WORKDIR/counterexample-handoff.json" \
    600 || exit 2
fi
if [[ -e "$AGENT_STAGE/checker-request.json" || -L "$AGENT_STAGE/checker-request.json" ]]; then
  echo "direct checker-request files are forbidden; use the host broker wrapper" >&2
  exit 2
fi

# Keep untrusted process output file-backed. In particular, do not `cat` these
# files through docker-run's stdout/stderr pipes: the Rust parent would then
# aggregate as much as the complete writable quota in `Command::output()`.
# Publish stdout, which contains the resumable session telemetry, last. Thus
# observing a session id implies that its home, scratch, Problem, handoff, and
# authority closure have all reached their durable host locations.
publish_stage_file "$EXPORT_STAGE/agent-stderr" "$AGENT_STAGE/agent-stderr" 600 || exit 2
if [[ -s "$DOCKER_STDERR" ]]; then
  cat "$DOCKER_STDERR" >>"$AGENT_STAGE/agent-stderr"
fi
if [[ -s "$DOCKER_STDOUT" ]]; then
  {
    echo
    echo '[docker launcher stdout]'
    cat "$DOCKER_STDOUT"
  } >>"$AGENT_STAGE/agent-stderr"
fi
publish_stage_file "$EXPORT_STAGE/agent-stdout" "$AGENT_STAGE/agent-stdout" 600 || exit 2

exit "$status"
