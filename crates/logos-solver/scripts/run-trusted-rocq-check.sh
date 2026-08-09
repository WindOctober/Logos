#!/usr/bin/env bash
set -euo pipefail

# Host-only trusted checker.  This file must never be copied or mounted into an
# agent workspace.  Legacy environment switches are explicitly neutralized so
# checker mode is selected only by the strict command-line interface below.
unset LOGOS_UNTRUSTED_AGENT_CHECK
unset LOGOS_ROCQ_CHECK_DIAGNOSTIC_CHILD
unset LOGOS_ROCQ_CHECK_TIMEOUT_SECONDS
unset LOGOS_TRUSTED_ENVIRONMENT_PREFLIGHT
unset LOGOS_TRUSTED_ROCQ_CHECK_MODE
unset LOGOS_HOST_DIAGNOSTIC_CHECK
unset ROCQPATH
unset COQPATH
unset ROCQFLAGS
unset COQFLAGS
unset ROCQRC
unset COQRC

usage() {
  cat >&2 <<'EOF'
usage: bash run-trusted-rocq-check.sh
       bash run-trusted-rocq-check.sh --problem-diagnostic --timeout-seconds <positive>
       bash run-trusted-rocq-check.sh --module-diagnostic --candidate ProofModules/Name.v --timeout-seconds <positive>
       bash run-trusted-rocq-check.sh --preflight
       bash run-trusted-rocq-check.sh --witness-preflight
EOF
}

mode=final
requested_timeout_seconds=
module_candidate=
case "$#" in
  0)
    ;;
  1)
    if [[ "$1" == "--preflight" ]]; then
      mode=preflight
    elif [[ "$1" == "--witness-preflight" ]]; then
      mode=witness-preflight
    else
      usage
      exit 64
    fi
    ;;
  3)
    if [[ "$1" != "--problem-diagnostic" || "$2" != "--timeout-seconds" ]]; then
      usage
      exit 64
    fi
    mode="${1#--}"
    requested_timeout_seconds="$3"
    case "$requested_timeout_seconds" in
      ''|*[!0-9]*)
        echo "diagnostic timeout must be a positive integer number of seconds" >&2
        exit 64
        ;;
    esac
    if ((requested_timeout_seconds < 1)); then
      echo "diagnostic timeout must be positive" >&2
      exit 64
    fi
    ;;
  5)
    if [[ "$1" != "--module-diagnostic" || "$2" != "--candidate" || \
          "$4" != "--timeout-seconds" ]]; then
      usage
      exit 64
    fi
    mode=module-diagnostic
    module_candidate="$3"
    requested_timeout_seconds="$5"
    if [[ ! "$module_candidate" =~ ^ProofModules/[A-Z][A-Za-z0-9_]*\.v$ ]]; then
      echo "module diagnostic candidate must be ProofModules/<UppercaseRocqIdentifier>.v" >&2
      exit 64
    fi
    case "$requested_timeout_seconds" in
      ''|*[!0-9]*)
        echo "diagnostic timeout must be a positive integer number of seconds" >&2
        exit 64
        ;;
    esac
    if ((requested_timeout_seconds < 1)); then
      echo "diagnostic timeout must be positive" >&2
      exit 64
    fi
    ;;
  *)
    usage
    exit 64
    ;;
esac

: "${LOGOS_REPO_ROOT:?set LOGOS_REPO_ROOT to the trusted Logos repository root}"
: "${LOGOS_PROOF_WORKDIR:?set LOGOS_PROOF_WORKDIR to the checked proof workspace}"
: "${LOGOS_TRUSTED_ROCQ_CACHE_DIR:?set the host-only trusted diagnostic cache directory}"

TRUSTED_ENVIRONMENT_FAILURE_EXIT_CODE=86

trusted_environment_failure() {
  local phase="$1"
  local status="$2"
  echo "LOGOS_TRUSTED_ROCQ_ENVIRONMENT_FAILURE phase=$phase status=$status" >&2
  exit "$TRUSTED_ENVIRONMENT_FAILURE_EXIT_CODE"
}

if [[ -n "${LOGOS_ROCQ_OPAM_SWITCH:-}" ]]; then
  LOGOS_ROCQ_OPAM_SWITCH="$(cd "$LOGOS_ROCQ_OPAM_SWITCH" && pwd)"
  ROCQ_BIN="$LOGOS_ROCQ_OPAM_SWITCH/_opam/bin/rocq"
  BWRAP_COMMAND="$LOGOS_ROCQ_OPAM_SWITCH/_opam/bin/bwrap"
else
  command -v rocq >/dev/null 2>&1 || {
    echo "rocq not found. Put rocq in PATH or set LOGOS_ROCQ_OPAM_SWITCH." >&2
    trusted_environment_failure "rocq-lookup" 127
  }
  ROCQ_BIN="$(command -v rocq)"
  command -v bwrap >/dev/null 2>&1 || {
    echo "bubblewrap (bwrap) is required to isolate untrusted Rocq compilation." >&2
    trusted_environment_failure "bwrap-lookup" 127
  }
  BWRAP_COMMAND="$(command -v bwrap)"
fi
if [[ "$ROCQ_BIN" != /* || ! -s "$ROCQ_BIN" || ! -x "$ROCQ_BIN" || -L "$ROCQ_BIN" ]]; then
  echo "resolved Rocq driver must be an absolute nonempty executable non-symlink file" >&2
  trusted_environment_failure "rocq-switch" 127
fi
if [[ "$BWRAP_COMMAND" != /* || ! -s "$BWRAP_COMMAND" || ! -x "$BWRAP_COMMAND" || -L "$BWRAP_COMMAND" ]]; then
  echo "resolved bubblewrap must be an absolute nonempty executable non-symlink file" >&2
  trusted_environment_failure "bwrap-lookup" 127
fi
ROCQ_BIN_DIR="${ROCQ_BIN%/*}"
ROCQ_INSTALL_PREFIX="${ROCQ_BIN_DIR%/*}"
export PATH="$ROCQ_BIN_DIR:/usr/bin:/bin"
BWRAP_BIN="$(realpath "$BWRAP_COMMAND")"

CHECKER_PATH="$(realpath "${BASH_SOURCE[0]}")"
LOGOS_REPO_ROOT="$(cd "$LOGOS_REPO_ROOT" && pwd)"
WORKDIR="$(cd "$LOGOS_PROOF_WORKDIR" && pwd)"
CACHE_PATH_INPUT="$LOGOS_TRUSTED_ROCQ_CACHE_DIR"
CACHE_PARENT_INPUT="$(dirname -- "$CACHE_PATH_INPUT")"
CACHE_NAME="$(basename -- "$CACHE_PATH_INPUT")"

case "$CACHE_PATH_INPUT" in
  /*)
    ;;
  *)
    echo "trusted diagnostic cache path must be absolute" >&2
    trusted_environment_failure "diagnostic-cache-location" 2
    ;;
esac
case "$CACHE_NAME" in
  ''|.|..|*$'\n'*)
    echo "trusted diagnostic cache has an unsafe basename" >&2
    trusted_environment_failure "diagnostic-cache-location" 2
    ;;
esac

# The cache parent is a host-owned case artifact directory. It is also the
# authority for the checker scratch root below, so no component may be a
# symlink or a lexical traversal. This keeps every checker invocation on the
# same case-local filesystem without trusting TMPDIR or the global /tmp.
assert_safe_absolute_directory() {
  local path="$1"
  local phase="$2"
  local relative component current=
  local -a components=()

  if [[ "$path" != /* || "$path" == / || "$path" == *$'\n'* ]]; then
    echo "unsafe absolute directory for $phase: $path" >&2
    trusted_environment_failure "$phase" 2
  fi
  relative="${path#/}"
  IFS='/' read -r -a components <<<"$relative"
  for component in "${components[@]}"; do
    case "$component" in
      ''|.|..)
        echo "unsafe path component for $phase: $path" >&2
        trusted_environment_failure "$phase" 2
        ;;
    esac
    current="$current/$component"
    if [[ -L "$current" ]]; then
      echo "refusing symlinked path component for $phase: $current" >&2
      trusted_environment_failure "$phase" 2
    fi
  done
  if [[ ! -d "$path" ]]; then
    echo "required directory is missing for $phase: $path" >&2
    trusted_environment_failure "$phase" 2
  fi
}

assert_safe_absolute_directory "$CACHE_PARENT_INPUT" "diagnostic-cache-location"
CACHE_PARENT="$(cd "$CACHE_PARENT_INPUT" && pwd -P)"
if [[ "$CACHE_PARENT" != "$CACHE_PARENT_INPUT" ]]; then
  echo "trusted diagnostic cache parent is not a canonical path" >&2
  trusted_environment_failure "diagnostic-cache-location" 2
fi
TRUSTED_CACHE="$CACHE_PARENT/$CACHE_NAME"
PROBLEM_CACHE="$CACHE_PARENT/problem-compile-cache"
SHARED_PREFIX_CACHE_ROOT="${LOGOS_SHARED_ROCQ_PREFIX_CACHE_DIR:-}"
SHARED_CHECKER_RUNTIME_CACHE_ROOT="${LOGOS_SHARED_ROCQ_CHECKER_RUNTIME_CACHE_DIR:-}"
SHARED_AUTHORITY_SHA256="${LOGOS_TRUSTED_ROCQ_AUTHORITY_SHA256:-}"
SHARED_PREFIX_KEY=
SHARED_PREFIX_HIT=false
if [[ -n "$SHARED_PREFIX_CACHE_ROOT" || -n "$SHARED_AUTHORITY_SHA256" ]]; then
  if [[ "$SHARED_PREFIX_CACHE_ROOT" != /* ||
        ! "$SHARED_AUTHORITY_SHA256" =~ ^[0-9a-f]{64}$ ]]; then
    echo "shared generated-prefix cache contract is malformed" >&2
    trusted_environment_failure "shared-prefix-cache" 2
  fi
  mkdir -p "$SHARED_PREFIX_CACHE_ROOT" \
    || trusted_environment_failure "shared-prefix-cache" "$?"
  if [[ -L "$SHARED_PREFIX_CACHE_ROOT" || ! -d "$SHARED_PREFIX_CACHE_ROOT" ]]; then
    echo "shared generated-prefix cache root is unsafe" >&2
    trusted_environment_failure "shared-prefix-cache" 2
  fi
fi
if [[ -n "$SHARED_CHECKER_RUNTIME_CACHE_ROOT" ]]; then
  if [[ "$SHARED_CHECKER_RUNTIME_CACHE_ROOT" != /* ]]; then
    echo "shared checker-runtime cache path must be absolute" >&2
    trusted_environment_failure "shared-checker-runtime-cache" 2
  fi
  mkdir -p "$SHARED_CHECKER_RUNTIME_CACHE_ROOT" \
    || trusted_environment_failure "shared-checker-runtime-cache" "$?"
  if [[ -L "$SHARED_CHECKER_RUNTIME_CACHE_ROOT" ||
        ! -d "$SHARED_CHECKER_RUNTIME_CACHE_ROOT" ]]; then
    echo "shared checker-runtime cache root is unsafe" >&2
    trusted_environment_failure "shared-checker-runtime-cache" 2
  fi
fi

# Recover the only destructive window that cannot run the EXIT trap: an
# uncatchable process death after the live cache was renamed aside but before
# the staged replacement was published. A pending stage was never reported as
# successful and is discarded; exactly one retained old cache is restored.
recover_interrupted_cache_swap() {
  local candidate
  local -a old_candidates=() stage_candidates=()
  shopt -s nullglob
  old_candidates=("$CACHE_PARENT"/.logos-trusted-diagnostic-cache-old.*)
  stage_candidates=("$CACHE_PARENT"/.logos-trusted-diagnostic-cache.*)
  shopt -u nullglob
  for candidate in "${old_candidates[@]}" "${stage_candidates[@]}"; do
    [[ -d "$candidate" && ! -L "$candidate" ]] || {
      echo "interrupted trusted-cache artifact is unsafe: $candidate" >&2
      trusted_environment_failure "diagnostic-cache-recovery" 2
    }
  done
  if [[ ! -e "$TRUSTED_CACHE" && ! -L "$TRUSTED_CACHE" ]]; then
    if ((${#old_candidates[@]} > 1)); then
      echo "multiple prior trusted caches prevent unambiguous recovery" >&2
      trusted_environment_failure "diagnostic-cache-recovery" 2
    elif ((${#old_candidates[@]} == 1)); then
      mv -T "${old_candidates[0]}" "$TRUSTED_CACHE" \
        || trusted_environment_failure "diagnostic-cache-recovery" "$?"
      old_candidates=()
    fi
  fi
  for candidate in "${stage_candidates[@]}"; do
    rm -rf -- "$candidate" \
      || trusted_environment_failure "diagnostic-cache-recovery" "$?"
  done
}
recover_interrupted_cache_swap

discard_superseded_cache_backups() {
  local candidate
  local -a old_candidates=()
  shopt -s nullglob
  old_candidates=("$CACHE_PARENT"/.logos-trusted-diagnostic-cache-old.*)
  shopt -u nullglob
  for candidate in "${old_candidates[@]}"; do
    [[ -d "$candidate" && ! -L "$candidate" ]] || {
      echo "superseded trusted-cache backup is unsafe: $candidate" >&2
      trusted_environment_failure "diagnostic-cache-recovery" 2
    }
    rm -rf -- "$candidate" \
      || trusted_environment_failure "diagnostic-cache-recovery" "$?"
  done
}

if [[ -L "$TRUSTED_CACHE" || ( -e "$TRUSTED_CACHE" && ! -d "$TRUSTED_CACHE" ) ]]; then
  echo "trusted diagnostic cache is symlinked or not a directory: $TRUSTED_CACHE" >&2
  trusted_environment_failure "diagnostic-cache-location" 2
fi
case "$CHECKER_PATH" in
  "$WORKDIR"|"$WORKDIR"/*)
    echo "refusing to run the trusted checker from an agent-writable workspace" >&2
    trusted_environment_failure "checker-location" 2
    ;;
esac
case "$TRUSTED_CACHE" in
  "$WORKDIR"|"$WORKDIR"/*)
    echo "refusing a trusted diagnostic cache inside the agent-writable workspace" >&2
    trusted_environment_failure "diagnostic-cache-location" 2
    ;;
esac

for name in Schema.v Queries.v Witness.v Problem.v Goal.v; do
  path="$WORKDIR/$name"
  if [[ ! -f "$path" || -L "$path" ]]; then
    echo "missing trusted-check input or input is not a regular non-symlink file: $path" >&2
    trusted_environment_failure "proof-workspace" 2
  fi
done

HOST_TMP_ROOT="$CACHE_PARENT/host-tmp"
if [[ -e "$HOST_TMP_ROOT" || -L "$HOST_TMP_ROOT" ]]; then
  if [[ ! -d "$HOST_TMP_ROOT" || -L "$HOST_TMP_ROOT" || ! -O "$HOST_TMP_ROOT" ]]; then
    echo "trusted checker scratch root is unsafe: $HOST_TMP_ROOT" >&2
    trusted_environment_failure "checker-scratch-location" 2
  fi
else
  mkdir -m 700 "$HOST_TMP_ROOT" \
    || trusted_environment_failure "checker-scratch-location" "$?"
fi
chmod 700 "$HOST_TMP_ROOT" \
  || trusted_environment_failure "checker-scratch-location" "$?"
assert_safe_absolute_directory "$HOST_TMP_ROOT" "checker-scratch-location"
case "$HOST_TMP_ROOT" in
  "$WORKDIR"|"$WORKDIR"/*)
    echo "refusing trusted checker scratch inside the agent-writable workspace" >&2
    trusted_environment_failure "checker-scratch-location" 2
    ;;
esac

CHECKDIR="$(mktemp -d "$HOST_TMP_ROOT/trusted-rocq-check.XXXXXX")"
if [[ ! -d "$CHECKDIR" || -L "$CHECKDIR" || ! -O "$CHECKDIR" ]]; then
  echo "trusted checker failed to create a safe scratch directory" >&2
  trusted_environment_failure "checker-scratch-location" 2
fi
CACHE_STAGE=
CACHE_OLD=
CACHE_PUBLISHED=false
cleanup_trusted_checker() {
  local status="$?"
  trap - EXIT
  # EXIT traps inherit `errexit`. Recovery of the last valid cache must happen
  # before any best-effort scratch cleanup, and no cleanup failure may abort the
  # rollback path.
  set +e
  if [[ -n "${CACHE_OLD:-}" ]]; then
    case "$CACHE_OLD" in
      "$CACHE_PARENT"/.logos-trusted-diagnostic-cache-old.*)
        if [[ -d "$CACHE_OLD" && ! -L "$CACHE_OLD" ]]; then
          if [[ ( "${CACHE_PUBLISHED:-false}" == true ||
                  ( -n "${CACHE_STAGE:-}" && ! -e "$CACHE_STAGE" &&
                    ! -L "$CACHE_STAGE" ) ) &&
                -d "$TRUSTED_CACHE" && ! -L "$TRUSTED_CACHE" ]]; then
            CACHE_PUBLISHED=true
            # Compilation and atomic publication both completed. A late signal
            # interrupted only cleanup/reporting, so expose success to a direct
            # caller and let the Rust parent retain the already-installed source.
            status=0
            rm -rf -- "$CACHE_OLD"
          elif [[ ! -e "$TRUSTED_CACHE" && ! -L "$TRUSTED_CACHE" ]]; then
            mv -T "$CACHE_OLD" "$TRUSTED_CACHE" >/dev/null 2>&1 || {
              echo "failed to restore the prior trusted module cache after interruption: $CACHE_OLD" >&2
            }
          else
            echo "retaining prior trusted module cache because replacement publication was not confirmed: $CACHE_OLD" >&2
          fi
        fi
        ;;
    esac
  fi
  if [[ -n "${CACHE_STAGE:-}" ]]; then
    case "$CACHE_STAGE" in
      "$CACHE_PARENT"/.logos-trusted-diagnostic-cache.*)
        rm -rf -- "$CACHE_STAGE"
        ;;
    esac
  fi
  if [[ -n "${CHECKDIR:-}" ]]; then
    case "$CHECKDIR" in
      "$HOST_TMP_ROOT"/trusted-rocq-check.*)
        rm -rf -- "$CHECKDIR"
        ;;
    esac
  fi
  exit "$status"
}
trap cleanup_trusted_checker EXIT
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM
TRUSTEDDIR="$CHECKDIR/trusted"
PROBLEMDIR="$CHECKDIR/problem"
GOALDIR="$CHECKDIR/goal"
AUTHORITYDIR="$LOGOS_REPO_ROOT"
OSLIBDIR="$CHECKDIR/os-libs"
ROCQBINDIR="$CHECKDIR/rocq-bin"
PROBLEMOUTDIR="$CHECKDIR/problem-output"
HOSTHOMEDIR="$CHECKDIR/host-home"
HOSTXDGDATAHOME="$CHECKDIR/host-xdg-data-home"
HOSTXDGDATADIRS="$CHECKDIR/host-xdg-data-dirs"
mkdir -p \
  "$TRUSTEDDIR" \
  "$PROBLEMDIR/tmp" "$PROBLEMDIR/ProofModules" \
  "$PROBLEMOUTDIR/tmp" "$PROBLEMOUTDIR/ProofModules" \
  "$HOSTHOMEDIR" \
  "$HOSTXDGDATAHOME" "$HOSTXDGDATADIRS" \
  "$GOALDIR/tmp" "$GOALDIR/ProofModules" \
  "$OSLIBDIR" \
  "$ROCQBINDIR"
chmod 700 "$HOSTHOMEDIR"
export HOME="$HOSTHOMEDIR"
export XDG_CONFIG_HOME="$HOSTHOMEDIR/.config"
export XDG_CACHE_HOME="$HOSTHOMEDIR/.cache"
# Avoid Rocq's fallback to the absolute data directory compiled into the
# source switch.  Both values are host-created, invocation-private roots.
export XDG_DATA_HOME="$HOSTXDGDATAHOME"
export XDG_DATA_DIRS="$HOSTXDGDATADIRS"

if [[ -n "${LOGOS_ROCQ_OPAM_SWITCH:-}" ]]; then
  export ROCQLIB="$LOGOS_ROCQ_OPAM_SWITCH/_opam/lib/coq"
  export COQLIB="$ROCQLIB"
  export OCAMLFIND_CONF="$LOGOS_ROCQ_OPAM_SWITCH/_opam/lib/findlib.conf"
fi

command -v rocq >/dev/null 2>&1 || {
  echo "rocq not found. Put rocq in PATH or set LOGOS_ROCQ_OPAM_SWITCH." >&2
  trusted_environment_failure "rocq-lookup" 127
}
if [[ "$(realpath "$(command -v rocq)")" != "$(realpath "$ROCQ_BIN")" ]]; then
  echo "resolved Rocq binary differs from the configured switch" >&2
  trusted_environment_failure "rocq-switch-resolution" 127
fi
for host_tool in \
  bash timeout cat realpath dirname basename mktemp rm mkdir chmod install \
  find sort ldd awk readelf cp sha256sum cmp tee grep mv readlink stat id flock; do
  command -v "$host_tool" >/dev/null 2>&1 \
    || trusted_environment_failure "host-tool-$host_tool" 127
done

ROCQ_BIN="$(realpath "$ROCQ_BIN")"
ROCQ_RUNTIME_DIR="$ROCQ_INSTALL_PREFIX/lib/rocq-runtime"
ROCQ_STDLIB_DIR="$ROCQ_INSTALL_PREFIX/lib/coq"
ROCQ_STUBLIBS_DIR="$ROCQ_INSTALL_PREFIX/lib/stublibs"
ROCQ_OCAML_DIR="$ROCQ_INSTALL_PREFIX/lib/ocaml"
ROCQ_FINDLIB_DIR="$ROCQ_INSTALL_PREFIX/lib/findlib"
ROCQ_ZARITH_DIR="$ROCQ_INSTALL_PREFIX/lib/zarith"
ROCQ_FINDLIB_CONF="$ROCQ_INSTALL_PREFIX/lib/findlib.conf"
ROCQCHK_BIN="$ROCQ_INSTALL_PREFIX/bin/rocqchk"
for path in \
  "$ROCQ_RUNTIME_DIR" "$ROCQ_STDLIB_DIR" "$ROCQ_STUBLIBS_DIR" \
  "$ROCQ_OCAML_DIR" "$ROCQ_FINDLIB_DIR" "$ROCQ_ZARITH_DIR"; do
  if [[ ! -d "$path" || -L "$path" ]]; then
    echo "required Rocq runtime directory is missing or symlinked: $path" >&2
    trusted_environment_failure "rocq-runtime" 127
  fi
done
if [[ ! -f "$ROCQ_FINDLIB_CONF" || -L "$ROCQ_FINDLIB_CONF" ]]; then
  echo "required Rocq findlib configuration is missing or symlinked: $ROCQ_FINDLIB_CONF" >&2
  trusted_environment_failure "rocq-runtime" 127
fi
export ROCQLIB="$ROCQ_STDLIB_DIR"
export COQLIB="$ROCQ_STDLIB_DIR"
export OCAMLLIB="$ROCQ_OCAML_DIR"
export CAMLLIB="$ROCQ_OCAML_DIR"
export OCAMLFIND_CONF="$ROCQ_FINDLIB_CONF"
export CAML_LD_LIBRARY_PATH="$ROCQ_STUBLIBS_DIR:$ROCQ_OCAML_DIR/stublibs"
export LD_LIBRARY_PATH="$ROCQ_STUBLIBS_DIR:$ROCQ_OCAML_DIR/stublibs"
ROCQ_SANDBOX_FINDLIB_CONF="$CHECKDIR/findlib.conf"
printf '%s\n' \
  'destdir="/rocq/lib"' \
  'path="/rocq/lib/ocaml:/rocq/lib"' \
  >"$ROCQ_SANDBOX_FINDLIB_CONF"
chmod 444 "$ROCQ_SANDBOX_FINDLIB_CONF"
for executable in \
  "$ROCQCHK_BIN" \
  "$ROCQ_RUNTIME_DIR/rocqworker" \
  "$ROCQ_RUNTIME_DIR/rocqnative"; do
  if [[ ! -s "$executable" || ! -x "$executable" || -L "$executable" ]]; then
    echo "required Rocq executable is missing, empty, non-executable, or symlinked: $executable" >&2
    trusted_environment_failure "rocq-runtime" 127
  fi
done

# Build the sandbox-only authority and runtime closure only for a mode that
# actually compiles agent-controlled Problem.v.  Preflight checks the generated
# immutable prefix directly and is immediately followed by a problem-diagnostic
# checkpoint in the proof workflow; copying this  source/object closure during
# preflight was therefore pure duplicate I/O.
if [[ "$mode" != preflight && "$mode" != witness-preflight ]]; then
# The runner already supplies a content-bound, read-only authority snapshot,
# not the mutable repository. Validate its complete source/object closure and
# mount it directly instead of copying the same closure for every diagnostic.
is_excluded_authority_source() {
  local relative="${1,,}"
  case "/$relative/" in
    *example*|*/catalog/*|*/build/*|*/_build/*|*/var/*)
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

  if [[ "$relative" == "$source" || "$relative" == ../* || "$relative" == */../* ]]; then
    echo "authority source escaped its root: $source" >&2
    trusted_environment_failure "authority-closure" 2
  fi
  if [[ ! -f "$source" || -L "$source" ]]; then
    echo "authority source is not a regular non-symlink file: $source" >&2
    trusted_environment_failure "authority-closure" 2
  fi
  if [[ ! -s "$object" || -L "$object" ]]; then
    echo "authority source lacks a nonempty regular object: $source" >&2
    trusted_environment_failure "authority-closure" 2
  fi
  if [[ "$source" -nt "$object" ]]; then
    echo "authority object predates its source; rebuild before checking: $object" >&2
    trusted_environment_failure "authority-closure" 2
  fi
  if [[ "$(stat -c '%a' "$source")" != 444 || "$(stat -c '%a' "$object")" != 444 ]]; then
    echo "authority source/object pair is not immutable: $source" >&2
    trusted_environment_failure "authority-closure" 2
  fi
  authority_source_count=$((authority_source_count + 1))
}

VENDOR_SOURCE_ROOT="$LOGOS_REPO_ROOT/vendor/FormalSQL/src"
LOGOS_SOURCE_ROOT="$LOGOS_REPO_ROOT/theories/FormalSQL"
for path in "$VENDOR_SOURCE_ROOT" "$LOGOS_SOURCE_ROOT"; do
  if [[ ! -d "$path" || -L "$path" ]]; then
    echo "required authority source tree is missing or symlinked: $path" >&2
    trusted_environment_failure "authority-closure" 2
  fi
done
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
  echo "trusted Rocq authority closure is empty" >&2
  trusted_environment_failure "authority-closure" 2
fi

# Stage only the ELF dependencies needed by the Rocq driver, worker, native
# helper, and OCaml stubs.  Each staged file is mounted at the absolute path
# reported by ldd, because the Rocq driver does not preserve LD_LIBRARY_PATH
# when it starts rocqworker.  No host library directory is exposed.  The ELF
# interpreter likewise retains its compiled absolute path.  The resulting
# closure is content-addressed and immutable, so later diagnostics do not
# repeat ldd/readelf or copy the same runtime payload again.
declare -A BWRAP_RUNTIME_DIRS=()
declare -A BWRAP_RUNTIME_BIND_SOURCES=()
BWRAP_RUNTIME_DIR_ARGS=()
BWRAP_RUNTIME_BIND_ARGS=()
CHECKER_RUNTIME_CACHE_KEY=
CHECKER_RUNTIME_CACHE_HIT=false

append_runtime_directory() {
  local directory="$1"
  local relative component current=
  local -a components=()
  if [[ "$directory" != /* || "$directory" == *$'\n'* ]]; then
    echo "invalid absolute Rocq runtime directory: $directory" >&2
    trusted_environment_failure "rocq-runtime-library" 127
  fi
  relative="${directory#/}"
  IFS='/' read -r -a components <<<"$relative"
  for component in "${components[@]}"; do
    [[ -n "$component" ]] || continue
    current="$current/$component"
    if [[ -z "${BWRAP_RUNTIME_DIRS[$current]+set}" ]]; then
      BWRAP_RUNTIME_DIRS["$current"]=1
      BWRAP_RUNTIME_DIR_ARGS+=(--dir "$current")
    fi
  done
}

stage_elf_dependencies() {
  local executable="$1"
  local dependency resolved destination
  while IFS= read -r dependency; do
    [[ -n "$dependency" ]] || continue
    resolved="$(realpath "$dependency")"
    if [[ ! -s "$resolved" || -L "$resolved" ]]; then
      echo "invalid Rocq runtime dependency: $dependency" >&2
      trusted_environment_failure "rocq-runtime-library" 127
    fi
    destination="$OSLIBDIR/${resolved##*/}"
    if [[ -e "$destination" ]] && ! cmp -s "$resolved" "$destination"; then
      echo "conflicting Rocq runtime libraries share a basename: ${resolved##*/}" >&2
      trusted_environment_failure "rocq-runtime-library" 127
    fi
    if [[ ! -e "$destination" ]]; then
      install -m 444 "$resolved" "$destination"
    fi
    append_runtime_directory "$(dirname "$dependency")"
    if [[ -n "${BWRAP_RUNTIME_BIND_SOURCES[$dependency]+set}" &&
          "${BWRAP_RUNTIME_BIND_SOURCES[$dependency]}" != "$destination" ]]; then
      echo "conflicting Rocq runtime dependency target: $dependency" >&2
      trusted_environment_failure "rocq-runtime-library" 127
    fi
    if [[ -z "${BWRAP_RUNTIME_BIND_SOURCES[$dependency]+set}" ]]; then
      BWRAP_RUNTIME_BIND_SOURCES["$dependency"]="$destination"
      BWRAP_RUNTIME_BIND_ARGS+=(--ro-bind "$destination" "$dependency")
    fi
  done < <(
    ldd "$executable" | awk '
      /=>[[:space:]]+\// { print $3; next }
      /^[[:space:]]*\// { print $1 }
    '
  )
}

checker_runtime_input_key() {
  {
    printf '%s\n' 'logos-trusted-checker-runtime-closure-v1'
    printf 'install-prefix=%s\n' "$ROCQ_INSTALL_PREFIX"
    for executable in \
      "$ROCQ_BIN" "$BWRAP_BIN" \
      "$ROCQ_RUNTIME_DIR/rocqworker" "$ROCQ_RUNTIME_DIR/rocqnative"; do
      printf 'consumer=%s\n' "$executable"
      sha256sum "$executable"
    done
    while IFS= read -r -d '' stub; do
      printf 'consumer=%s\n' "$stub"
      sha256sum "$stub"
    done < <(
      find "$ROCQ_STUBLIBS_DIR" "$ROCQ_OCAML_DIR/stublibs" \
        -maxdepth 1 -type f -name '*.so' -print0 | LC_ALL=C sort -z
    )
  } | sha256sum | awk '{print $1}'
}

write_checker_runtime_digests() {
  local root="$1" output="$2" file
  (
    cd "$root"
    {
      sha256sum INPUT-KEY INTERPRETER DIRECTORIES BINDINGS rocq-bin/rocq
      while IFS= read -r file; do
        sha256sum "elf-interpreter/$file"
      done < <(find elf-interpreter -mindepth 1 -maxdepth 1 -type f -printf '%f\n' | LC_ALL=C sort)
      while IFS= read -r file; do
        sha256sum "os-libs/$file"
      done < <(find os-libs -mindepth 1 -maxdepth 1 -type f -printf '%f\n' | LC_ALL=C sort)
    } >"$output"
  )
}

load_checker_runtime_cache() {
  local bundle="$1" expected_manifest="$CHECKDIR/checker-runtime.SHA256SUMS"
  local entry target staged directory file
  local -a top_entries=() rocq_entries=() interpreter_entries=() os_library_entries=()
  if [[ ! -d "$bundle" || -L "$bundle" || "$(stat -c '%a' "$bundle")" != 555 ]]; then
    return 1
  fi
  mapfile -t top_entries < <(
    find "$bundle" -mindepth 1 -maxdepth 1 -printf '%f\n' | LC_ALL=C sort
  )
  if [[ "${top_entries[*]}" != \
        'BINDINGS DIRECTORIES INPUT-KEY INTERPRETER SHA256SUMS elf-interpreter os-libs rocq-bin' ]]; then
    echo "shared checker-runtime cache file set drifted: $bundle" >&2
    trusted_environment_failure "shared-checker-runtime-cache" 2
  fi
  for directory in rocq-bin elf-interpreter os-libs; do
    if [[ ! -d "$bundle/$directory" || -L "$bundle/$directory" ||
          "$(stat -c '%a' "$bundle/$directory")" != 555 ]]; then
      echo "shared checker-runtime cache directory is unsafe: $bundle/$directory" >&2
      trusted_environment_failure "shared-checker-runtime-cache" 2
    fi
  done
  for entry in INPUT-KEY INTERPRETER DIRECTORIES BINDINGS SHA256SUMS; do
    if [[ ! -s "$bundle/$entry" || -L "$bundle/$entry" ||
          "$(stat -c '%a' "$bundle/$entry")" != 444 ||
          "$(stat -c '%h' "$bundle/$entry")" != 1 ]]; then
      echo "shared checker-runtime cache control file is unsafe: $bundle/$entry" >&2
      trusted_environment_failure "shared-checker-runtime-cache" 2
    fi
  done
  if [[ "$(cat "$bundle/INPUT-KEY")" != "$CHECKER_RUNTIME_CACHE_KEY" ]]; then
    echo "shared checker-runtime cache key drifted" >&2
    trusted_environment_failure "shared-checker-runtime-cache" 2
  fi
  if [[ ! -s "$bundle/rocq-bin/rocq" || -L "$bundle/rocq-bin/rocq" ||
        "$(stat -c '%a' "$bundle/rocq-bin/rocq")" != 555 ||
        "$(stat -c '%h' "$bundle/rocq-bin/rocq")" != 1 ||
        ! -x "$bundle/rocq-bin/rocq" ]] ||
     ! cmp -s "$ROCQ_BIN" "$bundle/rocq-bin/rocq"; then
    echo "shared checker-runtime Rocq driver is unsafe" >&2
    trusted_environment_failure "shared-checker-runtime-cache" 2
  fi
  mapfile -t rocq_entries < <(
    find "$bundle/rocq-bin" -mindepth 1 -maxdepth 1 -type f -printf '%f\n' | LC_ALL=C sort
  )
  if [[ "${rocq_entries[*]}" != rocq ]]; then
    echo "shared checker-runtime Rocq driver set drifted" >&2
    trusted_environment_failure "shared-checker-runtime-cache" 2
  fi
  ROCQ_ELF_INTERPRETER="$(cat "$bundle/INTERPRETER")"
  if [[ "$ROCQ_ELF_INTERPRETER" != /* || "$ROCQ_ELF_INTERPRETER" == *$'\n'* ||
        "${ROCQ_ELF_INTERPRETER##*/}" == *$'\t'* ]]; then
    echo "shared checker-runtime interpreter target is invalid" >&2
    trusted_environment_failure "shared-checker-runtime-cache" 2
  fi
  mapfile -t interpreter_entries < <(
    find "$bundle/elf-interpreter" -mindepth 1 -maxdepth 1 -type f -printf '%f\n' | LC_ALL=C sort
  )
  if [[ "${interpreter_entries[*]}" != "${ROCQ_ELF_INTERPRETER##*/}" ||
        ! -s "$bundle/elf-interpreter/${ROCQ_ELF_INTERPRETER##*/}" ||
        -L "$bundle/elf-interpreter/${ROCQ_ELF_INTERPRETER##*/}" ||
        "$(stat -c '%a' "$bundle/elf-interpreter/${ROCQ_ELF_INTERPRETER##*/}")" != 555 ||
        "$(stat -c '%h' "$bundle/elf-interpreter/${ROCQ_ELF_INTERPRETER##*/}")" != 1 ]]; then
    echo "shared checker-runtime interpreter is unsafe" >&2
    trusted_environment_failure "shared-checker-runtime-cache" 2
  fi
  mapfile -t os_library_entries < <(
    find "$bundle/os-libs" -mindepth 1 -maxdepth 1 -type f -printf '%f\n' | LC_ALL=C sort
  )
  if ((${#os_library_entries[@]} == 0)); then
    echo "shared checker-runtime OS library closure is empty" >&2
    trusted_environment_failure "shared-checker-runtime-cache" 2
  fi
  for file in "${os_library_entries[@]}"; do
    if [[ "$file" == *$'\t'* || "$file" == *$'\n'* ||
          ! -s "$bundle/os-libs/$file" || -L "$bundle/os-libs/$file" ||
          "$(stat -c '%a' "$bundle/os-libs/$file")" != 444 ||
          "$(stat -c '%h' "$bundle/os-libs/$file")" != 1 ]]; then
      echo "shared checker-runtime OS library is unsafe: $file" >&2
      trusted_environment_failure "shared-checker-runtime-cache" 2
    fi
  done
  while IFS= read -r directory || [[ -n "$directory" ]]; do
    if [[ "$directory" != /* || "$directory" == *$'\t'* || "$directory" == *$'\n'* ]]; then
      echo "shared checker-runtime directory target is invalid" >&2
      trusted_environment_failure "shared-checker-runtime-cache" 2
    fi
    append_runtime_directory "$directory"
  done <"$bundle/DIRECTORIES"
  while IFS=$'\t' read -r target staged extra || [[ -n "$target$staged$extra" ]]; do
    if [[ "$target" != /* || -n "$extra" || -z "$staged" || "$staged" == */* ||
          "$staged" == '.' || "$staged" == '..' || "$staged" == *$'\n'* ||
          ! -s "$bundle/os-libs/$staged" || -L "$bundle/os-libs/$staged" ||
          "$(stat -c '%a' "$bundle/os-libs/$staged")" != 444 ]]; then
      echo "shared checker-runtime binding is invalid" >&2
      trusted_environment_failure "shared-checker-runtime-cache" 2
    fi
    if [[ -n "${BWRAP_RUNTIME_BIND_SOURCES[$target]+set}" ]]; then
      echo "shared checker-runtime repeats a binding target: $target" >&2
      trusted_environment_failure "shared-checker-runtime-cache" 2
    fi
    BWRAP_RUNTIME_BIND_SOURCES["$target"]="$bundle/os-libs/$staged"
    BWRAP_RUNTIME_BIND_ARGS+=(--ro-bind "$bundle/os-libs/$staged" "$target")
  done <"$bundle/BINDINGS"
  write_checker_runtime_digests "$bundle" "$expected_manifest"
  if ! cmp -s "$expected_manifest" "$bundle/SHA256SUMS"; then
    echo "shared checker-runtime cache digest binding drifted" >&2
    trusted_environment_failure "shared-checker-runtime-cache" 2
  fi
  OSLIBDIR="$bundle/os-libs"
  ROCQBINDIR="$bundle/rocq-bin"
  ROCQ_ELF_INTERPRETER_DIR="$bundle/elf-interpreter"
  STAGED_ELF_INTERPRETER="$ROCQ_ELF_INTERPRETER_DIR/${ROCQ_ELF_INTERPRETER##*/}"
  CHECKER_RUNTIME_CACHE_HIT=true
  echo "LOGOS_TRUSTED_ROCQ_CHECKER_RUNTIME_CACHE hit=true key=$CHECKER_RUNTIME_CACHE_KEY" >&2
}

stage_checker_runtime() {
  local dependency
  install -m 555 "$ROCQ_BIN" "$ROCQBINDIR/rocq"
  stage_elf_dependencies "$ROCQ_BIN"
  stage_elf_dependencies "$BWRAP_BIN"
  stage_elf_dependencies "$ROCQ_RUNTIME_DIR/rocqworker"
  stage_elf_dependencies "$ROCQ_RUNTIME_DIR/rocqnative"
  while IFS= read -r -d '' dependency; do
    stage_elf_dependencies "$dependency"
  done < <(
    find "$ROCQ_STUBLIBS_DIR" "$ROCQ_OCAML_DIR/stublibs" \
      -maxdepth 1 -type f -name '*.so' -print0 | LC_ALL=C sort -z
  )

  ROCQ_ELF_INTERPRETER="$({
    readelf -l "$ROCQ_BIN" | awk -F': ' '/Requesting program interpreter/ {
      value=$2; sub(/]$/, "", value); print value; exit
    }'
  })"
  if [[ "$ROCQ_ELF_INTERPRETER" != /* ]]; then
    echo "could not determine the absolute Rocq ELF interpreter" >&2
    trusted_environment_failure "rocq-runtime-library" 127
  fi
  ROCQ_ELF_INTERPRETER_SOURCE="$(realpath "$ROCQ_ELF_INTERPRETER")"
  if [[ ! -s "$ROCQ_ELF_INTERPRETER_SOURCE" ]]; then
    echo "Rocq ELF interpreter is missing: $ROCQ_ELF_INTERPRETER" >&2
    trusted_environment_failure "rocq-runtime-library" 127
  fi
  append_runtime_directory "$(dirname "$ROCQ_ELF_INTERPRETER")"
  install -m 444 "$ROCQ_ELF_INTERPRETER_SOURCE" \
    "$OSLIBDIR/${ROCQ_ELF_INTERPRETER_SOURCE##*/}"
  if [[ -z "${BWRAP_RUNTIME_BIND_SOURCES[$ROCQ_ELF_INTERPRETER]+set}" ]]; then
    BWRAP_RUNTIME_BIND_SOURCES["$ROCQ_ELF_INTERPRETER"]=\
"$OSLIBDIR/${ROCQ_ELF_INTERPRETER_SOURCE##*/}"
    BWRAP_RUNTIME_BIND_ARGS+=(
      --ro-bind "$OSLIBDIR/${ROCQ_ELF_INTERPRETER_SOURCE##*/}" "$ROCQ_ELF_INTERPRETER"
    )
  fi
  ROCQ_ELF_INTERPRETER_DIR="$CHECKDIR/elf-interpreter"
  mkdir -p "$ROCQ_ELF_INTERPRETER_DIR"
  for dependency in "${!BWRAP_RUNTIME_BIND_SOURCES[@]}"; do
    if [[ "$(dirname "$dependency")" == "$(dirname "$ROCQ_ELF_INTERPRETER")" ]]; then
      install -m 555 \
        "${BWRAP_RUNTIME_BIND_SOURCES[$dependency]}" \
        "$ROCQ_ELF_INTERPRETER_DIR/${dependency##*/}"
    fi
  done
  BWRAP_ELF_INTERPRETER="$({
    readelf -l "$BWRAP_BIN" | awk -F': ' '/Requesting program interpreter/ {
      value=$2; sub(/]$/, "", value); print value; exit
    }'
  })"
  if [[ "$BWRAP_ELF_INTERPRETER" != "$ROCQ_ELF_INTERPRETER" ]]; then
    echo "Rocq and bwrap use different ELF interpreters" >&2
    trusted_environment_failure "bwrap-runtime-library" 127
  fi
  STAGED_ELF_INTERPRETER="$ROCQ_ELF_INTERPRETER_DIR/${ROCQ_ELF_INTERPRETER##*/}"
  if [[ ! -s "$STAGED_ELF_INTERPRETER" || ! -x "$STAGED_ELF_INTERPRETER" ]]; then
    echo "staged outer ELF interpreter is missing" >&2
    trusted_environment_failure "bwrap-runtime-library" 127
  fi
}

publish_checker_runtime_cache() {
  local bundle="$1" stage dependency directory source staged
  bundle="$SHARED_CHECKER_RUNTIME_CACHE_ROOT/$CHECKER_RUNTIME_CACHE_KEY"
  [[ ! -e "$bundle" && ! -L "$bundle" ]] || return 0
  stage="$(mktemp -d "$SHARED_CHECKER_RUNTIME_CACHE_ROOT/.${CHECKER_RUNTIME_CACHE_KEY}.XXXXXX")"
  mkdir "$stage/rocq-bin" "$stage/elf-interpreter" "$stage/os-libs"
  install -m 555 "$ROCQBINDIR/rocq" "$stage/rocq-bin/rocq"
  install -m 555 "$STAGED_ELF_INTERPRETER" \
    "$stage/elf-interpreter/${ROCQ_ELF_INTERPRETER##*/}"
  for source in "$OSLIBDIR"/*; do
    [[ -f "$source" && ! -L "$source" ]] || continue
    install -m 444 "$source" "$stage/os-libs/${source##*/}"
  done
  printf '%s\n' "$CHECKER_RUNTIME_CACHE_KEY" >"$stage/INPUT-KEY"
  printf '%s\n' "$ROCQ_ELF_INTERPRETER" >"$stage/INTERPRETER"
  for directory in "${!BWRAP_RUNTIME_DIRS[@]}"; do
    printf '%s\n' "$directory"
  done | LC_ALL=C sort >"$stage/DIRECTORIES"
  for dependency in "${!BWRAP_RUNTIME_BIND_SOURCES[@]}"; do
    source="${BWRAP_RUNTIME_BIND_SOURCES[$dependency]}"
    staged="${source##*/}"
    printf '%s\t%s\n' "$dependency" "$staged"
  done | LC_ALL=C sort >"$stage/BINDINGS"
  chmod 444 "$stage/INPUT-KEY" "$stage/INTERPRETER" \
    "$stage/DIRECTORIES" "$stage/BINDINGS"
  write_checker_runtime_digests "$stage" SHA256SUMS
  chmod 444 "$stage/SHA256SUMS"
  chmod 555 "$stage/rocq-bin" "$stage/elf-interpreter" "$stage/os-libs" "$stage"
  if ! mv -T "$stage" "$bundle" 2>/dev/null; then
    chmod -R u+w "$stage" 2>/dev/null || true
    rm -rf -- "$stage"
  fi
}

CHECKER_RUNTIME_CACHE_KEY="$(checker_runtime_input_key)"
if [[ -n "$SHARED_CHECKER_RUNTIME_CACHE_ROOT" ]]; then
  CHECKER_RUNTIME_LOCK="$SHARED_CHECKER_RUNTIME_CACHE_ROOT/.${CHECKER_RUNTIME_CACHE_KEY}.lock"
  exec {CHECKER_RUNTIME_LOCK_FD}>"$CHECKER_RUNTIME_LOCK"
  flock "$CHECKER_RUNTIME_LOCK_FD"
  if ! load_checker_runtime_cache \
      "$SHARED_CHECKER_RUNTIME_CACHE_ROOT/$CHECKER_RUNTIME_CACHE_KEY"; then
    stage_checker_runtime
    publish_checker_runtime_cache \
      "$SHARED_CHECKER_RUNTIME_CACHE_ROOT/$CHECKER_RUNTIME_CACHE_KEY"
    BWRAP_RUNTIME_DIRS=()
    BWRAP_RUNTIME_BIND_SOURCES=()
    BWRAP_RUNTIME_DIR_ARGS=()
    BWRAP_RUNTIME_BIND_ARGS=()
    load_checker_runtime_cache \
      "$SHARED_CHECKER_RUNTIME_CACHE_ROOT/$CHECKER_RUNTIME_CACHE_KEY"
  fi
  flock -u "$CHECKER_RUNTIME_LOCK_FD"
  exec {CHECKER_RUNTIME_LOCK_FD}>&-
else
  stage_checker_runtime
fi

BWRAP_LAUNCH=(
  "$STAGED_ELF_INTERPRETER"
  --library-path "$ROCQ_INSTALL_PREFIX/lib:$OSLIBDIR"
  "$BWRAP_BIN"
)
fi

# The ordered Logos entries are exhaustively checked against the structured
# Rust trusted-theory registry by proof-stage unit tests.
for file in \
  "$LOGOS_REPO_ROOT/vendor/FormalSQL/src/data/proof_of_concept/SqlSyntax.vo" \
  "$LOGOS_REPO_ROOT/vendor/FormalSQL/src/data/proof_of_concept/GenericInstance.vo" \
  "$LOGOS_REPO_ROOT/vendor/FormalSQL/src/data/proof_of_concept/SchemaConstraints.vo" \
  "$LOGOS_REPO_ROOT/vendor/FormalSQL/src/data/sql/SqlOutcome.vo" \
  "$LOGOS_REPO_ROOT/vendor/FormalSQL/src/data/sql/SqlErrorSemantics.vo" \
  "$LOGOS_REPO_ROOT/vendor/FormalSQL/src/data/sql/SqlOrder.vo" \
  "$LOGOS_REPO_ROOT/vendor/FormalSQL/src/data/sql/SqlListFacts.vo" \
  "$LOGOS_REPO_ROOT/vendor/FormalSQL/src/data/sql/SqlQuerySyntax.vo" \
  "$LOGOS_REPO_ROOT/vendor/FormalSQL/src/data/sql/SqlQuerySemantics.vo" \
  "$LOGOS_REPO_ROOT/vendor/FormalSQL/src/data/sql/SqlBagAbstraction.vo" \
  "$LOGOS_REPO_ROOT/vendor/FormalSQL/src/data/sql/SqlRenameFacts.vo" \
  "$LOGOS_REPO_ROOT/vendor/FormalSQL/src/data/sql/SqlQueryFacts.vo" \
  "$LOGOS_REPO_ROOT/vendor/FormalSQL/src/data/sql/SqlQueryContexts.vo" \
  "$LOGOS_REPO_ROOT/vendor/FormalSQL/src/data/sql/SqlQueryRenameTransport.vo" \
  "$LOGOS_REPO_ROOT/vendor/FormalSQL/src/data/sql/SqlQueryWellFormed.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/TNullSyntax.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/VerificationConditions.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/SchemaCardinality.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/QueryCardinality.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/QueryTNullSyntax.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/NumericFacts.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/BitwiseFacts.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/CardinalityCombinators.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/IntegrityFacts.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/ScalarPredicateFacts.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/StringTemporalFacts.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/NumericDerivedFacts.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/GroupingRewriteFacts.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/AggregateRuntimeFacts.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/RelationalAlgebraFacts.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/OuterJoinFilterFacts.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/GroupedFilterOutcomeFacts.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/SemijoinCompositionFacts.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/NumericRegroupFacts.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/OrderedQueryFacts.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/OrderedObservationTransportFacts.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/RenameTransportFacts.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/PossibleOutcomeFacts.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/ProofAgentFacade.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/SubqueryFacts.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/MembershipCompositionFacts.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/WitnessFacts.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/CountermodelFacts.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/AggregateOutcomeBridgeFacts.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/CorrelatedMembershipFacts.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/MembershipJoinCompositionFacts.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/FilterFkEliminationFacts.vo" \
  "$LOGOS_REPO_ROOT/theories/FormalSQL/QueryBindingSemantics.vo"; do
  if [[ ! -s "$file" ]]; then
    echo "missing or empty trusted Rocq object: $file" >&2
    echo "run 'make logos-formal-sql-lemmas' in LOGOS_REPO_ROOT before proof checking" >&2
    trusted_environment_failure "trusted-object" 2
  fi
  if [[ -L "$file" ]]; then
    echo "refusing symlinked trusted Rocq object: $file" >&2
    echo "run 'make logos-formal-sql-lemmas' in LOGOS_REPO_ROOT before proof checking" >&2
    trusted_environment_failure "trusted-object" 2
  fi
done

declare -a PROOF_MODULE_ORDER=()

validate_trusted_cache() {
  local expected_manifest entry file stem
  local -A ordered=()

  if [[ -L "$TRUSTED_CACHE" || ! -d "$TRUSTED_CACHE" ]]; then
    echo "trusted diagnostic cache is missing or symlinked: $TRUSTED_CACHE" >&2
    trusted_environment_failure "diagnostic-cache" 2
  fi
  for entry in Schema.v Schema.vo Queries.v Queries.vo Witness.v Witness.vo SHA256SUMS; do
    if [[ ! -s "$TRUSTED_CACHE/$entry" || -L "$TRUSTED_CACHE/$entry" ]]; then
      echo "trusted diagnostic cache entry is missing, empty, or symlinked: $entry" >&2
      trusted_environment_failure "diagnostic-cache" 2
    fi
  done
  if [[ ! -d "$TRUSTED_CACHE/ProofModules" || -L "$TRUSTED_CACHE/ProofModules" ||
        ! -f "$TRUSTED_CACHE/ProofModules/ORDER" || -L "$TRUSTED_CACHE/ProofModules/ORDER" ]]; then
    echo "trusted diagnostic cache has no safe ProofModules order manifest" >&2
    trusted_environment_failure "diagnostic-module-cache" 2
  fi

  PROOF_MODULE_ORDER=()
  while IFS= read -r file || [[ -n "$file" ]]; do
    [[ -n "$file" ]] || continue
    if [[ ! "$file" =~ ^[A-Z][A-Za-z0-9_]*\.v$ || -n "${ordered[$file]+set}" ]]; then
      echo "trusted module order contains an invalid or duplicate entry: $file" >&2
      trusted_environment_failure "diagnostic-module-order" 2
    fi
    stem="${file%.v}"
    for entry in "$file" "$stem.vo"; do
      if [[ ! -s "$TRUSTED_CACHE/ProofModules/$entry" ||
            -L "$TRUSTED_CACHE/ProofModules/$entry" ]]; then
        echo "trusted module cache entry is missing, empty, or symlinked: $entry" >&2
        trusted_environment_failure "diagnostic-module-cache" 2
      fi
    done
    ordered["$file"]=1
    ordered["$stem.vo"]=1
    PROOF_MODULE_ORDER+=("$file")
  done <"$TRUSTED_CACHE/ProofModules/ORDER"

  while IFS= read -r -d '' entry; do
    file="${entry#"$TRUSTED_CACHE/ProofModules/"}"
    if [[ "$file" != ORDER && -z "${ordered[$file]+set}" ]]; then
      echo "trusted module cache contains an unordered entry: $file" >&2
      trusted_environment_failure "diagnostic-module-cache" 2
    fi
  done < <(find "$TRUSTED_CACHE/ProofModules" -mindepth 1 -maxdepth 1 -print0)
  if [[ -n "$(find "$TRUSTED_CACHE" -mindepth 1 -maxdepth 1 \
      ! -name Schema.v ! -name Schema.vo ! -name Queries.v ! -name Queries.vo \
      ! -name Witness.v ! -name Witness.vo ! -name SHA256SUMS \
      ! -name ProofModules -print -quit)" ]]; then
    echo "trusted diagnostic cache contains an unexpected root entry" >&2
    trusted_environment_failure "diagnostic-cache" 2
  fi

  expected_manifest="$(
    cd "$TRUSTED_CACHE"
    {
      sha256sum Schema.v Schema.vo Queries.v Queries.vo Witness.v Witness.vo ProofModules/ORDER
      for file in "${PROOF_MODULE_ORDER[@]}"; do
        stem="${file%.v}"
        sha256sum "ProofModules/$file" "ProofModules/$stem.vo"
      done
    }
  )"
  if [[ "$(cat "$TRUSTED_CACHE/SHA256SUMS")" != "$expected_manifest" ]]; then
    echo "trusted diagnostic cache digest manifest is invalid" >&2
    trusted_environment_failure "diagnostic-cache-digest" 2
  fi
  if ! cmp -s "$WORKDIR/Schema.v" "$TRUSTED_CACHE/Schema.v" ||
     ! cmp -s "$WORKDIR/Queries.v" "$TRUSTED_CACHE/Queries.v" ||
     { [[ "$mode" != witness-preflight ]] &&
       ! cmp -s "$WORKDIR/Witness.v" "$TRUSTED_CACHE/Witness.v"; }; then
    echo "trusted diagnostic cache source binding drifted" >&2
    trusted_environment_failure "diagnostic-cache-source" 2
  fi
}

copy_trusted_cache() {
  local destination="$1" file stem
  mkdir -p "$destination/ProofModules"
  chmod 700 "$destination/ProofModules"
  install -m 600 \
    "$TRUSTED_CACHE/Schema.v" "$TRUSTED_CACHE/Schema.vo" \
    "$TRUSTED_CACHE/Queries.v" "$TRUSTED_CACHE/Queries.vo" \
    "$TRUSTED_CACHE/Witness.v" "$TRUSTED_CACHE/Witness.vo" \
    "$destination/"
  install -m 600 "$TRUSTED_CACHE/ProofModules/ORDER" "$destination/ProofModules/ORDER"
  for file in "${PROOF_MODULE_ORDER[@]}"; do
    stem="${file%.v}"
    install -m 600 \
      "$TRUSTED_CACHE/ProofModules/$file" \
      "$TRUSTED_CACHE/ProofModules/$stem.vo" \
      "$destination/ProofModules/"
  done
}

copy_trusted_cache_objects() {
  local destination="$1" file stem
  mkdir -p "$destination/ProofModules"
  chmod 700 "$destination/ProofModules"
  install -m 600 \
    "$TRUSTED_CACHE/Schema.vo" \
    "$TRUSTED_CACHE/Queries.vo" \
    "$TRUSTED_CACHE/Witness.vo" \
    "$destination/"
  for file in "${PROOF_MODULE_ORDER[@]}"; do
    stem="${file%.v}"
    install -m 600 \
      "$TRUSTED_CACHE/ProofModules/$stem.vo" \
      "$destination/ProofModules/"
  done
}

discard_problem_cache() {
  if [[ -e "$PROBLEM_CACHE" || -L "$PROBLEM_CACHE" ]]; then
    if [[ ! -d "$PROBLEM_CACHE" || -L "$PROBLEM_CACHE" ]]; then
      echo "problem compile cache is unsafe: $PROBLEM_CACHE" >&2
      trusted_environment_failure "problem-cache" 2
    fi
    rm -rf -- "$PROBLEM_CACHE" \
      || trusted_environment_failure "problem-cache" "$?"
  fi
}

publish_problem_cache() {
  local stage cache_manifest_sha256
  stage="$(mktemp -d "$CACHE_PARENT/.logos-problem-compile-cache.XXXXXX")"
  chmod 700 "$stage"
  cache_manifest_sha256="$(sha256sum "$TRUSTED_CACHE/SHA256SUMS" | awk '{print $1}')"
  install -m 600 "$WORKDIR/Problem.v" "$PROBLEMOUTDIR/Problem.vo" "$stage/"
  printf '%s\n' "$cache_manifest_sha256" >"$stage/PREFIX-SHA256"
  (
    cd "$stage"
    sha256sum Problem.v Problem.vo PREFIX-SHA256 >SHA256SUMS
  )
  discard_problem_cache
  mv -T "$stage" "$PROBLEM_CACHE" \
    || trusted_environment_failure "problem-cache-publish" "$?"
}

reuse_problem_cache() {
  local expected_manifest cache_manifest_sha256
  [[ -d "$PROBLEM_CACHE" && ! -L "$PROBLEM_CACHE" ]] || return 1
  for entry in Problem.v Problem.vo PREFIX-SHA256 SHA256SUMS; do
    if [[ ! -s "$PROBLEM_CACHE/$entry" || -L "$PROBLEM_CACHE/$entry" ]]; then
      echo "problem compile cache entry is unsafe: $entry" >&2
      trusted_environment_failure "problem-cache" 2
    fi
  done
  expected_manifest="$(cd "$PROBLEM_CACHE" && sha256sum Problem.v Problem.vo PREFIX-SHA256)"
  if [[ "$(cat "$PROBLEM_CACHE/SHA256SUMS")" != "$expected_manifest" ]] ||
     ! cmp -s "$WORKDIR/Problem.v" "$PROBLEM_CACHE/Problem.v"; then
    echo "problem compile cache source/object binding drifted" >&2
    trusted_environment_failure "problem-cache" 2
  fi
  cache_manifest_sha256="$(sha256sum "$TRUSTED_CACHE/SHA256SUMS" | awk '{print $1}')"
  if [[ "$(cat "$PROBLEM_CACHE/PREFIX-SHA256")" != "$cache_manifest_sha256" ]]; then
    return 1
  fi
  install -m 600 "$PROBLEM_CACHE/Problem.vo" "$PROBLEMOUTDIR/Problem.vo"
  echo "LOGOS_TRUSTED_ROCQ_PROBLEM_CACHE hit=true" >&2
  return 0
}

write_cache_manifest() {
  local cache="$1" file stem
  (
    cd "$cache"
    {
      sha256sum Schema.v Schema.vo Queries.v Queries.vo Witness.v Witness.vo ProofModules/ORDER
      while IFS= read -r file || [[ -n "$file" ]]; do
        [[ -n "$file" ]] || continue
        stem="${file%.v}"
        sha256sum "ProofModules/$file" "ProofModules/$stem.vo"
      done <ProofModules/ORDER
    } >SHA256SUMS
    chmod 600 SHA256SUMS
  )
}

shared_prefix_key() {
  {
    printf '%s\n' "$SHARED_AUTHORITY_SHA256"
    sha256sum "$WORKDIR/Schema.v" "$WORKDIR/Queries.v" "$WORKDIR/Witness.v"
  } | sha256sum | awk '{print $1}'
}

validate_shared_prefix_bundle() {
  local bundle="$1" expected
  if [[ ! -d "$bundle" || -L "$bundle" ||
        "$(stat -c '%a' "$bundle")" != 555 ]]; then
    return 1
  fi
  for entry in Schema.v Schema.vo Queries.v Queries.vo Witness.v Witness.vo SHA256SUMS; do
    if [[ ! -s "$bundle/$entry" || -L "$bundle/$entry" ||
          "$(stat -c '%a' "$bundle/$entry")" != 444 ]]; then
      echo "shared generated-prefix cache entry is unsafe: $bundle/$entry" >&2
      trusted_environment_failure "shared-prefix-cache" 2
    fi
  done
  expected="$(cd "$bundle" && sha256sum Schema.v Schema.vo Queries.v Queries.vo Witness.v Witness.vo)"
  if [[ "$(cat "$bundle/SHA256SUMS")" != "$expected" ]] ||
     ! cmp -s "$WORKDIR/Schema.v" "$bundle/Schema.v" ||
     ! cmp -s "$WORKDIR/Queries.v" "$bundle/Queries.v" ||
     ! cmp -s "$WORKDIR/Witness.v" "$bundle/Witness.v"; then
    echo "shared generated-prefix cache digest/source binding drifted" >&2
    trusted_environment_failure "shared-prefix-cache" 2
  fi
}

try_shared_prefix_cache() {
  local bundle
  [[ -n "$SHARED_PREFIX_CACHE_ROOT" ]] || return 1
  SHARED_PREFIX_KEY="$(shared_prefix_key)"
  bundle="$SHARED_PREFIX_CACHE_ROOT/$SHARED_PREFIX_KEY"
  validate_shared_prefix_bundle "$bundle" || return 1
  install -m 600 \
    "$bundle/Schema.v" "$bundle/Schema.vo" \
    "$bundle/Queries.v" "$bundle/Queries.vo" \
    "$bundle/Witness.v" "$bundle/Witness.vo" \
    "$TRUSTEDDIR/"
  SHARED_PREFIX_HIT=true
  echo "LOGOS_TRUSTED_ROCQ_PREFIX_CACHE hit=true key=$SHARED_PREFIX_KEY" >&2
  return 0
}

publish_shared_prefix_cache() {
  local bundle stage
  [[ -n "$SHARED_PREFIX_CACHE_ROOT" ]] || return 0
  [[ -n "$SHARED_PREFIX_KEY" ]] || SHARED_PREFIX_KEY="$(shared_prefix_key)"
  bundle="$SHARED_PREFIX_CACHE_ROOT/$SHARED_PREFIX_KEY"
  if [[ -e "$bundle" || -L "$bundle" ]]; then
    validate_shared_prefix_bundle "$bundle"
    return 0
  fi
  stage="$(mktemp -d "$SHARED_PREFIX_CACHE_ROOT/.${SHARED_PREFIX_KEY}.XXXXXX")"
  install -m 444 \
    "$TRUSTEDDIR/Schema.v" "$TRUSTEDDIR/Schema.vo" \
    "$TRUSTEDDIR/Queries.v" "$TRUSTEDDIR/Queries.vo" \
    "$TRUSTEDDIR/Witness.v" "$TRUSTEDDIR/Witness.vo" \
    "$stage/"
  (cd "$stage" && sha256sum Schema.v Schema.vo Queries.v Queries.vo Witness.v Witness.vo >SHA256SUMS)
  chmod 444 "$stage/SHA256SUMS"
  chmod 555 "$stage"
  if ! mv -T "$stage" "$bundle" 2>/dev/null; then
    chmod 700 "$stage" 2>/dev/null || true
    rm -rf -- "$stage"
    validate_shared_prefix_bundle "$bundle"
  fi
}

validate_final_workspace_modules() {
  local module_root="$WORKDIR/ProofModules" entry file
  local -A expected=()
  for file in "${PROOF_MODULE_ORDER[@]}"; do expected["$file"]=1; done
  if [[ ! -e "$module_root" ]]; then
    if ((${#PROOF_MODULE_ORDER[@]} == 0)); then return 0; fi
    echo "final workspace is missing checked ProofModules" >&2
    trusted_environment_failure "final-module-source" 2
  fi
  if [[ ! -d "$module_root" || -L "$module_root" ]]; then
    echo "final ProofModules path is not a real directory" >&2
    trusted_environment_failure "final-module-source" 2
  fi
  while IFS= read -r -d '' entry; do
    file="${entry#"$module_root/"}"
    if [[ "$file" == "$entry" || "$file" == */* ||
          ! "$file" =~ ^[A-Z][A-Za-z0-9_]*\.v$ ||
          ! -f "$entry" || -L "$entry" || -z "${expected[$file]+set}" ]]; then
      echo "final workspace contains an unchecked proof module entry: $entry" >&2
      trusted_environment_failure "final-module-source" 2
    fi
  done < <(find "$module_root" -mindepth 1 -print0)
  for file in "${PROOF_MODULE_ORDER[@]}"; do
    if [[ ! -f "$module_root/$file" || -L "$module_root/$file" ]] ||
       ! cmp -s "$module_root/$file" "$TRUSTED_CACHE/ProofModules/$file"; then
      echo "final workspace proof module differs from its checked cache source: $file" >&2
      trusted_environment_failure "final-module-source" 2
    fi
  done
}

cp "$WORKDIR/Problem.v" "$PROBLEMDIR/"

if [[ "$mode" != preflight ]]; then
  validate_trusted_cache
  # Only a fully manifest/source-validated live cache can supersede retained
  # crash-recovery backups. Removing them here prevents two interrupted swaps
  # from accumulating ambiguous old-cache candidates.
  discard_superseded_cache_backups
  if [[ "$mode" == witness-preflight ]]; then
    if ! try_shared_prefix_cache; then
      cp "$TRUSTED_CACHE/Schema.v" "$TRUSTED_CACHE/Schema.vo" \
        "$TRUSTED_CACHE/Queries.v" "$TRUSTED_CACHE/Queries.vo" "$TRUSTEDDIR/"
      cp "$WORKDIR/Witness.v" "$TRUSTEDDIR/"
      "$ROCQ_BIN" compile -q -coqlib "$ROCQ_STDLIB_DIR" \
        -Q "$LOGOS_REPO_ROOT/vendor/FormalSQL/src" SQLFS \
        -Q "$LOGOS_REPO_ROOT/theories" Logos \
        -Q "$TRUSTEDDIR" LogosGenerated \
        "$TRUSTEDDIR/Witness.v" || trusted_environment_failure "witness" "$?"
    fi
  elif [[ "$mode" == problem-diagnostic ]]; then
    cp "$TRUSTED_CACHE/Schema.vo" "$TRUSTED_CACHE/Queries.vo" \
      "$TRUSTED_CACHE/Witness.vo" "$PROBLEMOUTDIR/"
    for file in "${PROOF_MODULE_ORDER[@]}"; do
      stem="${file%.v}"
      cp "$TRUSTED_CACHE/ProofModules/$stem.vo" "$PROBLEMOUTDIR/ProofModules/"
    done
  elif [[ "$mode" == module-diagnostic ]]; then
    candidate_name="${module_candidate#ProofModules/}"
    candidate_stem="${candidate_name%.v}"
    if [[ ! -f "$WORKDIR/$module_candidate" || -L "$WORKDIR/$module_candidate" ]]; then
      echo "module diagnostic candidate is missing or symlinked: $module_candidate" >&2
      trusted_environment_failure "diagnostic-module-source" 2
    fi
    if [[ -e "$TRUSTED_CACHE/ProofModules/$candidate_name" ]]; then
      if ! cmp -s "$WORKDIR/$module_candidate" "$TRUSTED_CACHE/ProofModules/$candidate_name"; then
        echo "refusing to replace immutable checked proof module: $candidate_name" >&2
        exit 65
      fi
      echo "LOGOS_TRUSTED_ROCQ_CHECK mode=module-diagnostic candidate=$module_candidate already_cached=true" >&2
      exit 0
    fi
    CACHE_STAGE="$(mktemp -d "$CACHE_PARENT/.logos-trusted-diagnostic-cache.XXXXXX")"
    chmod 700 "$CACHE_STAGE"
    copy_trusted_cache "$CACHE_STAGE"
    copy_trusted_cache_objects "$PROBLEMOUTDIR"
    install -m 600 "$WORKDIR/$module_candidate" "$PROBLEMDIR/ProofModules/$candidate_name"
  else
    # The cache is host-created only after preflight kernel-checks these exact
    # generated sources and objects, is digest-bound, and is never mounted into
    # the agent. Reuse the checked prefix for final proof assembly.
    cp "$TRUSTED_CACHE/Schema.v" "$TRUSTED_CACHE/Schema.vo" \
      "$TRUSTED_CACHE/Queries.v" "$TRUSTED_CACHE/Queries.vo" \
      "$TRUSTED_CACHE/Witness.v" "$TRUSTED_CACHE/Witness.vo" "$TRUSTEDDIR/"
    validate_final_workspace_modules
  fi
else
  if ! try_shared_prefix_cache; then
    cp "$WORKDIR/Schema.v" "$WORKDIR/Queries.v" "$WORKDIR/Witness.v" "$TRUSTEDDIR/"

    "$ROCQ_BIN" compile -q -coqlib "$ROCQ_STDLIB_DIR" \
      -Q "$LOGOS_REPO_ROOT/vendor/FormalSQL/src" SQLFS \
      -Q "$LOGOS_REPO_ROOT/theories" Logos \
      -Q "$TRUSTEDDIR" LogosGenerated \
      "$TRUSTEDDIR/Schema.v" || trusted_environment_failure "schema" "$?"

    "$ROCQ_BIN" compile -q -coqlib "$ROCQ_STDLIB_DIR" \
      -Q "$LOGOS_REPO_ROOT/vendor/FormalSQL/src" SQLFS \
      -Q "$LOGOS_REPO_ROOT/theories" Logos \
      -Q "$TRUSTEDDIR" LogosGenerated \
      "$TRUSTEDDIR/Queries.v" || trusted_environment_failure "queries" "$?"

    "$ROCQ_BIN" compile -q -coqlib "$ROCQ_STDLIB_DIR" \
      -Q "$LOGOS_REPO_ROOT/vendor/FormalSQL/src" SQLFS \
      -Q "$LOGOS_REPO_ROOT/theories" Logos \
      -Q "$TRUSTEDDIR" LogosGenerated \
      "$TRUSTEDDIR/Witness.v" || trusted_environment_failure "witness" "$?"
  fi
fi

if [[ "$mode" == preflight || "$mode" == witness-preflight ]]; then
  # Schema, Queries, and Witness are case-generated and therefore never enter
  # the manifest-bound trusted dependency exception. Check every generated module
  # explicitly; checking only the final/root module with [-norec] would admit
  # these generated dependencies and would be unsound.
  PREFLIGHT_CONTEXT="$CHECKDIR/rocq-check-generated-preflight-context.txt"
  "$ROCQ_BIN" check -silent -o -coqlib "$ROCQ_STDLIB_DIR" \
    -Q "$LOGOS_REPO_ROOT/vendor/FormalSQL/src" SQLFS \
    -Q "$LOGOS_REPO_ROOT/theories" Logos \
    -Q "$TRUSTEDDIR" LogosGenerated \
    -norec LogosGenerated.Schema \
    -norec LogosGenerated.Queries \
    -norec LogosGenerated.Witness >"$PREFLIGHT_CONTEXT" 2>&1 \
    || {
      status="$?"
      cat "$PREFLIGHT_CONTEXT" >&2
      trusted_environment_failure "generated-preflight-kernel-check" "$status"
    }
  if grep -Eq '^[[:space:]]+LogosGenerated\.' "$PREFLIGHT_CONTEXT"; then
    echo "generated preflight module depends on an untrusted axiom" >&2
    cat "$PREFLIGHT_CONTEXT" >&2
    trusted_environment_failure "generated-preflight-assumption" 3
  fi
  for required in \
    '* Theory: Set is predicative' \
    '* Theory: Rewrite rules are not allowed' \
    '* Constants/Inductives relying on type-in-type: <none>' \
    '* Constants/Inductives relying on unsafe (co)fixpoints: <none>' \
    '* Inductives whose positivity is assumed: <none>'; do
    if ! grep -Fq -- "$required" "$PREFLIGHT_CONTEXT"; then
      echo "generated preflight uses an unsafe Rocq kernel setting: $required" >&2
      trusted_environment_failure "generated-preflight-kernel-setting" 3
    fi
  done

  if [[ "$SHARED_PREFIX_HIT" != true ]]; then
    publish_shared_prefix_cache
  fi

  if [[ "$mode" == preflight ]] && \
     [[ -e "$TRUSTED_CACHE" || -L "$TRUSTED_CACHE" ]]; then
    echo "refusing to replace a pre-existing trusted diagnostic cache: $TRUSTED_CACHE" >&2
    trusted_environment_failure "diagnostic-cache-preexisting" 2
  fi

  # Preflight owns only the generated, agent-immutable dependency prefix.
  # Publish it now and leave Problem.v to the immediately following
  # problem-diagnostic checkpoint.  Compiling the same generated scaffold in
  # both phases used to duplicate the most expensive mutable-module work for
  # every case without adding an independent trust boundary.
  CACHE_STAGE="$(mktemp -d "$CACHE_PARENT/.logos-trusted-diagnostic-cache.XXXXXX")"
  chmod 700 "$CACHE_STAGE"
  mkdir -m 700 "$CACHE_STAGE/ProofModules"
  install -m 600 \
    "$TRUSTEDDIR/Schema.v" "$TRUSTEDDIR/Schema.vo" \
    "$TRUSTEDDIR/Queries.v" "$TRUSTEDDIR/Queries.vo" \
    "$TRUSTEDDIR/Witness.v" "$TRUSTEDDIR/Witness.vo" \
    "$CACHE_STAGE/"
  install -m 600 /dev/null "$CACHE_STAGE/ProofModules/ORDER"
  write_cache_manifest "$CACHE_STAGE"
  if [[ "$mode" == witness-preflight ]]; then
    CACHE_OLD="$(mktemp -d "$CACHE_PARENT/.logos-trusted-diagnostic-cache-old.XXXXXX")"
    rm -rf -- "$CACHE_OLD"
    mv -T "$TRUSTED_CACHE" "$CACHE_OLD" \
      || trusted_environment_failure "diagnostic-cache-publish" "$?"
    if ! mv -T "$CACHE_STAGE" "$TRUSTED_CACHE"; then
      status="$?"
      mv -T "$CACHE_OLD" "$TRUSTED_CACHE" || true
      trusted_environment_failure "diagnostic-cache-publish" "$status"
    fi
    rm -rf -- "$CACHE_OLD"
    CACHE_OLD=
    discard_problem_cache
  else
    mv -T "$CACHE_STAGE" "$TRUSTED_CACHE" \
      || trusted_environment_failure "diagnostic-cache-publish" "$?"
  fi
  CACHE_STAGE=
  exit 0
fi

# Every agent-controlled module is compiled in the same empty-root sandbox.
# Only the output directory's already checked .vo prefix is visible through the
# LogosGenerated logical root. Source files are read-only and cannot replace a
# prior object while the compiler runs.
sandbox_compile() {
  local input_root="$1"
  local output_root="$2"
  local source_relative="$3"
  local logical_name="$4"
  local output_relative="$5"
  mkdir -p \
    "$(dirname "$output_root/$output_relative")" \
    "$output_root/tmp" \
    "$output_root/xdg-data-home" \
    "$output_root/xdg-data-dirs" \
    "$output_root/xdg-config" \
    "$output_root/xdg-cache"
  "${BWRAP_LAUNCH[@]}" \
    --die-with-parent \
    --new-session \
    --unshare-all \
    --unshare-user \
    --disable-userns \
    --assert-userns-disabled \
    --tmpfs / \
    --dir /rocq \
    --dir /rocq/bin \
    --dir /rocq/lib \
    --dir /authority \
    "${BWRAP_RUNTIME_DIR_ARGS[@]}" \
    --ro-bind "$ROCQBINDIR" /rocq/bin \
    --ro-bind "$ROCQ_RUNTIME_DIR" /rocq/lib/rocq-runtime \
    --ro-bind "$ROCQ_STDLIB_DIR" /rocq/lib/coq \
    --ro-bind "$ROCQ_STUBLIBS_DIR" /rocq/lib/stublibs \
    --ro-bind "$ROCQ_OCAML_DIR" /rocq/lib/ocaml \
    --ro-bind "$ROCQ_FINDLIB_DIR" /rocq/lib/findlib \
    --ro-bind "$ROCQ_ZARITH_DIR" /rocq/lib/zarith \
    --ro-bind "$ROCQ_SANDBOX_FINDLIB_CONF" /rocq/lib/findlib.conf \
    --ro-bind "$AUTHORITYDIR" /authority \
    "${BWRAP_RUNTIME_BIND_ARGS[@]}" \
    --ro-bind "$ROCQ_ELF_INTERPRETER_DIR" "$(dirname "$ROCQ_ELF_INTERPRETER")" \
    --ro-bind "$input_root" /input \
    --bind "$output_root" /out \
    --chdir /out \
    --clearenv \
    --setenv PATH /rocq/bin \
    --setenv HOME /out \
    --setenv TMPDIR /out/tmp \
    --setenv LC_ALL C \
    --setenv LANG C \
    --setenv XDG_DATA_HOME /out/xdg-data-home \
    --setenv XDG_DATA_DIRS /out/xdg-data-dirs \
    --setenv XDG_CONFIG_HOME /out/xdg-config \
    --setenv XDG_CACHE_HOME /out/xdg-cache \
    --setenv ROCQLIB /rocq/lib/coq \
    --setenv COQLIB /rocq/lib/coq \
    --setenv OCAMLLIB /rocq/lib/ocaml \
    --setenv CAMLLIB /rocq/lib/ocaml \
    --setenv OCAMLFIND_CONF /rocq/lib/findlib.conf \
    --setenv CAML_LD_LIBRARY_PATH /rocq/lib/stublibs:/rocq/lib/ocaml/stublibs \
    --setenv LD_LIBRARY_PATH /rocq/lib/stublibs:/rocq/lib/ocaml/stublibs \
    /rocq/bin/rocq compile -q -noglob -top "$logical_name" \
      -o "/out/$output_relative" \
      -coqlib /rocq/lib/coq \
      -Q /authority/vendor/FormalSQL/src SQLFS \
      -Q /authority/theories Logos \
      -Q /out LogosGenerated \
      "/input/$source_relative"
}

if [[ "$mode" == module-diagnostic ]]; then
  sandbox_compile \
    "$PROBLEMDIR" "$PROBLEMOUTDIR" "$module_candidate" \
    "LogosGenerated.ProofModules.$candidate_stem" \
    "ProofModules/$candidate_stem.vo"
  install -m 600 \
    "$PROBLEMDIR/ProofModules/$candidate_name" \
    "$CACHE_STAGE/ProofModules/$candidate_name"
  install -m 600 \
    "$PROBLEMOUTDIR/ProofModules/$candidate_stem.vo" \
    "$CACHE_STAGE/ProofModules/$candidate_stem.vo"
  printf '%s\n' "$candidate_name" >>"$CACHE_STAGE/ProofModules/ORDER"
  write_cache_manifest "$CACHE_STAGE"
  discard_problem_cache

  CACHE_OLD="$(mktemp -d "$CACHE_PARENT/.logos-trusted-diagnostic-cache-old.XXXXXX")"
  rm -rf -- "$CACHE_OLD"
  mv -T "$TRUSTED_CACHE" "$CACHE_OLD" \
    || trusted_environment_failure "diagnostic-module-cache-publish" "$?"
  if mv -T "$CACHE_STAGE" "$TRUSTED_CACHE"; then
    CACHE_PUBLISHED=true
  else
    status="$?"
    trusted_environment_failure "diagnostic-module-cache-publish" "$status"
  fi
  CACHE_STAGE=
  rm -rf -- "$CACHE_OLD"
  CACHE_OLD=
  echo "LOGOS_TRUSTED_ROCQ_CHECK mode=module-diagnostic candidate=$module_candidate requested_timeout_seconds=$requested_timeout_seconds" >&2
  exit 0
fi

if [[ "$mode" == final ]]; then
  # Every cached proof module was already compiled by the serialized host
  # module diagnostic, atomically published with its exact source, and bound
  # into ORDER/SHA256SUMS. validate_trusted_cache and
  # validate_final_workspace_modules above recheck both bindings. Reuse that
  # immutable checked prefix here; recompiling it made final-check latency
  # proportional to all prior successful diagnostics without adding a new
  # trust boundary. The kernel still checks every module explicitly below.
  copy_trusted_cache_objects "$PROBLEMOUTDIR"
fi

if [[ "$mode" == final ]] && reuse_problem_cache; then
  : # Reused exact Problem.vo from the latest digest-bound passing diagnostic.
else
  sandbox_compile \
    "$PROBLEMDIR" "$PROBLEMOUTDIR" Problem.v \
    LogosGenerated.Problem Problem.vo
fi

if [[ "$mode" == problem-diagnostic ]]; then
  publish_problem_cache
  echo "LOGOS_TRUSTED_ROCQ_CHECK mode=problem-diagnostic requested_timeout_seconds=$requested_timeout_seconds" >&2
  exit 0
fi

# Goal.v enters a fresh host-created directory only after untrusted compilation
# exits, so Problem.v cannot replace the trusted goal or its dependencies.
cp "$WORKDIR/Goal.v" "$GOALDIR/"
cp "$TRUSTEDDIR/Schema.vo" "$TRUSTEDDIR/Queries.vo" "$TRUSTEDDIR/Witness.vo" \
  "$PROBLEMOUTDIR/Problem.vo" "$GOALDIR/"
for file in "${PROOF_MODULE_ORDER[@]}"; do
  stem="${file%.v}"
  cp "$PROBLEMOUTDIR/ProofModules/$stem.vo" "$GOALDIR/ProofModules/"
done
"$ROCQ_BIN" compile -q -coqlib "$ROCQ_STDLIB_DIR" \
  -Q "$LOGOS_REPO_ROOT/vendor/FormalSQL/src" SQLFS \
  -Q "$LOGOS_REPO_ROOT/theories" Logos \
  -Q "$GOALDIR" LogosGenerated \
  "$GOALDIR/Goal.v"

CHECK_CONTEXT="$CHECKDIR/rocq-check-context.txt"
module_check_arguments=()
for file in "${PROOF_MODULE_ORDER[@]}"; do
  stem="${file%.v}"
  module_check_arguments+=( -norec "LogosGenerated.ProofModules.$stem" )
done
# Schema, Queries, and Witness were kernel-checked before the exact
# source/object prefix was published into the immutable cache. The final
# source-binding and cache-manifest checks above establish that these are the
# same objects. Check only the newly added proof closure here.
"$ROCQ_BIN" check -silent -o -coqlib "$ROCQ_STDLIB_DIR" \
  -Q "$LOGOS_REPO_ROOT/vendor/FormalSQL/src" SQLFS \
  -Q "$LOGOS_REPO_ROOT/theories" Logos \
  -Q "$GOALDIR" LogosGenerated \
  "${module_check_arguments[@]}" \
  -norec LogosGenerated.Problem \
  -norec LogosGenerated.Goal 2>&1 | tee "$CHECK_CONTEXT"

if grep -Eq '^[[:space:]]+LogosGenerated\.' "$CHECK_CONTEXT"; then
  echo "generated proof depends on an untrusted axiom" >&2
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
