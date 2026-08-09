#!/usr/bin/env bash
set -euo pipefail

# This is the only checker-shaped executable exposed to the untrusted proof
# agent. It is a client for a narrow host Unix-socket broker: the host snapshots
# the selected Problem.v, ProofModules/<Name>.v, or scratch/*.v candidate,
# verifies its digest, runs the corresponding diagnostic in bubblewrap, records
# authoritative telemetry, and returns compiler output. A passing module is
# published only by the host into its immutable append-only module cache;
# scratch bytes never enter the final dependency graph.
# The broker has no final-check operation and exposes neither a Rocq switch nor
# a shell command surface to the container.
unset LOGOS_UNTRUSTED_AGENT_CHECK
unset LOGOS_ROCQ_CHECK_DIAGNOSTIC_CHILD
unset LOGOS_ROCQ_CHECK_TIMEOUT_SECONDS
unset LOGOS_TRUSTED_ENVIRONMENT_PREFLIGHT
unset LOGOS_TRUSTED_ROCQ_CHECK_MODE
unset LOGOS_HOST_DIAGNOSTIC_CHECK

usage() {
  echo "usage: bash run-rocq-check.sh --mode <problem|module|scratch> --candidate <Problem.v|ProofModules/Name.v|scratch/*.v> --purpose <static-obligation|semantic-equivalence|assembly> [--timeout-seconds <positive>]" >&2
}

requested_timeout="${LOGOS_PROOF_AGENT_TIMEOUT:-}"
timeout_seen=false
mode=''
candidate=''
purpose=''
while (($#)); do
  [[ "$#" -ge 2 ]] || {
    usage
    exit 64
  }
  case "$1" in
    --mode)
      [[ -z "$mode" ]] || { echo "--mode may be supplied only once" >&2; exit 64; }
      mode="$2"
      ;;
    --candidate)
      [[ -z "$candidate" ]] || { echo "--candidate may be supplied only once" >&2; exit 64; }
      candidate="$2"
      ;;
    --purpose)
      [[ -z "$purpose" ]] || { echo "--purpose may be supplied only once" >&2; exit 64; }
      purpose="$2"
      ;;
    --timeout-seconds)
      [[ "$timeout_seen" == false ]] || {
        echo "--timeout-seconds may be supplied only once" >&2
        exit 64
      }
      requested_timeout="$2"
      timeout_seen=true
      ;;
    *)
      usage
      exit 64
      ;;
  esac
  shift 2
done

case "$mode" in
  problem)
    [[ "$candidate" == Problem.v ]] || {
      echo "problem mode requires --candidate Problem.v" >&2
      exit 64
    }
    ;;
  module)
    [[ "$candidate" =~ ^ProofModules/[A-Z][A-Za-z0-9_]*\.v$ ]] || {
      echo "module mode requires --candidate ProofModules/<UppercaseRocqIdentifier>.v" >&2
      exit 64
    }
    ;;
  scratch)
    [[ "$candidate" == scratch/*.v ]] || {
      echo "scratch mode requires a normalized --candidate scratch/*.v" >&2
      exit 64
    }
    ;;
  *)
    usage
    exit 64
    ;;
esac
case "$purpose" in
  static-obligation|semantic-equivalence|assembly) ;;
  *)
    usage
    exit 64
    ;;
esac

case "$requested_timeout" in
  ''|*[!0-9]*)
    echo "checker timeout must be a positive integer number of seconds" >&2
    exit 64
    ;;
esac
if ((requested_timeout < 1)); then
  echo "checker timeout must be positive" >&2
  exit 64
fi

: "${LOGOS_PROOF_DIAGNOSTIC_SOCKET:?host diagnostic broker socket is unavailable}"
: "${LOGOS_PROOF_DIAGNOSTIC_NONCE:?host diagnostic broker nonce is unavailable}"

workdir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
candidate_file="$workdir/$candidate"
[[ -f "$candidate_file" && ! -L "$candidate_file" ]] || {
  echo "diagnostic candidate must be a regular non-symlink file" >&2
  exit 66
}

python3 - \
  "$LOGOS_PROOF_DIAGNOSTIC_SOCKET" \
  "$LOGOS_PROOF_DIAGNOSTIC_NONCE" \
  "$mode" \
  "$candidate" \
  "$purpose" \
  "$requested_timeout" \
  "$workdir" <<'PY'
import hashlib
import json
import os
import socket
import stat
import sys

socket_path, nonce, mode, candidate_path, purpose, raw_timeout, workdir = sys.argv[1:]
if os.path.isabs(candidate_path) or os.path.normpath(candidate_path) != candidate_path:
    raise SystemExit("candidate path must be normalized and relative")
parts = candidate_path.split("/")
if any(part in ("", ".", "..") for part in parts):
    raise SystemExit("candidate path contains an invalid component")
if mode == "problem" and candidate_path != "Problem.v":
    raise SystemExit("problem mode requires Problem.v")
if mode == "module":
    if (
        len(parts) != 2
        or parts[0] != "ProofModules"
        or not parts[1].endswith(".v")
    ):
        raise SystemExit(
            "module mode requires ProofModules/<UppercaseRocqIdentifier>.v"
        )
    stem = parts[1][:-2]
    if (
        not stem
        or not stem[0].isascii()
        or not stem[0].isupper()
        or not all(ch.isascii() and (ch.isalnum() or ch == "_") for ch in stem)
    ):
        raise SystemExit("proof module name is not a valid uppercase Rocq identifier")
if mode == "scratch" and (len(parts) < 2 or parts[0] != "scratch" or not candidate_path.endswith(".v")):
    raise SystemExit("scratch mode requires scratch/*.v")
cursor = workdir
for part in parts[:-1]:
    cursor = os.path.join(cursor, part)
    if stat.S_ISLNK(os.lstat(cursor).st_mode):
        raise SystemExit("candidate parent must not be a symlink")
candidate_file = os.path.join(workdir, candidate_path)
candidate_stat = os.lstat(candidate_file)
if not stat.S_ISREG(candidate_stat.st_mode) or stat.S_ISLNK(candidate_stat.st_mode):
    raise SystemExit("candidate must be a regular non-symlink file")
candidate_sha256_state = hashlib.sha256()
with open(candidate_file, "rb") as stream:
    for block in iter(lambda: stream.read(1024 * 1024), b""):
        candidate_sha256_state.update(block)
candidate_sha256 = candidate_sha256_state.hexdigest()
candidate_bytes = candidate_stat.st_size
request = {
    "schemaVersion": 2,
    "nonce": nonce,
    "mode": mode,
    "candidatePath": candidate_path,
    "purpose": purpose,
    "candidateSha256": candidate_sha256,
    "candidateBytes": candidate_bytes,
    "requestedTimeoutSeconds": int(raw_timeout),
}
payload = (json.dumps(request, separators=(",", ":")) + "\n").encode("utf-8")
client = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
client.connect(socket_path)
client.sendall(payload)
with open(candidate_file, "rb") as stream:
    for block in iter(lambda: stream.read(1024 * 1024), b""):
        client.sendall(block)
response = bytearray()
while not response.endswith(b"\n"):
    block = client.recv(65536)
    if not block:
        raise RuntimeError("host diagnostic broker closed without a response")
    response.extend(block)
result = json.loads(response)
if result.get("schemaVersion") != 2:
    raise RuntimeError("host diagnostic broker response schema mismatch")
for key, expected in (
    ("mode", mode),
    ("candidatePath", candidate_path),
    ("purpose", purpose),
    ("candidateSha256", candidate_sha256),
):
    if (result.get("compilePassed") is True or result.get(key) is not None) and result.get(key) != expected:
        raise RuntimeError(f"host diagnostic broker response identity mismatch for {key}")
if result.get("stdout"):
    sys.stdout.write(result["stdout"])
if result.get("stderr"):
    sys.stderr.write(result["stderr"])
if result.get("error"):
    sys.stderr.write("host diagnostic broker: " + result["error"] + "\n")
if result.get("compilePassed") is True:
    checkpoint_advanced = result.get("compileCheckpointAdvanced") is True
    problem_passed = result.get("problemCompilePassed") is True
    if mode == "problem" and (not problem_passed or not checkpoint_advanced):
        raise RuntimeError("successful Problem.v compile did not advance its checkpoint")
    if mode in ("module", "scratch") and (problem_passed or checkpoint_advanced):
        raise RuntimeError(f"{mode} compile was incorrectly classified as a Problem.v checkpoint")
    if mode == "problem":
        sys.stdout.write(
            "Host problem-only compile passed and checkpointed this exact Problem.v. "
            "Continue editing, or end the turn if the mode-specific final theorem is complete.\n"
        )
    elif mode == "module":
        sys.stdout.write(
            "Host module compile passed and published this exact source into the "
            "immutable ordered ProofModules cache. Do not modify this module; create "
            "a new successor module for further lemmas.\n"
        )
    else:
        sys.stdout.write(
            "Host scratch compile passed and retained this exact opaque-Qed subproof. "
            "It did not advance or certify Problem.v; continue with proof development and assembly.\n"
        )
    raise SystemExit(0)
if result.get("timedOut") is True:
    raise SystemExit(124)
code = result.get("exitCode")
raise SystemExit(code if isinstance(code, int) and 0 < code < 126 else 1)
PY
