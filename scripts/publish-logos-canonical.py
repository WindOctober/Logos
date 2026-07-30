#!/usr/bin/env python3
"""Publish one canonical frozen-cohort Logos result from runner artifacts."""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import math
import os
import re
import runpy
import shlex
import shutil
import stat
import sys
import tempfile
import types
from collections import Counter
from pathlib import Path
from typing import Any

try:
    import tomllib
except ModuleNotFoundError:
    import tomli as tomllib

LOGOS_ROOT = Path(__file__).resolve().parents[1]
SOURCE_TREE_DIGEST_HELPER_RELATIVE_PATH = "scripts/logos_source_tree_digest.py"
SOURCE_TREE_DIGEST_HELPER_SHA256 = (
    "3ed6d7123ada5585018afcd5c575bedbe564c5c0cb296bc6fb85b1119a509f55"
)
SOURCE_TREE_DIGEST_HELPER_BYTES = 7_880


def load_source_tree_digest_helper() -> types.ModuleType:
    """Execute only helper bytes transitively pinned by this publisher."""

    path = LOGOS_ROOT / SOURCE_TREE_DIGEST_HELPER_RELATIVE_PATH
    flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NOFOLLOW", 0)
    descriptor = -1
    try:
        descriptor = os.open(path, flags)
        metadata = os.fstat(descriptor)
        if (
            not stat.S_ISREG(metadata.st_mode)
            or metadata.st_size != SOURCE_TREE_DIGEST_HELPER_BYTES
        ):
            raise RuntimeError(
                "source-tree digest helper is not the immutable expected regular file"
            )
        with os.fdopen(descriptor, "rb", closefd=True) as stream:
            descriptor = -1
            payload = stream.read()
    except OSError as error:
        raise RuntimeError(
            f"cannot load immutable source-tree digest helper: {error}"
        ) from error
    finally:
        if descriptor >= 0:
            os.close(descriptor)
    if (
        len(payload) != SOURCE_TREE_DIGEST_HELPER_BYTES
        or hashlib.sha256(payload).hexdigest() != SOURCE_TREE_DIGEST_HELPER_SHA256
    ):
        raise RuntimeError(
            "source-tree digest helper differs from the immutable publisher binding"
        )
    module = types.ModuleType("logos_source_tree_digest")
    module.__file__ = str(path)
    module.__package__ = ""
    sys.modules[module.__name__] = module
    exec(compile(payload, str(path), "exec", dont_inherit=True), module.__dict__)
    return module


_SOURCE_TREE_DIGEST_HELPER = load_source_tree_digest_helper()
SourceTreeError = _SOURCE_TREE_DIGEST_HELPER.SourceTreeError
build_source_tree_manifest = _SOURCE_TREE_DIGEST_HELPER.build_manifest
source_tree_manifest_sha256 = _SOURCE_TREE_DIGEST_HELPER.manifest_sha256


WORKFLOW_ROOT = LOGOS_ROOT.parent
RUNNER_PATH = LOGOS_ROOT / "benchmarks/scripts/run-logos"
_RUNNER_VALIDATORS: dict[str, Any] | None = None
DEFAULT_OUTPUT = WORKFLOW_ROOT / "FinalExperiment/Logos"
FROZEN_SUMMARY_SHA256 = (
    "be93b4fb307812067194ca55f1b4b9394d2dbdb04d0bf985dcbb03e2f86abcbe"
)
BENCHMARK_FINGERPRINT = (
    "0c25cb9d500bce29545ede21d42df355fd23efbef32d1725db11ad026b6be91f"
)
FROZEN_CASE_SET_SHA256 = (
    "c02bc80056ccd6adccecbd1b3c2cd9bf98032d6906580ffb755dc93d05a330a8"
)
FROZEN_INPUT_MANIFEST_SHA256 = (
    "d34443e927c3e68a28c6d216334c624e1b50d0b37d60c9c937d21202b9f3162e"
)
INPUT_MANIFEST_ALGORITHM = "logos-frozen-input-manifest-v1"
SEMANTIC_INPUT_AUTHORITY_ALGORITHM = "logos-semantic-input-authority-v1"
FROZEN_SEMANTIC_INPUT_AUTHORITY_SHA256 = (
    "8ee79987c8f77cb88bc637196931010b7da88e8f4fb3303392527f1e156587a4"
)
TRUSTED_ROCQ_RUNTIME_SNAPSHOT_SCHEMA_VERSION = 1
TRUSTED_ROCQ_RUNTIME_SNAPSHOT_ALGORITHM = "logos-trusted-rocq-runtime-snapshot-v1"
TRUSTED_ROCQ_RUNTIME_SNAPSHOT_POLICY = (
    "run-private-immutable-rocq-runtime-bwrap-closure-v1"
)
TRUSTED_ROCQ_AUTHORITY_SNAPSHOT_SCHEMA_VERSION = 2
TRUSTED_ROCQ_AUTHORITY_SNAPSHOT_ALGORITHM = (
    "logos-trusted-rocq-authority-snapshot-v2"
)
TRUSTED_ROCQ_AUTHORITY_SNAPSHOT_POLICY = (
    "run-private-forced-source-build-closure-v2"
)
TRUSTED_STACK_MANIFEST_ALGORITHM = "logos-trusted-proof-stack-manifest-v7"
TRUSTED_STACK_MANIFEST_SCHEMA_VERSION = 7
TRUSTED_DYNAMIC_LINKING_ALGORITHM = "logos-elf-runtime-closure-v2"
TRUSTED_INSPECTION_ENVIRONMENT_POLICY = "clear-then-fixed-allowlist-v1"
TRUSTED_INSPECTION_ENVIRONMENT_VARIABLES = (
    {"name": "LANG", "value": "C"},
    {"name": "LC_ALL", "value": "C"},
    {"name": "PATH", "value": "/usr/bin:/bin"},
)
TRUSTED_CHECKER_INITIAL_PATH = "/Anaconda/bin:/usr/bin:/bin"
TRUSTED_LDD_PATH = "/usr/bin/ldd"
TRUSTED_LDD_SHA256S = frozenset(
    {
        # Ubuntu GLIBC 2.37-0ubuntu2.2 (Ubuntu 23.04).
        "ab2b0110ee2b8725a08deec886d57d84a37c31d1225aceb7321faf1b583c46f1",
        # Ubuntu GLIBC 2.35-0ubuntu3.13 (Ubuntu 22.04).
        "e7cc1a3c95077362934b953093fec80330b6b76974e66836b7583ff818468fd5",
    }
)
TRUSTED_LDD_RUNTIME_LOADER_ALGORITHM = "logos-ldd-literal-rtldlist-closure-v1"
TRUSTED_SYSTEM_RESOLVER_CONFIGURATION_ALGORITHM = (
    "logos-system-dynamic-loader-config-closure-v1"
)
TRUSTED_SYSTEM_RESOLVER_CONFIGURATION_PATHS = (
    "/etc/ld.so.cache",
    "/etc/ld.so.preload",
)
TRUSTED_SYSTEM_IDENTITY_CONFIGURATION_ALGORITHM = (
    "logos-system-identity-config-closure-v1"
)
TRUSTED_SYSTEM_IDENTITY_CONFIGURATION_PATHS = (
    "/etc/nsswitch.conf",
    "/etc/passwd",
)
TRUSTED_EXECUTABLE_NAMES = (
    "rocq",
    "rocqchk",
    "rocqworker",
    "rocqnative",
    "bwrap",
)
TRUSTED_HOST_TOOL_NAMES = (
    "bash",
    "timeout",
    "cat",
    "realpath",
    "dirname",
    "basename",
    "mktemp",
    "rm",
    "mkdir",
    "chmod",
    "install",
    "find",
    "sort",
    "ldd",
    "awk",
    "readelf",
    "cp",
    "sha256sum",
    "cmp",
    "tee",
    "grep",
    "comm",
    "mv",
    "readlink",
    "stat",
    "id",
)
TRUSTED_DIAGNOSTIC_CACHE_BASE_ENTRIES = (
    "Schema.v",
    "Schema.vo",
    "Queries.v",
    "Queries.vo",
    "Witness.v",
    "Witness.vo",
    "ProofModules/ORDER",
)
TRUSTED_DIAGNOSTIC_CACHE_SOURCE_ENTRIES = (
    "Schema.v",
    "Queries.v",
    "Witness.v",
)
FRONTEND_STACK_MANIFEST_ALGORITHM = "logos-sql-frontend-stack-manifest-v2"
FRONTEND_STACK_MANIFEST_SCHEMA_VERSION = 2
FRONTEND_LAUNCH_ENVIRONMENT_ALGORITHM = "logos-sql-frontend-launch-environment-v1"
FRONTEND_LAUNCH_ENVIRONMENT_POLICY = "clear-then-fixed-explicit-allowlist-v1"
FRONTEND_LAUNCH_TOOLS_ALGORITHM = "logos-sql-frontend-launch-tools-v1"
FRONTEND_FIXED_ENVIRONMENT_VARIABLES = (
    {"name": "PATH", "value": "/usr/bin:/bin"},
    {"name": "HOME", "value": "/nonexistent"},
    {"name": "TMPDIR", "value": "/tmp"},
    {"name": "LC_ALL", "value": "C"},
    {"name": "LANG", "value": "C"},
    {"name": "TZ", "value": "UTC"},
)
FRONTEND_EXPLICIT_ENVIRONMENT_NAMES = (
    "JAVA_HOME",
    "MAVEN_VERSION",
    "LOGOS_CALCITE_RUNTIME_CLASSPATH_FILE",
)
FRONTEND_LAUNCH_EXCLUDED_VARIABLES = (
    "BASH_ENV",
    "ENV",
    "SHELLOPTS",
    "BASHOPTS",
    "LD_PRELOAD",
    "LD_LIBRARY_PATH",
    "OCAMLPATH",
    "CAML_LD_LIBRARY_PATH",
    "CDPATH",
    "JAVA_TOOL_OPTIONS",
    "_JAVA_OPTIONS",
    "JDK_JAVA_OPTIONS",
    "CLASSPATH",
    "MAVEN_OPTS",
    "MAVEN_ARGS",
)
FRONTEND_LAUNCH_BASH = "/usr/bin/bash"
FRONTEND_LAUNCH_ARGUMENTS = ("--noprofile", "--norc", "-c")
FRONTEND_LAUNCH_COMMAND_BODY = 'source "$0" "$@"'
FRONTEND_LAUNCH_TOOL_NAMES = (
    "bash",
    "sh",
    "dirname",
    "readlink",
    "uname",
    "mkdir",
    "curl",
    "tar",
)
FRONTEND_LAUNCH_TOOL_PATHS = {
    "bash": FRONTEND_LAUNCH_BASH,
    "sh": "/bin/sh",
    "dirname": "/usr/bin/dirname",
    "readlink": "/usr/bin/readlink",
    "uname": "/usr/bin/uname",
    "mkdir": "/usr/bin/mkdir",
    "curl": "/usr/bin/curl",
    "tar": "/usr/bin/tar",
}
CODEX_PROVIDER_MANIFEST_ALGORITHM = "logos-codex-provider-manifest-v1"
POSTGRES_PROFILE_MANIFEST_ALGORITHM = "logos-postgres-server-profile-v1"
CANONICAL_FRONTEND_SCRIPT = LOGOS_ROOT / "scripts/calcite-ir"
CANONICAL_FRONTEND_SCRIPT_DISPLAY = CANONICAL_FRONTEND_SCRIPT.relative_to(
    WORKFLOW_ROOT
).as_posix()
CANONICAL_FRONTEND_COMMAND = shlex.join(
    (
        FRONTEND_LAUNCH_BASH,
        *FRONTEND_LAUNCH_ARGUMENTS,
        FRONTEND_LAUNCH_COMMAND_BODY,
        str(CANONICAL_FRONTEND_SCRIPT.resolve()),
    )
)
MODEL = "gpt-5.6-sol"
REASONING_EFFORT = "medium"
FULL_RUN_JOBS = 32
CASE_TIMEOUT_SECONDS = 4 * 3600
MAX_COUNTEREXAMPLE_ROUNDS = 3
TRUSTED_CHECK_TIMEOUT_SECONDS = 420
PROOF_AGENT_MEMORY_LIMIT_MIB = 6144
PROOF_AGENT_STORAGE_LIMIT_MIB = 2048
STATEMENT_TIMEOUT_SECONDS = 600
PROOF_AGENT_SESSION_RESTART_AFTER_FAILED_ROUNDS = 16
PROOF_AGENT_SESSION_HOME_POLICY = "isolated_per_generation"
PROOF_AGENT_DIAGNOSTIC_TRANSPORT = "host_unix_broker"
PROOF_AGENT_DIAGNOSTIC_CACHE_POLICY = "preflight_built_source_digest_bound_host_only"
PROOF_AGENT_DIAGNOSTIC_TIMEOUT_POLICY = (
    "positive_request_bounded_only_by_current_invocation_deadline"
)
PROOF_AGENT_DIAGNOSTIC_BUDGET_POLICY = "bounded_by_invocation_deadline"
PROOF_AGENT_DIAGNOSTIC_CHECKER_PARALLELISM_MAX = 1
PROOF_AGENT_DIAGNOSTIC_CHECKER_SCHEDULING_POLICY = (
    "sequential_host_broker_invocation_deadline_bounded"
)
DIAGNOSTIC_ELAPSED_KILL_MARGIN_MS = 6_000
DIAGNOSTIC_ELAPSED_WARNING_CODE = (
    "diagnostic_elapsed_exceeded_timeout_plus_kill_margin"
)
TRUSTED_ELAPSED_WARNING_CODE = (
    "trusted_elapsed_exceeded_timeout_plus_kill_margin"
)
PROOF_AGENT_COMPILE_CHECKPOINT_POLICY = (
    "latest_host_problem_compile_pass_over_immutable_checked_module_cache_digest_deduplicated"
)
PROOF_AGENT_SCRATCH_PERSISTENCE_POLICY = (
    "regular_nonsymlink_allowed_extension_round_replacement_drop_other_extensions_with_warning_exact_digest_checked_promotion"
)
PROOF_AGENT_SCRATCH_ALLOWED_EXTENSIONS = ["v", "md", "txt"]
PROOF_AGENT_WRITABLE_STORAGE_POLICY = (
    "single_kernel_tmpfs_all_agent_writes_with_read_only_root_v1"
)
PROOF_AGENT_LAUNCH_EXCLUDED_VARIABLES = (
    "BASH_ENV",
    "ENV",
    "SHELLOPTS",
    "BASHOPTS",
    "LD_PRELOAD",
    "LD_LIBRARY_PATH",
    "OCAMLPATH",
    "CAML_LD_LIBRARY_PATH",
    "CDPATH",
)
PROOF_AGENT_LAUNCH_EXCLUDED_PREFIXES = ("BASH_FUNC_",)
SOLVER_LAUNCH_EXCLUDED_VARIABLES = FRONTEND_LAUNCH_EXCLUDED_VARIABLES + (
    "PYTHONHOME",
    "PYTHONPATH",
    "VIRTUAL_ENV",
    "OPENAI_API_KEY",
    "CODEX_API_KEY",
    "OPENAI_BASE_URL",
    "CODEX_BASE_URL",
    "OPENAI_API_BASE",
    "AZURE_OPENAI_ENDPOINT",
    "OPENAI_ORGANIZATION",
    "OPENAI_ORG_ID",
    "OPENAI_PROJECT_ID",
    "HTTP_PROXY",
    "HTTPS_PROXY",
    "ALL_PROXY",
    "NO_PROXY",
    "http_proxy",
    "https_proxy",
    "all_proxy",
    "no_proxy",
)
SOLVER_FIXED_ENVIRONMENT_VARIABLES = (
    "HOME=/nonexistent",
    "TMPDIR=/tmp",
    "LC_ALL=C",
    "LANG=C",
    "TZ=UTC",
)
SOLVER_EXPLICIT_ENVIRONMENT_NAMES = (
    "CODEX_HOME",
    "LOGOS_SOLVER_CODEX_HOME",
    "LOGOS_SOLVER_CODEX_CONFIG",
    "JAVA_HOME",
    "MAVEN_VERSION",
    "LOGOS_CALCITE_RUNTIME_CLASSPATH_FILE",
)
SOLVER_ENVIRONMENT_POLICY_ALGORITHM = "logos-solver-launch-environment-v1"
TRUSTED_CHECKER_FIXED_VARIABLES = (
    "PATH=/Anaconda/bin:/usr/bin:/bin",
    "HOME=/nonexistent",
    "LC_ALL=C",
    "LANG=C",
)
TRUSTED_CHECKER_EXPLICIT_CONTRACT_VARIABLES = (
    "LOGOS_REPO_ROOT",
    "LOGOS_PROOF_WORKDIR",
    "LOGOS_TRUSTED_ROCQ_CACHE_DIR",
    "LOGOS_ROCQ_OPAM_SWITCH",
)
PROOF_AGENT_LAUNCHER_FIXED_VARIABLES = (
    "PATH=/usr/bin:/bin",
    "LC_ALL=C",
    "LANG=C",
)
PROOF_AGENT_LAUNCHER_HOST_ENVIRONMENT_ALLOWLIST = (
    "HOME",
    "CODEX_HOME",
    "LOGOS_SOLVER_CODEX_HOME",
    "LOGOS_SOLVER_CODEX_CONFIG",
    "OPENAI_API_KEY",
    "CODEX_API_KEY",
    "DOCKER_HOST",
    "DOCKER_CONTEXT",
    "DOCKER_CONFIG",
    "DOCKER_CERT_PATH",
    "DOCKER_TLS",
    "DOCKER_TLS_VERIFY",
    "DOCKER_API_VERSION",
)
PROOF_AGENT_LAUNCHER_EXPLICIT_CONTRACT_VARIABLES = (
    "LOGOS_REPO_ROOT",
    "LOGOS_PROOF_WORKDIR",
    "LOGOS_PROOF_AGENT_CODEX_HOME",
    "LOGOS_PROOF_AGENT_STAGE",
    "LOGOS_PROOF_DIAGNOSTIC_SOCKET",
    "LOGOS_PROOF_DIAGNOSTIC_NONCE",
    "LOGOS_SOLVER_IMAGE",
    "LOGOS_PROOF_AGENT_COMMAND",
    "LOGOS_PROOF_AGENT_MEMORY_LIMIT",
    "LOGOS_PROOF_AGENT_STORAGE_LIMIT_BYTES",
    "LOGOS_PROOF_AGENT_TIMEOUT",
)
LEGACY_CATALOG_GUIDANCE_ENVIRONMENT_VARIABLE = "LOGOS_PROOF_AGENT_CATALOG_GUIDANCE"
PROOF_AGENT_BROKER_METRIC_KEYS = (
    "diagnosticRequestCount",
    "diagnosticRequestedTimeoutSecondsReserved",
    "diagnosticAcceptedRequestCount",
    "diagnosticRejectedSourceAuditCount",
    "diagnosticOtherRejectedRequestCount",
    "diagnosticAcceptedAuditArtifactCount",
    "diagnosticRejectedSourceAuditArtifactCount",
    "diagnosticPreservedArtifactCount",
)
VERIFICATION_MODE = "outcome-unconditional"
INPUT_RATE = 5.0
CACHED_INPUT_RATE = 0.5
OUTPUT_RATE = 30.0
PRICING_SOURCE = "https://developers.openai.com/api/docs/pricing"
PRICING_AS_OF = "2026-07-22"
TERMINAL_STATUSES = frozenset(("completed", "timed_out", "failed"))
FORCED_COUNTEREXAMPLE_ARGUMENT = "--force-llm-assessment"
DEFAULT_PROOF_AGENT_COMMAND = (
    "codex exec --disable plugins --disable remote_plugin --disable plugin_hooks "
    "--disable skill_mcp_dependency_install --disable goals --json --model gpt-5.6-sol "
    "-c model_reasoning_effort=medium "
    "--dangerously-bypass-approvals-and-sandbox --skip-git-repo-check "
    "--cd /workspace/problem - < proof-agent-prompt.md"
)
DEFAULT_PROOF_AGENT_RESUME_COMMAND = (
    "codex exec resume --disable plugins --disable remote_plugin --disable "
    "plugin_hooks --disable skill_mcp_dependency_install --disable goals --json --model "
    "gpt-5.6-sol -c model_reasoning_effort=medium "
    "--dangerously-bypass-approvals-and-sandbox --skip-git-repo-check "
    "{session_id} - < proof-agent-prompt.md"
)
DEFAULT_COUNTEREXAMPLE_COMMAND = (
    "codex exec --disable plugins --disable remote_plugin --disable plugin_hooks "
    "--disable skill_mcp_dependency_install --json --model gpt-5.6-sol "
    "-c model_reasoning_effort=medium "
    "--dangerously-bypass-approvals-and-sandbox --skip-git-repo-check -"
)
FORBIDDEN_SOLVER_OPTIONS = frozenset(
    (
        "--disable-counterexample-search",
        "--disable-proof-agent",
        "--calcite-ir-command",
        "--help",
        "--llm-assessment-only",
        "--max-counterexample-rounds",
        "--reuse-llm-assessment",
        "--transform-only",
        "--version",
    )
)


class PublishError(RuntimeError):
    pass


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def load_json(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise PublishError(f"cannot read {path}: {error}") from error
    if not isinstance(value, dict):
        raise PublishError(f"{path} must contain one JSON object")
    return value


def sha256_text(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def resolve_recorded_file(value: Any, location: str, run_root: Path) -> Path:
    if not isinstance(value, str) or not value.strip():
        raise PublishError(f"{location} must be a nonempty path")
    recorded = Path(value).expanduser()
    candidates = (
        (recorded,)
        if recorded.is_absolute()
        else (
            WORKFLOW_ROOT / recorded,
            LOGOS_ROOT / recorded,
            run_root / recorded,
        )
    )
    raw_matches = [candidate for candidate in candidates if candidate.is_file()]
    if any(candidate.is_symlink() for candidate in raw_matches):
        raise PublishError(f"{location} must not identify a symlink: {value}")
    matches = [candidate.resolve() for candidate in raw_matches]
    if not matches:
        raise PublishError(f"{location} does not identify a readable file: {value}")
    unique = list(dict.fromkeys(matches))
    if len(unique) > 1:
        raise PublishError(f"{location} is ambiguous: {value}")
    return unique[0]


def resolve_recorded_directory(value: Any, location: str, run_root: Path) -> Path:
    if not isinstance(value, str) or not value.strip():
        raise PublishError(f"{location} must be a nonempty path")
    recorded = Path(value).expanduser()
    candidates = (
        (recorded,)
        if recorded.is_absolute()
        else (
            WORKFLOW_ROOT / recorded,
            LOGOS_ROOT / recorded,
            run_root / recorded,
        )
    )
    raw_matches = [candidate for candidate in candidates if candidate.is_dir()]
    if any(candidate.is_symlink() for candidate in raw_matches):
        raise PublishError(f"{location} must not identify a symlink: {value}")
    matches = [candidate.resolve() for candidate in raw_matches]
    if not matches:
        raise PublishError(f"{location} does not identify a readable directory: {value}")
    unique = list(dict.fromkeys(matches))
    if len(unique) > 1:
        raise PublishError(f"{location} is ambiguous: {value}")
    return unique[0]


def validate_file_binding(
    record: Any,
    *,
    path_key: str,
    digest_key: str,
    location: str,
    run_root: Path,
    expected_path: Path | None = None,
) -> tuple[Path, str]:
    if not isinstance(record, dict):
        raise PublishError(f"{location} must be an object")
    digest = record.get(digest_key)
    if not valid_sha256(digest):
        raise PublishError(f"{location}.{digest_key} must be a lowercase SHA-256")
    path = resolve_recorded_file(
        record.get(path_key), f"{location}.{path_key}", run_root
    )
    if expected_path is not None and path != expected_path.resolve():
        raise PublishError(f"{location}.{path_key} identifies the wrong artifact")
    observed = sha256(path)
    if observed != digest:
        raise PublishError(
            f"{location} digest mismatch: recorded {digest}, observed {observed}"
        )
    return path, digest


def string_array(value: Any, location: str) -> list[str]:
    if not isinstance(value, list) or any(
        not isinstance(item, str) or not item for item in value
    ):
        raise PublishError(f"{location} must be an array of nonempty strings")
    return list(value)


def require_exact_keys(
    value: Any, expected: set[str] | frozenset[str], location: str
) -> dict[str, Any]:
    """Require one object with no omitted or silently ignored fields."""
    if not isinstance(value, dict) or set(value) != set(expected):
        observed = sorted(value) if isinstance(value, dict) else type(value).__name__
        raise PublishError(
            f"{location} has noncanonical fields: expected {sorted(expected)}, "
            f"observed {observed}"
        )
    return value


def launch_environment_policy(
    *,
    fixed_variables: tuple[str, ...],
    host_environment_allowlist: tuple[str, ...],
    explicit_contract_variables: tuple[str, ...],
) -> dict[str, Any]:
    """Build the exact fail-closed host process environment contract."""
    return {
        "schemaVersion": 1,
        "inheritedEnvironmentCleared": True,
        "fixedVariables": list(fixed_variables),
        "hostEnvironmentAllowlist": list(host_environment_allowlist),
        "explicitContractVariables": list(explicit_contract_variables),
        "unlistedEnvironmentPolicy": "excluded_by_env_clear_before_process_start",
        "explicitlyExcludedVariables": list(PROOF_AGENT_LAUNCH_EXCLUDED_VARIABLES),
        "explicitlyExcludedPrefixes": list(PROOF_AGENT_LAUNCH_EXCLUDED_PREFIXES),
    }


def proof_agent_environment_configuration(
    *, legacy_catalog: bool = False
) -> dict[str, Any]:
    """The exact host launch policies for current or legacy proof artifacts."""
    launcher_contract = list(PROOF_AGENT_LAUNCHER_EXPLICIT_CONTRACT_VARIABLES)
    if legacy_catalog:
        launcher_contract.insert(
            launcher_contract.index("LOGOS_PROOF_AGENT_MEMORY_LIMIT"),
            LEGACY_CATALOG_GUIDANCE_ENVIRONMENT_VARIABLE,
        )
    return {
        "trustedCheckerEnvironmentPolicy": launch_environment_policy(
            fixed_variables=TRUSTED_CHECKER_FIXED_VARIABLES,
            host_environment_allowlist=(),
            explicit_contract_variables=(TRUSTED_CHECKER_EXPLICIT_CONTRACT_VARIABLES),
        ),
        "proofAgentLauncherEnvironmentPolicy": launch_environment_policy(
            fixed_variables=PROOF_AGENT_LAUNCHER_FIXED_VARIABLES,
            host_environment_allowlist=(
                PROOF_AGENT_LAUNCHER_HOST_ENVIRONMENT_ALLOWLIST
            ),
            explicit_contract_variables=tuple(launcher_contract),
        ),
    }


def proof_agent_diagnostic_configuration(
    *, legacy_catalog: bool = False
) -> dict[str, Any]:
    """The fixed host-broker/checkpoint contract recorded by solver reports."""
    return {
        "diagnosticTransport": PROOF_AGENT_DIAGNOSTIC_TRANSPORT,
        "diagnosticCachePolicy": PROOF_AGENT_DIAGNOSTIC_CACHE_POLICY,
        "diagnosticTimeoutPolicy": PROOF_AGENT_DIAGNOSTIC_TIMEOUT_POLICY,
        "diagnosticBudgetPolicy": PROOF_AGENT_DIAGNOSTIC_BUDGET_POLICY,
        "diagnosticCheckerParallelismMax": (
            PROOF_AGENT_DIAGNOSTIC_CHECKER_PARALLELISM_MAX
        ),
        "diagnosticCheckerSchedulingPolicy": (
            PROOF_AGENT_DIAGNOSTIC_CHECKER_SCHEDULING_POLICY
        ),
        "compileCheckpointPolicy": PROOF_AGENT_COMPILE_CHECKPOINT_POLICY,
        "scratchPersistencePolicy": PROOF_AGENT_SCRATCH_PERSISTENCE_POLICY,
        "writableStorageLimitBytes": PROOF_AGENT_STORAGE_LIMIT_MIB * 1024 * 1024,
        "writableStoragePolicy": PROOF_AGENT_WRITABLE_STORAGE_POLICY,
        "scratchAllowedExtensions": PROOF_AGENT_SCRATCH_ALLOWED_EXTENSIONS,
        **proof_agent_environment_configuration(legacy_catalog=legacy_catalog),
    }


def effective_proof_agent_diagnostic_configuration(
    *, legacy_catalog: bool = False
) -> dict[str, Any]:
    """Flattened form emitted in each runner result's effective configuration."""
    return {
        "proofAgentDiagnosticTransport": PROOF_AGENT_DIAGNOSTIC_TRANSPORT,
        "proofAgentDiagnosticCachePolicy": PROOF_AGENT_DIAGNOSTIC_CACHE_POLICY,
        "proofAgentDiagnosticTimeoutPolicy": PROOF_AGENT_DIAGNOSTIC_TIMEOUT_POLICY,
        "proofAgentDiagnosticBudgetPolicy": PROOF_AGENT_DIAGNOSTIC_BUDGET_POLICY,
        "proofAgentDiagnosticCheckerParallelismMax": (
            PROOF_AGENT_DIAGNOSTIC_CHECKER_PARALLELISM_MAX
        ),
        "proofAgentDiagnosticCheckerSchedulingPolicy": (
            PROOF_AGENT_DIAGNOSTIC_CHECKER_SCHEDULING_POLICY
        ),
        "proofAgentCompileCheckpointPolicy": PROOF_AGENT_COMPILE_CHECKPOINT_POLICY,
        "proofAgentScratchPersistencePolicy": PROOF_AGENT_SCRATCH_PERSISTENCE_POLICY,
        "proofAgentWritableStorageLimitBytes": (
            PROOF_AGENT_STORAGE_LIMIT_MIB * 1024 * 1024
        ),
        "proofAgentWritableStoragePolicy": PROOF_AGENT_WRITABLE_STORAGE_POLICY,
        "proofAgentScratchAllowedExtensions": PROOF_AGENT_SCRATCH_ALLOWED_EXTENSIONS,
        **proof_agent_environment_configuration(legacy_catalog=legacy_catalog),
    }


def validate_legacy_catalog_marker(
    record: Any,
    key: str,
    *,
    legacy_catalog: bool,
    location: str,
) -> None:
    """Require one coherent legacy marker, or its absence in current artifacts."""
    if not isinstance(record, dict):
        raise PublishError(f"{location} must be an object")
    if legacy_catalog:
        if record.get(key) is not True:
            raise PublishError(
                f"{location}.{key} is missing from legacy catalog-on evidence"
            )
    elif key in record:
        raise PublishError(
            f"{location}.{key} is legacy catalog metadata in a current artifact"
        )


def legacy_catalog_artifact_mode(document: dict[str, Any], configuration: Any) -> bool:
    """Classify a full run without interpreting catalog metadata as treatment."""
    if not isinstance(configuration, dict):
        raise PublishError("full runner summary has no configuration object")
    proof_agent = configuration.get("proofAgent")
    if not isinstance(proof_agent, dict):
        raise PublishError("full runner summary has no proofAgent configuration")
    top_present = "proofAgentCatalogGuidanceEnabled" in document
    nested_present = "catalogGuidanceEnabled" in proof_agent
    if top_present != nested_present:
        raise PublishError(
            "legacy catalog metadata is incomplete across full-run layers"
        )
    if not top_present:
        return False
    if (
        document.get("proofAgentCatalogGuidanceEnabled") is not True
        or proof_agent.get("catalogGuidanceEnabled") is not True
    ):
        raise PublishError("legacy catalog metadata is not the catalog-on format")
    return True


def validate_fixed_fields(record: Any, expected: dict[str, Any], location: str) -> None:
    if not isinstance(record, dict):
        raise PublishError(f"{location} must be an object")
    for key, value in expected.items():
        if record.get(key) != value:
            raise PublishError(f"{location}.{key} differs from the frozen contract")


def validate_solver_arguments(
    document: dict[str, Any], configuration: dict[str, Any]
) -> list[str]:
    requested = string_array(document.get("solverArgs"), "solverArgs")
    effective = string_array(document.get("effectiveSolverArgs"), "effectiveSolverArgs")
    if (
        configuration.get("solverArgs") != requested
        or configuration.get("effectiveSolverArgs") != effective
    ):
        raise PublishError("top-level and configuration solver arguments differ")
    if effective.count(FORCED_COUNTEREXAMPLE_ARGUMENT) != 1:
        raise PublishError("effective solver arguments must force one fresh assessment")
    for argument in (*requested, *effective):
        option = argument.split("=", 1)[0]
        if option in FORBIDDEN_SOLVER_OPTIONS:
            raise PublishError(
                f"canonical full run uses disabling/short-circuit solver option {option}"
            )
    if (
        configuration.get("counterexampleAssessmentPolicy") != "force-fresh"
        or document.get("counterexampleAssessmentPolicy") != "force-fresh"
    ):
        raise PublishError(
            "canonical full run did not force fresh counterexample assessment"
        )
    return effective


def parse_timestamp(value: Any, location: str) -> dt.datetime:
    if not isinstance(value, str) or not value:
        raise PublishError(f"{location} must be a nonempty timestamp")
    try:
        parsed = dt.datetime.fromisoformat(value.replace("Z", "+00:00"))
    except ValueError as error:
        raise PublishError(f"{location} is not an ISO-8601 timestamp") from error
    if parsed.tzinfo is None:
        raise PublishError(f"{location} must include a time zone")
    return parsed


def canonical_case(value: str) -> str:
    prefix = "nonwetune-flat__"
    return value[len(prefix) :] if value.startswith(prefix) else value


def expected_cases(output: Path) -> set[str]:
    frozen = output / "summary.raw.json"
    if sha256(frozen) != FROZEN_SUMMARY_SHA256:
        raise PublishError("frozen summary.raw.json digest changed")
    rows = load_json(frozen).get("results")
    if not isinstance(rows, list):
        raise PublishError("frozen summary has no results array")
    cases = {
        canonical_case(row["case"])
        for row in rows
        if isinstance(row, dict) and isinstance(row.get("case"), str)
    }
    if len(rows) != 389 or len(cases) != 389:
        raise PublishError("frozen scope is not 389 unique cases")
    return cases


def canonical_usage(value: Any, location: str) -> dict[str, Any]:
    if not isinstance(value, dict) or value.get("model") != MODEL:
        raise PublishError(f"{location}: missing {MODEL} usage")

    def count(name: str) -> int:
        result = value.get(name)
        if isinstance(result, bool) or not isinstance(result, int) or result < 0:
            raise PublishError(f"{location}.{name} must be a nonnegative integer")
        return result

    input_tokens = count("inputTokens")
    cached_tokens = count("cachedInputTokens")
    output_tokens = count("outputTokens")
    total_tokens = count("totalTokens")
    if cached_tokens > input_tokens or total_tokens != input_tokens + output_tokens:
        raise PublishError(f"{location}: inconsistent token counts")
    cost = (
        (input_tokens - cached_tokens) * INPUT_RATE
        + cached_tokens * CACHED_INPUT_RATE
        + output_tokens * OUTPUT_RATE
    ) / 1_000_000
    supplied = value.get("estimatedCostUsd")
    if (
        isinstance(supplied, bool)
        or not isinstance(supplied, (int, float))
        or not math.isclose(float(supplied), cost, rel_tol=1e-8, abs_tol=1e-8)
    ):
        raise PublishError(f"{location}: estimated cost does not reconcile")
    return {
        "model": MODEL,
        "inputTokens": input_tokens,
        "cachedInputTokens": cached_tokens,
        "outputTokens": output_tokens,
        "totalTokens": total_tokens,
        "estimatedCostUsd": cost,
    }


def nested(value: dict[str, Any], *keys: str) -> Any:
    current: Any = value
    for key in keys:
        if not isinstance(current, dict) or key not in current:
            return None
        current = current[key]
    return current


def valid_sha256(value: Any) -> bool:
    return (
        isinstance(value, str)
        and len(value) == 64
        and all(character in "0123456789abcdef" for character in value)
    )


def completed_return_code_is_coherent(row: dict[str, Any]) -> bool:
    """Accept unknown exit telemetry only for strict crash-window recovery."""
    return_code = row.get("returnCode")
    if type(return_code) is int and return_code == 0:
        return True
    invocation = row.get("terminalizedByInvocation")
    evidence = row.get("reportEvidence")
    return (
        row.get("returnCode") is None
        and row.get("status") == "completed"
        and row.get("recoveredFromTerminalReport") is True
        and row.get("elapsedIncomplete") is True
        and isinstance(invocation, int)
        and not isinstance(invocation, bool)
        and invocation >= 1
        and isinstance(evidence, dict)
        and evidence.get("present") is True
        and row.get("runnerError") is None
    )


def manifest_rows(document: dict[str, Any], location: str) -> dict[str, dict[str, str]]:
    rows = document.get("cases")
    if not isinstance(rows, list):
        raise PublishError(f"{location}.cases must be an array")
    values: dict[str, dict[str, str]] = {}
    for index, row in enumerate(rows):
        row_location = f"{location}.cases[{index}]"
        if not isinstance(row, dict) or not isinstance(row.get("caseId"), str):
            raise PublishError(f"{row_location} is malformed")
        if set(row) != {"caseId", "schemaSha256", "sql1Sha256", "sql2Sha256"}:
            raise PublishError(f"{row_location} has noncanonical fields")
        case_id = row["caseId"]
        if not case_id or case_id in values:
            raise PublishError(f"{row_location} has an empty or duplicate caseId")
        normalized: dict[str, str] = {"caseId": case_id}
        for key in ("schemaSha256", "sql1Sha256", "sql2Sha256"):
            if not valid_sha256(row.get(key)):
                raise PublishError(f"{row_location}.{key} must be a lowercase SHA-256")
            normalized[key] = row[key]
        values[case_id] = normalized
    return values


def semantic_manifest_rows(
    document: dict[str, Any], location: str
) -> dict[str, dict[str, Any]]:
    rows = document.get("cases")
    if not isinstance(rows, list):
        raise PublishError(f"{location}.cases must be an array")
    values: dict[str, dict[str, Any]] = {}
    expected_keys = {
        "caseId",
        "flatCaseId",
        "metadataSha256",
        "semanticSidecarPath",
        "semanticSidecarSha256",
    }
    for index, row in enumerate(rows):
        row_location = f"{location}.cases[{index}]"
        if not isinstance(row, dict) or set(row) != expected_keys:
            raise PublishError(f"{row_location} has noncanonical fields")
        case_id = row.get("caseId")
        flat_case_id = row.get("flatCaseId")
        sidecar_path = row.get("semanticSidecarPath")
        sidecar_sha256 = row.get("semanticSidecarSha256")
        if (
            not isinstance(case_id, str)
            or not case_id
            or case_id in values
            or not isinstance(flat_case_id, str)
            or not flat_case_id
            or not valid_sha256(row.get("metadataSha256"))
            or ((sidecar_path is None) != (sidecar_sha256 is None))
            or (
                sidecar_path is not None
                and (
                    not isinstance(sidecar_path, str)
                    or not sidecar_path
                    or not valid_sha256(sidecar_sha256)
                )
            )
        ):
            raise PublishError(f"{row_location} is malformed")
        values[case_id] = dict(row)
    return values


def validate_input_manifests(
    record: Any,
    run_root: Path,
    expected_raw_cases: set[str],
) -> dict[str, Any]:
    input_path, input_digest = validate_file_binding(
        record,
        path_key="path",
        digest_key="sha256",
        location="configuration.inputManifest",
        run_root=run_root,
    )
    selected_path, selected_digest = validate_file_binding(
        record,
        path_key="selectedPath",
        digest_key="selectedSha256",
        location="configuration.inputManifest selected cohort",
        run_root=run_root,
    )
    semantic_path, semantic_digest = validate_file_binding(
        record,
        path_key="semanticAuthorityPath",
        digest_key="semanticAuthoritySha256",
        location="configuration.inputManifest semantic authority",
        run_root=run_root,
    )
    selected_semantic_path, selected_semantic_digest = validate_file_binding(
        record,
        path_key="selectedSemanticAuthorityPath",
        digest_key="selectedSemanticAuthoritySha256",
        location="configuration.inputManifest selected semantic authority",
        run_root=run_root,
    )
    assert isinstance(record, dict)
    if (
        record.get("algorithm") != INPUT_MANIFEST_ALGORITHM
        or record.get("caseCount") != 389
        or record.get("selectedCaseCount") != 389
        or record.get("expectedFrozenSha256") != FROZEN_INPUT_MANIFEST_SHA256
        or record.get("frozenVerified") is not True
        or record.get("semanticAuthorityAlgorithm")
        != SEMANTIC_INPUT_AUTHORITY_ALGORITHM
        or record.get("expectedFrozenSemanticAuthoritySha256")
        != FROZEN_SEMANTIC_INPUT_AUTHORITY_SHA256
        or record.get("frozenSemanticAuthorityVerified") is not True
    ):
        raise PublishError(
            "input-manifest binding violates the frozen 389-case contract"
        )
    document = load_json(input_path)
    selected_document = load_json(selected_path)
    semantic_document = load_json(semantic_path)
    selected_semantic_document = load_json(selected_semantic_path)
    if (
        input_digest != FROZEN_INPUT_MANIFEST_SHA256
        or selected_digest != FROZEN_INPUT_MANIFEST_SHA256
        or set(document) != {"schemaVersion", "algorithm", "caseCount", "cases"}
        or set(selected_document)
        != {"schemaVersion", "algorithm", "caseCount", "cases"}
        or document.get("schemaVersion") != 1
        or selected_document.get("schemaVersion") != 1
        or document.get("algorithm") != INPUT_MANIFEST_ALGORITHM
        or selected_document.get("algorithm") != INPUT_MANIFEST_ALGORITHM
        or document.get("caseCount") != 389
        or selected_document.get("caseCount") != 389
    ):
        raise PublishError(
            "input manifest content violates its canonical frozen schema"
        )
    if (
        semantic_digest != FROZEN_SEMANTIC_INPUT_AUTHORITY_SHA256
        or selected_semantic_digest != FROZEN_SEMANTIC_INPUT_AUTHORITY_SHA256
        or set(semantic_document)
        != {"schemaVersion", "algorithm", "caseCount", "cases"}
        or set(selected_semantic_document)
        != {"schemaVersion", "algorithm", "caseCount", "cases"}
        or semantic_document.get("schemaVersion") != 1
        or selected_semantic_document.get("schemaVersion") != 1
        or semantic_document.get("algorithm")
        != SEMANTIC_INPUT_AUTHORITY_ALGORITHM
        or selected_semantic_document.get("algorithm")
        != SEMANTIC_INPUT_AUTHORITY_ALGORITHM
        or semantic_document.get("caseCount") != 389
        or selected_semantic_document.get("caseCount") != 389
    ):
        raise PublishError(
            "semantic input authority violates its canonical frozen schema"
        )
    input_rows = manifest_rows(document, "input manifest")
    selected_rows = manifest_rows(selected_document, "selected input manifest")
    semantic_rows = semantic_manifest_rows(
        semantic_document, "semantic input authority"
    )
    selected_semantic_rows = semantic_manifest_rows(
        selected_semantic_document, "selected semantic input authority"
    )
    if (
        set(input_rows) != expected_raw_cases
        or set(selected_rows) != expected_raw_cases
        or set(semantic_rows) != expected_raw_cases
        or set(selected_semantic_rows) != expected_raw_cases
    ):
        raise PublishError(
            "input manifests do not contain the exact frozen 389-case cohort"
        )
    if input_rows != selected_rows or semantic_rows != selected_semantic_rows:
        raise PublishError(
            "selected input manifest differs from the full frozen input manifest"
        )
    canonical_document = {
        "schemaVersion": 1,
        "algorithm": INPUT_MANIFEST_ALGORITHM,
        "caseCount": 389,
        "cases": [input_rows[case] for case in sorted(input_rows)],
    }
    canonical_bytes = (
        json.dumps(canonical_document, sort_keys=True, separators=(",", ":")) + "\n"
    ).encode("utf-8")
    canonical_semantic_document = {
        "schemaVersion": 1,
        "algorithm": SEMANTIC_INPUT_AUTHORITY_ALGORITHM,
        "caseCount": 389,
        "cases": [semantic_rows[case] for case in sorted(semantic_rows)],
    }
    canonical_semantic_bytes = (
        json.dumps(
            canonical_semantic_document,
            sort_keys=True,
            separators=(",", ":"),
        )
        + "\n"
    ).encode("utf-8")
    if (
        input_path.read_bytes() != canonical_bytes
        or selected_path.read_bytes() != canonical_bytes
        or semantic_path.read_bytes() != canonical_semantic_bytes
        or selected_semantic_path.read_bytes() != canonical_semantic_bytes
    ):
        raise PublishError(
            "input manifests are not canonical byte-for-byte frozen manifests"
        )
    return {
        "path": input_path,
        "sha256": input_digest,
        "selectedPath": selected_path,
        "selectedSha256": selected_digest,
        "rows": input_rows,
        "semanticPath": semantic_path,
        "semanticSha256": semantic_digest,
        "selectedSemanticPath": selected_semantic_path,
        "selectedSemanticSha256": selected_semantic_digest,
        "semanticRows": semantic_rows,
    }


def validate_dynamic_linking(
    value: Any,
    executable_sha256: dict[str, str],
    expected_names: tuple[str, ...],
    location: str,
) -> int:
    value = require_exact_keys(
        value,
        {"algorithm", "consumerCount", "consumers", "fileCount", "files"},
        location,
    )
    if (
        value.get("algorithm") != TRUSTED_DYNAMIC_LINKING_ALGORITHM
        or not isinstance(value.get("consumers"), list)
        or value.get("consumerCount") != len(value["consumers"])
        or value.get("consumerCount") != len(expected_names)
        or not isinstance(value.get("files"), list)
        or not value["files"]
        or value.get("fileCount") != len(value["files"])
    ):
        raise PublishError(f"{location} is empty or malformed")
    files_by_mount: dict[str, dict[str, Any]] = {}
    for index, entry in enumerate(value["files"]):
        entry = require_exact_keys(
            entry,
            {"mountPath", "sourcePath", "sha256", "bytes"},
            f"{location}.files[{index}]",
        )
        mount_path = entry.get("mountPath") if isinstance(entry, dict) else None
        if (
            not isinstance(entry, dict)
            or not isinstance(mount_path, str)
            or not mount_path.startswith("/")
            or not isinstance(entry.get("sourcePath"), str)
            or not entry["sourcePath"]
            or not valid_sha256(entry.get("sha256"))
            or nonnegative_integer(entry.get("bytes"), f"{location}.files[{index}]")
            == 0
            or mount_path in files_by_mount
        ):
            raise PublishError(f"{location}.files[{index}] is malformed")
        files_by_mount[mount_path] = entry
    if list(files_by_mount) != sorted(files_by_mount):
        raise PublishError(f"{location}.files are not canonically ordered")

    consumers = value["consumers"]
    if [entry.get("name") for entry in consumers if isinstance(entry, dict)] != list(
        expected_names
    ):
        raise PublishError(f"{location}.consumers are incomplete or reordered")
    for index, consumer in enumerate(consumers):
        consumer = require_exact_keys(
            consumer,
            {
                "name",
                "executableSha256",
                "interpreterMountPath",
                "dependencyMountPaths",
            },
            f"{location}.consumers[{index}]",
        )
        name = consumer["name"]
        interpreter = consumer.get("interpreterMountPath")
        dependencies = consumer.get("dependencyMountPaths")
        if (
            consumer.get("executableSha256") != executable_sha256[name]
            or not isinstance(interpreter, str)
            or not interpreter.startswith("/")
            or interpreter not in files_by_mount
            or not isinstance(dependencies, list)
            or not dependencies
            or dependencies != sorted(set(dependencies))
            or any(
                not isinstance(path, str)
                or not path.startswith("/")
                or path not in files_by_mount
                for path in dependencies
            )
        ):
            raise PublishError(f"{location}.consumers[{index}] is malformed")
    return len(files_by_mount)


def validate_inspection_environment(value: Any) -> None:
    value = require_exact_keys(
        value,
        {
            "policy",
            "parentEnvironmentInherited",
            "workingDirectory",
            "allowedVariableCount",
            "allowedVariables",
        },
        "trusted inspection environment",
    )
    allowed = value.get("allowedVariables")
    if (
        value.get("policy") != TRUSTED_INSPECTION_ENVIRONMENT_POLICY
        or value.get("parentEnvironmentInherited") is not False
        or value.get("workingDirectory") != "/"
        or value.get("allowedVariableCount")
        != len(TRUSTED_INSPECTION_ENVIRONMENT_VARIABLES)
        or allowed != list(TRUSTED_INSPECTION_ENVIRONMENT_VARIABLES)
        or any(
            not isinstance(row, dict) or set(row) != {"name", "value"}
            for row in allowed or []
        )
    ):
        raise PublishError("trusted inspection environment is not the fixed C policy")


def validate_optional_system_configuration(
    value: Any,
    *,
    algorithm: str,
    selection_policy: str,
    expected_paths: tuple[str, ...],
    expected_states: tuple[str, ...],
    location: str,
) -> tuple[int, int]:
    value = require_exact_keys(
        value,
        {
            "algorithm",
            "selectionPolicy",
            "pathCount",
            "presentPathCount",
            "absentPathCount",
            "paths",
        },
        location,
    )
    rows = value.get("paths")
    if (
        value.get("algorithm") != algorithm
        or value.get("selectionPolicy") != selection_policy
        or not isinstance(rows, list)
        or len(rows) != len(expected_paths)
        or value.get("pathCount") != len(rows)
        or [row.get("selectedPath") for row in rows if isinstance(row, dict)]
        != list(expected_paths)
        or [row.get("state") for row in rows if isinstance(row, dict)]
        != list(expected_states)
    ):
        raise PublishError(f"{location} is incomplete, reordered, or malformed")

    present_count = 0
    for index, (row, state) in enumerate(zip(rows, expected_states, strict=True)):
        row_location = f"{location}.paths[{index}]"
        if state == "absent":
            require_exact_keys(row, {"selectedPath", "state"}, row_location)
            continue
        row = require_exact_keys(
            row,
            {
                "selectedPath",
                "state",
                "selectedPathIsSymlink",
                "selectedPathSymlinkTarget",
                "resolvedPath",
                "resolvedMode",
                "sha256",
                "bytes",
            },
            row_location,
        )
        if (
            not isinstance(row.get("selectedPathIsSymlink"), bool)
            or (
                row["selectedPathIsSymlink"]
                and (
                    not isinstance(row.get("selectedPathSymlinkTarget"), str)
                    or not row["selectedPathSymlinkTarget"]
                )
            )
            or (
                not row["selectedPathIsSymlink"]
                and row.get("selectedPathSymlinkTarget") is not None
            )
            or not isinstance(row.get("resolvedPath"), str)
            or not row["resolvedPath"].startswith("/")
            or not isinstance(row.get("resolvedMode"), str)
            or re.fullmatch(r"[0-7]{4}", row["resolvedMode"]) is None
            or not valid_sha256(row.get("sha256"))
            or nonnegative_integer(row.get("bytes"), f"{row_location}.bytes") == 0
        ):
            raise PublishError(f"{row_location} has invalid present-file evidence")
        present_count += 1
    absent_count = len(rows) - present_count
    if (
        value.get("presentPathCount") != present_count
        or value.get("absentPathCount") != absent_count
    ):
        raise PublishError(f"{location} summary counts do not reconcile")
    return present_count, absent_count


def validate_ldd_runtime_loaders(value: Any) -> tuple[int, int]:
    location = "trusted ldd runtime-loader closure"
    value = require_exact_keys(
        value,
        {
            "algorithm",
            "declaration",
            "selectionPolicy",
            "candidateCount",
            "presentCandidateCount",
            "absentCandidateCount",
            "candidates",
        },
        location,
    )
    expected = (
        (
            "/lib/ld-linux.so.2",
            "present",
            "8bfac642322e3e03bbf5cb7f8ffed50ee8a8119f0ce7d9da9dd54cb961436abf",
        ),
        (
            "/lib64/ld-linux-x86-64.so.2",
            "present",
            "db61dfe5ac2fb5522cc111df698146d187b13cbfb73684f190f58217b8dbeec4",
        ),
        ("/libx32/ld-linux-x32.so.2", "absent", None),
    )
    rows = value.get("candidates")
    if (
        value.get("algorithm") != TRUSTED_LDD_RUNTIME_LOADER_ALGORITHM
        or value.get("declaration") != "RTLDLIST"
        or value.get("selectionPolicy") != "ordered-first-present-compatible-loader-v1"
        or not isinstance(rows, list)
        or len(rows) != len(expected)
        or value.get("candidateCount") != len(rows)
    ):
        raise PublishError(f"{location} is empty or malformed")
    for index, (row, (path, state, expected_sha256)) in enumerate(
        zip(rows, expected, strict=True), start=1
    ):
        row_location = f"{location}.candidates[{index - 1}]"
        if state == "absent":
            row = require_exact_keys(
                row, {"ordinal", "selectedPath", "state"}, row_location
            )
        else:
            row = require_exact_keys(
                row,
                {
                    "ordinal",
                    "selectedPath",
                    "state",
                    "selectedPathIsSymlink",
                    "selectedPathSymlinkTarget",
                    "resolvedPath",
                    "resolvedMode",
                    "sha256",
                    "bytes",
                    "executableCheckPassed",
                    "elfCheck",
                },
                row_location,
            )
            elf_check = require_exact_keys(
                row.get("elfCheck"), {"passed", "magicHex"}, f"{row_location}.elfCheck"
            )
            if (
                not isinstance(row.get("selectedPathIsSymlink"), bool)
                or (
                    row["selectedPathIsSymlink"]
                    and (
                        not isinstance(row.get("selectedPathSymlinkTarget"), str)
                        or not row["selectedPathSymlinkTarget"]
                    )
                )
                or (
                    not row["selectedPathIsSymlink"]
                    and row.get("selectedPathSymlinkTarget") is not None
                )
                or not isinstance(row.get("resolvedPath"), str)
                or not row["resolvedPath"].startswith("/")
                or re.fullmatch(r"[0-7]{4}", row.get("resolvedMode", "")) is None
                or row.get("sha256") != expected_sha256
                or nonnegative_integer(row.get("bytes"), f"{row_location}.bytes") == 0
                or row.get("executableCheckPassed") is not True
                or elf_check != {"passed": True, "magicHex": "7f454c46"}
            ):
                raise PublishError(f"{row_location} has invalid loader evidence")
        if (
            row.get("ordinal") != index
            or row.get("selectedPath") != path
            or row.get("state") != state
        ):
            raise PublishError(f"{location} is reordered or has changed state")
    present_count = sum(state == "present" for _, state, _ in expected)
    absent_count = len(expected) - present_count
    if (
        value.get("presentCandidateCount") != present_count
        or value.get("absentCandidateCount") != absent_count
    ):
        raise PublishError(f"{location} summary counts do not reconcile")
    return present_count, absent_count


def validate_system_identity_configuration(value: Any) -> tuple[int, int]:
    location = "trusted system identity configuration"
    value = require_exact_keys(
        value,
        {
            "algorithm",
            "selectionPolicy",
            "pathCount",
            "presentPathCount",
            "absentPathCount",
            "paths",
        },
        location,
    )
    rows = value.get("paths")
    if (
        value.get("algorithm") != TRUSTED_SYSTEM_IDENTITY_CONFIGURATION_ALGORITHM
        or value.get("selectionPolicy") != "fixed-system-identity-paths-v1"
        or not isinstance(rows, list)
        or len(rows) != len(TRUSTED_SYSTEM_IDENTITY_CONFIGURATION_PATHS)
        or value.get("pathCount") != len(rows)
        or [row.get("path") for row in rows if isinstance(row, dict)]
        != list(TRUSTED_SYSTEM_IDENTITY_CONFIGURATION_PATHS)
    ):
        raise PublishError(f"{location} is incomplete, reordered, or malformed")
    for index, row in enumerate(rows):
        row = require_exact_keys(
            row,
            {"path", "present", "resolvedPath", "sha256", "bytes"},
            f"{location}.paths[{index}]",
        )
        if (
            row.get("present") is not True
            or row.get("resolvedPath") != row.get("path")
            or not valid_sha256(row.get("sha256"))
            or nonnegative_integer(row.get("bytes"), f"{location}.paths[{index}].bytes")
            == 0
        ):
            raise PublishError(
                f"{location}.paths[{index}] has invalid required-file evidence"
            )
    present_count = len(rows)
    if (
        value.get("presentPathCount") != present_count
        or value.get("absentPathCount") != 0
    ):
        raise PublishError(f"{location} summary counts do not reconcile")
    return present_count, 0


def validate_rocq_runtime_snapshot(record: Any, run_root: Path) -> dict[str, Any]:
    record = require_exact_keys(
        record,
        {
            "root",
            "manifestPath",
            "manifestSha256",
            "schemaVersion",
            "algorithm",
            "policy",
            "directoryCount",
            "fileCount",
            "totalBytes",
        },
        "configuration.rocqRuntimeSnapshot",
    )
    manifest_path, manifest_digest = validate_file_binding(
        record,
        path_key="manifestPath",
        digest_key="manifestSha256",
        location="configuration.rocqRuntimeSnapshot",
        run_root=run_root,
        expected_path=run_root / "trusted-rocq-runtime-manifest.json",
    )
    root = resolve_recorded_directory(
        record.get("root"), "configuration.rocqRuntimeSnapshot.root", run_root
    )
    if root != (run_root / "runtime/trusted-rocq-switch").resolve():
        raise PublishError(
            "configuration.rocqRuntimeSnapshot.root is not the run-private snapshot"
        )
    validators = runner_validators()
    try:
        document, observed_digest = validators[
            "read_trusted_rocq_runtime_snapshot_manifest"
        ](manifest_path)
        validators["verify_trusted_rocq_runtime_snapshot_tree"](root, document)
    except Exception as error:
        raise PublishError(
            f"trusted Rocq runtime snapshot failed runner validation: {error}"
        ) from error
    expected_summary = {
        "schemaVersion": TRUSTED_ROCQ_RUNTIME_SNAPSHOT_SCHEMA_VERSION,
        "algorithm": TRUSTED_ROCQ_RUNTIME_SNAPSHOT_ALGORITHM,
        "policy": TRUSTED_ROCQ_RUNTIME_SNAPSHOT_POLICY,
        "directoryCount": document.get("directoryCount"),
        "fileCount": document.get("fileCount"),
        "totalBytes": document.get("totalBytes"),
    }
    if (
        observed_digest != manifest_digest
        or any(record.get(key) != value for key, value in expected_summary.items())
    ):
        raise PublishError("trusted Rocq runtime snapshot record drifted")
    return {
        "root": root,
        "manifestPath": manifest_path,
        "manifestSha256": manifest_digest,
        "document": document,
        **expected_summary,
    }


def validate_rocq_authority_snapshot(
    record: Any,
    run_root: Path,
    runtime_snapshot: dict[str, Any],
    framework_source_tree: dict[str, Any],
) -> dict[str, Any]:
    record = require_exact_keys(
        record,
        {
            "root",
            "manifestPath",
            "manifestSha256",
            "schemaVersion",
            "algorithm",
            "policy",
            "sourceObjectPairCount",
            "fileCount",
            "totalBytes",
        },
        "configuration.rocqAuthoritySnapshot",
    )
    manifest_path, manifest_digest = validate_file_binding(
        record,
        path_key="manifestPath",
        digest_key="manifestSha256",
        location="configuration.rocqAuthoritySnapshot",
        run_root=run_root,
        expected_path=run_root / "trusted-rocq-authority-manifest.json",
    )
    root = resolve_recorded_directory(
        record.get("root"), "configuration.rocqAuthoritySnapshot.root", run_root
    )
    if root != (run_root / "runtime/trusted-rocq-authority").resolve():
        raise PublishError(
            "configuration.rocqAuthoritySnapshot.root is not the run-private snapshot"
        )
    validators = runner_validators()
    try:
        document, observed_digest = validators[
            "read_rocq_authority_snapshot_manifest"
        ](manifest_path)
        validators["verify_rocq_authority_snapshot_tree"](root, document)
        validators["validate_rocq_authority_external_bindings"](
            document,
            {
                key: value
                for key, value in runtime_snapshot.items()
                if key not in {"document", "root", "manifestPath"}
            }
            | {
                "root": validators["workspace_display_path"](
                    runtime_snapshot["root"]
                ),
                "manifestPath": validators["workspace_display_path"](
                    runtime_snapshot["manifestPath"]
                ),
            },
            framework_source_tree,
        )
    except Exception as error:
        raise PublishError(
            f"trusted Rocq authority snapshot failed runner validation: {error}"
        ) from error
    expected_summary = {
        "schemaVersion": TRUSTED_ROCQ_AUTHORITY_SNAPSHOT_SCHEMA_VERSION,
        "algorithm": TRUSTED_ROCQ_AUTHORITY_SNAPSHOT_ALGORITHM,
        "policy": TRUSTED_ROCQ_AUTHORITY_SNAPSHOT_POLICY,
        "sourceObjectPairCount": document.get("sourceObjectPairCount"),
        "fileCount": document.get("fileCount"),
        "totalBytes": document.get("totalBytes"),
    }
    if (
        observed_digest != manifest_digest
        or any(record.get(key) != value for key, value in expected_summary.items())
    ):
        raise PublishError("trusted Rocq authority snapshot record drifted")
    build_log = document.get("buildLog")
    build_log_path, build_log_digest = validate_file_binding(
        build_log,
        path_key="path",
        digest_key="sha256",
        location="trusted Rocq authority buildLog",
        run_root=run_root,
        expected_path=run_root / "trusted-rocq-authority-build.log",
    )
    if build_log.get("bytes") != build_log_path.stat().st_size:
        raise PublishError("trusted Rocq authority build log byte count drifted")
    return {
        "root": root,
        "manifestPath": manifest_path,
        "manifestSha256": manifest_digest,
        "document": document,
        "buildLogPath": build_log_path,
        "buildLogSha256": build_log_digest,
        **expected_summary,
    }


def validate_rocq_snapshot_trusted_stack_binding(
    runtime_snapshot: dict[str, Any],
    authority_snapshot: dict[str, Any],
    trusted_stack: dict[str, Any],
) -> None:
    if trusted_stack.get("sourceObjects") != authority_snapshot.get("document", {}).get(
        "sourceObjects"
    ):
        raise PublishError(
            "trusted-stack source/object authority differs from the immutable snapshot"
        )
    for name, snapshot in (
        ("rocqRuntimeSnapshot", runtime_snapshot),
        ("rocqAuthoritySnapshot", authority_snapshot),
    ):
        summary = {
            key: value
            for key, value in snapshot.items()
            if key
            not in {
                "document",
                "root",
                "manifestPath",
                "buildLogPath",
                "buildLogSha256",
            }
        }
        summary.update(
            {
                "root": runner_validators()["workspace_display_path"](
                    snapshot["root"]
                ),
                "manifestPath": runner_validators()["workspace_display_path"](
                    snapshot["manifestPath"]
                ),
            }
        )
        if trusted_stack.get(name) != summary:
            raise PublishError(f"trusted-stack {name} binding drifted")


def copy_rocq_authority_snapshot(
    snapshot: dict[str, Any], destination_root: Path
) -> None:
    manifest_copy = destination_root / "trusted-rocq-authority-manifest.json"
    shutil.copyfile(snapshot["manifestPath"], manifest_copy)
    if sha256(manifest_copy) != snapshot["manifestSha256"]:
        raise PublishError("trusted Rocq authority manifest changed while being copied")
    manifest_copy.chmod(0o444)
    tree_copy = destination_root / "trusted-rocq-authority"
    shutil.copytree(snapshot["root"], tree_copy, copy_function=shutil.copy2)
    try:
        copied_document, copied_digest = runner_validators()[
            "read_rocq_authority_snapshot_manifest"
        ](manifest_copy)
        runner_validators()["verify_rocq_authority_snapshot_tree"](
            tree_copy, copied_document
        )
    except Exception as error:
        raise PublishError(
            f"canonical Rocq authority snapshot copy failed validation: {error}"
        ) from error
    if (
        copied_digest != snapshot["manifestSha256"]
        or copied_document != snapshot["document"]
    ):
        raise PublishError("canonical Rocq authority snapshot copy drifted")


def finalize_staged_rocq_authority(
    staging: Path, output: Path, snapshot: dict[str, Any]
) -> None:
    """Publish the already validated snapshot tree and manifest from staging."""

    staged_tree = staging / "trusted-rocq-authority"
    staged_manifest = staging / "trusted-rocq-authority-manifest.json"
    if not staged_tree.is_dir() or staged_tree.is_symlink():
        raise PublishError("staged canonical Rocq authority tree is missing")
    if not staged_manifest.is_file() or staged_manifest.is_symlink():
        raise PublishError("staged canonical Rocq authority manifest is missing")
    target_tree = output / "trusted-rocq-authority"
    target_manifest = output / "trusted-rocq-authority-manifest.json"
    backup_tree = output / (
        ".trusted-rocq-authority.previous-" + str(os.getpid())
    )
    backup_manifest = output / (
        ".trusted-rocq-authority-manifest.previous-" + str(os.getpid()) + ".json"
    )
    if (
        backup_tree.exists()
        or backup_tree.is_symlink()
        or backup_manifest.exists()
        or backup_manifest.is_symlink()
    ):
        raise PublishError("stale canonical Rocq authority backup exists")
    prior_tree_exists = target_tree.exists() or target_tree.is_symlink()
    prior_manifest_exists = target_manifest.exists() or target_manifest.is_symlink()
    if prior_tree_exists != prior_manifest_exists:
        raise PublishError("existing canonical Rocq authority pair is incomplete")
    had_prior = prior_tree_exists
    if had_prior:
        if (
            target_tree.is_symlink()
            or not target_tree.is_dir()
            or target_manifest.is_symlink()
            or not target_manifest.is_file()
        ):
            raise PublishError("existing canonical Rocq authority pair is malformed")
        try:
            prior_document, _ = runner_validators()[
                "read_rocq_authority_snapshot_manifest"
            ](target_manifest)
            runner_validators()["verify_rocq_authority_snapshot_tree"](
                target_tree, prior_document
            )
        except Exception as error:
            raise PublishError(
                f"existing canonical Rocq authority failed validation: {error}"
            ) from error
        os.replace(target_tree, backup_tree)
        try:
            os.replace(target_manifest, backup_manifest)
        except BaseException:
            os.replace(backup_tree, target_tree)
            raise

    def remove_tree(path: Path) -> None:
        if path.exists() and not path.is_symlink():
            runner_validators()["make_tree_writable_for_cleanup"](path)
            shutil.rmtree(path)

    try:
        # Some filesystems reject cross-parent renames of a non-writable
        # directory even when both parents are writable. The staged copy is
        # not authoritative until validation below, so open only its root for
        # the rename and restore the immutable mode immediately afterward.
        staged_tree.chmod(0o755)
        os.replace(staged_tree, target_tree)
        target_tree.chmod(0o555)
        os.replace(staged_manifest, target_manifest)
        document, digest = runner_validators()[
            "read_rocq_authority_snapshot_manifest"
        ](target_manifest)
        runner_validators()["verify_rocq_authority_snapshot_tree"](
            target_tree, document
        )
        if digest != snapshot["manifestSha256"] or document != snapshot["document"]:
            raise PublishError("published canonical Rocq authority snapshot drifted")
    except Exception as error:
        remove_tree(target_tree)
        target_manifest.unlink(missing_ok=True)
        if had_prior:
            os.replace(backup_tree, target_tree)
            os.replace(backup_manifest, target_manifest)
        if isinstance(error, PublishError):
            raise
        raise PublishError(
            f"published canonical Rocq authority failed validation: {error}"
        ) from error
    if had_prior:
        remove_tree(backup_tree)
        backup_manifest.unlink()


def validate_trusted_stack(
    record: Any, run_root: Path, *, legacy_catalog: bool = False
) -> dict[str, Any]:
    record = require_exact_keys(
        record,
        {
            "manifestPath",
            "manifestSha256",
            "manifestSchemaVersion",
            "algorithm",
            "dynamicLinkingAlgorithm",
            "rocqRuntimeSnapshot",
            "rocqAuthoritySnapshot",
            "sourceObjectPairCount",
            "rocqStdlibObjectCount",
            "rocqRuntimeComponentCount",
            "rocqRuntimeConfigurationCount",
            "trustedExecutableCount",
            "dynamicRuntimeFileCount",
            "trustedHostToolCount",
            "trustedHostDynamicRuntimeFileCount",
            "trustedInspectionEnvironmentPolicy",
            "trustedInspectionEnvironmentVariableCount",
            "lddRuntimeLoaderCandidateCount",
            "lddRuntimeLoaderClosureAlgorithm",
            "lddRuntimeLoaderPresentCandidateCount",
            "lddRuntimeLoaderAbsentCandidateCount",
            "systemResolverConfigurationPathCount",
            "systemResolverConfigurationAlgorithm",
            "systemResolverConfigurationPresentPathCount",
            "systemResolverConfigurationAbsentPathCount",
            "systemIdentityConfigurationPathCount",
            "systemIdentityConfigurationAlgorithm",
            "systemIdentityConfigurationPresentPathCount",
            "systemIdentityConfigurationAbsentPathCount",
            "rocqExecutable",
            "rocqCheckExecutable",
            "rocqWorkerExecutable",
            "rocqNativeExecutable",
            "bwrapExecutable",
            "trustedCheckerEnvironmentPolicy",
            "proofAgentLauncherEnvironmentPolicy",
        },
        "configuration.trustedStack",
    )
    path, digest = validate_file_binding(
        record,
        path_key="manifestPath",
        digest_key="manifestSha256",
        location="configuration.trustedStack",
        run_root=run_root,
    )
    document = load_json(path)
    require_exact_keys(
        document,
        {
            "schemaVersion",
            "algorithm",
            "rocqOpamSwitch",
            "rocqRuntimeSnapshot",
            "rocqAuthoritySnapshot",
            "executables",
            "dynamicLinking",
            "trustedHostTools",
            "trustedScripts",
            "sourceObjects",
            "rocqStdlib",
            "rocqRuntime",
        },
        "trusted-stack manifest",
    )
    source_objects = document.get("sourceObjects")
    stdlib = document.get("rocqStdlib")
    runtime = document.get("rocqRuntime")
    executables = document.get("executables")
    dynamic = document.get("dynamicLinking")
    host_tools = document.get("trustedHostTools")
    scripts = document.get("trustedScripts")
    runtime_configuration = (
        runtime.get("configuration") if isinstance(runtime, dict) else None
    )
    if (
        record.get("algorithm") != TRUSTED_STACK_MANIFEST_ALGORITHM
        or record.get("manifestSchemaVersion") != TRUSTED_STACK_MANIFEST_SCHEMA_VERSION
        or record.get("dynamicLinkingAlgorithm") != TRUSTED_DYNAMIC_LINKING_ALGORITHM
        or document.get("schemaVersion") != TRUSTED_STACK_MANIFEST_SCHEMA_VERSION
        or document.get("algorithm") != TRUSTED_STACK_MANIFEST_ALGORITHM
        or record.get("rocqRuntimeSnapshot")
        != document.get("rocqRuntimeSnapshot")
        or record.get("rocqAuthoritySnapshot")
        != document.get("rocqAuthoritySnapshot")
        or not isinstance(document.get("rocqOpamSwitch"), str)
        or not document["rocqOpamSwitch"]
        or not isinstance(source_objects, list)
        or not source_objects
        or record.get("sourceObjectPairCount") != len(source_objects)
        or not isinstance(stdlib, dict)
        or not isinstance(stdlib.get("objects"), list)
        or not stdlib["objects"]
        or stdlib.get("objectCount") != len(stdlib["objects"])
        or record.get("rocqStdlibObjectCount") != len(stdlib["objects"])
        or not isinstance(runtime, dict)
        or not isinstance(runtime.get("components"), list)
        or not runtime["components"]
        or runtime.get("componentCount") != len(runtime["components"])
        or record.get("rocqRuntimeComponentCount") != len(runtime["components"])
        or runtime.get("configurationSelection") != "nonempty-findlib-meta-conf-v1"
        or not isinstance(runtime_configuration, list)
        or not runtime_configuration
        or runtime.get("configurationCount") != len(runtime_configuration)
        or record.get("rocqRuntimeConfigurationCount") != len(runtime_configuration)
        or not isinstance(executables, dict)
        or set(executables) != set(TRUSTED_EXECUTABLE_NAMES)
        or record.get("trustedExecutableCount") != len(TRUSTED_EXECUTABLE_NAMES)
        or record.get("rocqExecutable") != executables["rocq"]
        or record.get("rocqCheckExecutable") != executables["rocqchk"]
        or record.get("rocqWorkerExecutable") != executables["rocqworker"]
        or record.get("rocqNativeExecutable") != executables["rocqnative"]
        or record.get("bwrapExecutable") != executables["bwrap"]
        or not isinstance(host_tools, dict)
        or host_tools.get("selectionPolicy") != "first-executable-in-sanitized-path-v1"
        or not isinstance(host_tools.get("searchPath"), str)
        or not host_tools["searchPath"]
        or not isinstance(host_tools.get("tools"), list)
        or host_tools.get("toolCount") != len(host_tools["tools"])
        or host_tools.get("toolCount") != len(TRUSTED_HOST_TOOL_NAMES)
        or record.get("trustedHostToolCount") != len(TRUSTED_HOST_TOOL_NAMES)
        or not isinstance(host_tools.get("dynamicLinking"), dict)
        or record.get("trustedHostDynamicRuntimeFileCount")
        != host_tools["dynamicLinking"].get("fileCount")
        or not isinstance(scripts, list)
        or not scripts
    ):
        raise PublishError("trusted-stack manifest is empty, malformed, or unbound")
    canonical = (
        json.dumps(document, sort_keys=True, separators=(",", ":")) + "\n"
    ).encode("utf-8")
    if path.read_bytes() != canonical:
        raise PublishError("trusted-stack manifest is not canonical JSON")
    for name in TRUSTED_EXECUTABLE_NAMES:
        executable = executables[name]
        expected_keys = {"path", "sha256", "bytes"}
        if name == "bwrap":
            expected_keys |= {
                "selectionPolicy",
                "runtimeSnapshotManifestSha256",
                "selectedPath",
                "selectedPathIsSymlink",
            }
        executable = require_exact_keys(
            executable, expected_keys, f"trusted stack executable {name}"
        )
        if (
            not isinstance(executable.get("path"), str)
            or not executable["path"]
            or not valid_sha256(executable.get("sha256"))
            or nonnegative_integer(
                executable.get("bytes"), f"trusted stack executable {name}.bytes"
            )
            == 0
        ):
            raise PublishError(f"trusted stack executable {name} is malformed")
    bwrap = executables["bwrap"]
    expected_bwrap = (
        resolve_recorded_directory(
            nested(record, "rocqRuntimeSnapshot", "root"),
            "trustedStack.rocqRuntimeSnapshot.root",
            run_root,
        )
        / "_opam/bin/bwrap"
    )
    stack_switch = resolve_recorded_directory(
        document.get("rocqOpamSwitch"),
        "trusted stack rocqOpamSwitch",
        run_root,
    )
    runtime_snapshot_root = resolve_recorded_directory(
        nested(record, "rocqRuntimeSnapshot", "root"),
        "trustedStack.rocqRuntimeSnapshot.root",
        run_root,
    )
    if stack_switch != runtime_snapshot_root:
        raise PublishError("trusted stack Rocq switch differs from runtime snapshot")
    if (
        bwrap.get("selectionPolicy") != "exact-run-private-switch-path-v1"
        or bwrap.get("runtimeSnapshotManifestSha256")
        != nested(record, "rocqRuntimeSnapshot", "manifestSha256")
        or bwrap.get("selectedPath") != str(expected_bwrap)
        or bwrap.get("selectedPathIsSymlink") is not False
        or resolve_recorded_file(
            bwrap.get("path"), "trusted stack bwrap.path", run_root
        )
        != expected_bwrap
    ):
        raise PublishError("trusted bwrap path selection is not fixed and bound")

    require_exact_keys(
        stdlib, {"root", "objectCount", "objects"}, "trusted Rocq stdlib"
    )
    require_exact_keys(
        runtime,
        {
            "root",
            "componentCount",
            "components",
            "configurationSelection",
            "configurationCount",
            "configuration",
        },
        "trusted Rocq runtime",
    )
    if (
        resolve_recorded_directory(
            stdlib.get("root"), "trusted Rocq stdlib.root", run_root
        )
        != stack_switch / "_opam/lib/coq"
        or resolve_recorded_directory(
            runtime.get("root"), "trusted Rocq runtime.root", run_root
        )
        != stack_switch / "_opam/lib"
    ):
        raise PublishError("trusted Rocq stack roots escape the runtime snapshot")
    runtime_configuration_paths: list[str] = []
    for index, entry in enumerate(runtime_configuration):
        entry = require_exact_keys(
            entry,
            {"path", "sha256", "bytes"},
            f"trusted stack runtime configuration[{index}]",
        )
        if (
            not isinstance(entry.get("path"), str)
            or not entry["path"]
            or not valid_sha256(entry.get("sha256"))
            or nonnegative_integer(
                entry.get("bytes"),
                f"trusted stack runtime configuration[{index}].bytes",
            )
            == 0
        ):
            raise PublishError(
                f"trusted stack runtime configuration[{index}] is malformed"
            )
        runtime_configuration_paths.append(entry["path"])
    if runtime_configuration_paths != sorted(set(runtime_configuration_paths)) or not {
        "findlib.conf",
        "rocq-runtime/META",
    } <= set(runtime_configuration_paths):
        raise PublishError(
            "trusted stack runtime configuration is noncanonical or incomplete"
        )

    dynamic_file_count = validate_dynamic_linking(
        dynamic,
        {name: executables[name]["sha256"] for name in TRUSTED_EXECUTABLE_NAMES},
        TRUSTED_EXECUTABLE_NAMES,
        "trusted stack dynamic linking",
    )
    if record.get("dynamicRuntimeFileCount") != dynamic_file_count:
        raise PublishError("trusted stack dynamic-linking count is not cross-bound")

    require_exact_keys(
        host_tools,
        {
            "selectionPolicy",
            "searchPath",
            "toolCount",
            "tools",
            "inspectionEnvironment",
            "lddRuntimeLoaders",
            "systemResolverConfiguration",
            "systemIdentityConfiguration",
            "dynamicLinking",
        },
        "trusted host-tool closure",
    )
    search_parts = host_tools["searchPath"].split(os.pathsep)
    if (
        len(search_parts) != 3
        or not search_parts[0].endswith("/_opam/bin")
        or search_parts[1:] != ["/usr/bin", "/bin"]
    ):
        raise PublishError("trusted host-tool search path is not the sanitized path")
    tool_records = host_tools["tools"]
    if [entry.get("name") for entry in tool_records if isinstance(entry, dict)] != list(
        TRUSTED_HOST_TOOL_NAMES
    ):
        raise PublishError("trusted host tools are incomplete or reordered")
    tools_by_name: dict[str, dict[str, Any]] = {}
    for index, tool in enumerate(tool_records):
        expected_keys = {
            "name",
            "selectedPath",
            "resolvedPath",
            "selectedPathIsSymlink",
            "format",
            "sha256",
            "bytes",
        }
        if isinstance(tool, dict) and tool.get("name") == "ldd":
            expected_keys.add("scriptInterpreter")
        tool = require_exact_keys(tool, expected_keys, f"trusted host tools[{index}]")
        name = tool["name"]
        expected_format = "script" if name == "ldd" else "elf"
        if (
            not isinstance(tool.get("selectedPath"), str)
            or not tool["selectedPath"]
            or not isinstance(tool.get("resolvedPath"), str)
            or not tool["resolvedPath"]
            or not isinstance(tool.get("selectedPathIsSymlink"), bool)
            or tool.get("format") != expected_format
            or not valid_sha256(tool.get("sha256"))
            or nonnegative_integer(
                tool.get("bytes"), f"trusted host tools[{index}].bytes"
            )
            == 0
        ):
            raise PublishError(f"trusted host tools[{index}] is malformed")
        tools_by_name[name] = tool
    if (
        tools_by_name["bash"]["selectedPath"] != "/usr/bin/bash"
        or tools_by_name["timeout"]["selectedPath"] != "/usr/bin/timeout"
        or tools_by_name["dirname"]["selectedPath"] != "/usr/bin/dirname"
        or tools_by_name["readlink"]["selectedPath"] != "/usr/bin/readlink"
    ):
        raise PublishError("trusted fixed host-tool paths are not pinned")
    if (
        tools_by_name["ldd"]["selectedPath"] != TRUSTED_LDD_PATH
        or tools_by_name["ldd"]["resolvedPath"] != TRUSTED_LDD_PATH
        or tools_by_name["ldd"]["selectedPathIsSymlink"] is not False
        or tools_by_name["ldd"]["sha256"] not in TRUSTED_LDD_SHA256S
    ):
        raise PublishError("trusted ldd script path or reviewed digest changed")
    ldd_interpreter = tools_by_name["ldd"].get("scriptInterpreter")
    require_exact_keys(
        ldd_interpreter,
        {"path", "resolvedPath", "hostTool", "sha256"},
        "trusted ldd script interpreter",
    )
    if (
        ldd_interpreter.get("path") != "/bin/bash"
        or ldd_interpreter.get("hostTool") != "bash"
        or ldd_interpreter.get("resolvedPath") != tools_by_name["bash"]["resolvedPath"]
        or ldd_interpreter.get("sha256") != tools_by_name["bash"]["sha256"]
    ):
        raise PublishError("trusted ldd script interpreter is not bound to bash")
    host_elf_names = tuple(
        name
        for name in TRUSTED_HOST_TOOL_NAMES
        if tools_by_name[name]["format"] == "elf"
    )
    validate_dynamic_linking(
        host_tools["dynamicLinking"],
        {name: tools_by_name[name]["sha256"] for name in host_elf_names},
        host_elf_names,
        "trusted host-tool dynamic linking",
    )
    validate_inspection_environment(host_tools.get("inspectionEnvironment"))
    if record.get(
        "trustedInspectionEnvironmentPolicy"
    ) != TRUSTED_INSPECTION_ENVIRONMENT_POLICY or record.get(
        "trustedInspectionEnvironmentVariableCount"
    ) != len(TRUSTED_INSPECTION_ENVIRONMENT_VARIABLES):
        raise PublishError("trusted inspection environment is not cross-bound")

    loader_present, loader_absent = validate_ldd_runtime_loaders(
        host_tools.get("lddRuntimeLoaders")
    )
    loader_closure = host_tools["lddRuntimeLoaders"]
    if (
        record.get("lddRuntimeLoaderCandidateCount") != loader_closure["candidateCount"]
        or record.get("lddRuntimeLoaderClosureAlgorithm") != loader_closure["algorithm"]
        or record.get("lddRuntimeLoaderPresentCandidateCount") != loader_present
        or record.get("lddRuntimeLoaderAbsentCandidateCount") != loader_absent
    ):
        raise PublishError("trusted ldd runtime-loader closure is not cross-bound")

    resolver_present, resolver_absent = validate_optional_system_configuration(
        host_tools.get("systemResolverConfiguration"),
        algorithm=TRUSTED_SYSTEM_RESOLVER_CONFIGURATION_ALGORITHM,
        selection_policy="fixed-system-dynamic-loader-paths-v1",
        expected_paths=TRUSTED_SYSTEM_RESOLVER_CONFIGURATION_PATHS,
        expected_states=("present", "absent"),
        location="trusted system resolver configuration",
    )
    resolver = host_tools["systemResolverConfiguration"]
    if (
        record.get("systemResolverConfigurationPathCount") != resolver["pathCount"]
        or record.get("systemResolverConfigurationAlgorithm") != resolver["algorithm"]
        or record.get("systemResolverConfigurationPresentPathCount") != resolver_present
        or record.get("systemResolverConfigurationAbsentPathCount") != resolver_absent
    ):
        raise PublishError("trusted system resolver closure is not cross-bound")

    identity_present, identity_absent = validate_system_identity_configuration(
        host_tools.get("systemIdentityConfiguration")
    )
    identity = host_tools["systemIdentityConfiguration"]
    if (
        record.get("systemIdentityConfigurationPathCount") != identity["pathCount"]
        or record.get("systemIdentityConfigurationAlgorithm") != identity["algorithm"]
        or record.get("systemIdentityConfigurationPresentPathCount") != identity_present
        or record.get("systemIdentityConfigurationAbsentPathCount") != identity_absent
    ):
        raise PublishError("trusted system identity closure is not cross-bound")

    expected_environment = proof_agent_environment_configuration(
        legacy_catalog=legacy_catalog
    )
    if (
        record.get("trustedCheckerEnvironmentPolicy")
        != expected_environment["trustedCheckerEnvironmentPolicy"]
        or record.get("proofAgentLauncherEnvironmentPolicy")
        != expected_environment["proofAgentLauncherEnvironmentPolicy"]
    ):
        raise PublishError("trusted process environment policies are not exact")

    for location, entries, digest_key, bytes_key in (
        ("Rocq stdlib", stdlib["objects"], "sha256", "bytes"),
        ("Rocq runtime", runtime["components"], "sha256", "bytes"),
        ("trusted scripts", scripts, "sha256", "bytes"),
    ):
        observed_paths: list[str] = []
        for index, entry in enumerate(entries):
            expected_keys = {"path", digest_key, bytes_key}
            entry = require_exact_keys(
                entry, expected_keys, f"trusted stack {location}[{index}]"
            )
            if (
                not isinstance(entry.get("path"), str)
                or not entry["path"]
                or not valid_sha256(entry.get(digest_key))
                or nonnegative_integer(
                    entry.get(bytes_key),
                    f"trusted stack {location}[{index}].{bytes_key}",
                )
                == 0
            ):
                raise PublishError(f"trusted stack {location}[{index}] is malformed")
            observed_paths.append(entry["path"])
        if observed_paths != sorted(set(observed_paths)):
            raise PublishError(f"trusted stack {location} is not canonically ordered")
    for index, entry in enumerate(source_objects):
        entry = require_exact_keys(
            entry,
            {
                "sourcePath",
                "sourceSha256",
                "sourceBytes",
                "objectPath",
                "objectSha256",
                "objectBytes",
            },
            f"trusted stack source objects[{index}]",
        )
        if (
            not isinstance(entry.get("sourcePath"), str)
            or not entry["sourcePath"]
            or not isinstance(entry.get("objectPath"), str)
            or not entry["objectPath"]
            or not valid_sha256(entry.get("sourceSha256"))
            or not valid_sha256(entry.get("objectSha256"))
            or nonnegative_integer(
                entry.get("sourceBytes"),
                f"trusted stack source objects[{index}].sourceBytes",
            )
            == 0
            or nonnegative_integer(
                entry.get("objectBytes"),
                f"trusted stack source objects[{index}].objectBytes",
            )
            == 0
        ):
            raise PublishError(f"trusted stack source objects[{index}] is malformed")
    if [entry["sourcePath"] for entry in source_objects] != sorted(
        {entry["sourcePath"] for entry in source_objects}
    ):
        raise PublishError("trusted stack source objects are not canonically ordered")
    return {
        "path": path,
        "sha256": digest,
        "sourceObjects": source_objects,
        "rocqRuntimeSnapshot": document["rocqRuntimeSnapshot"],
        "rocqAuthoritySnapshot": document["rocqAuthoritySnapshot"],
    }


def require_manifest_entries(value: Any, location: str) -> list[dict[str, Any]]:
    if not isinstance(value, list) or not value:
        raise PublishError(f"{location} must be a nonempty array")
    for index, entry in enumerate(value):
        if not isinstance(entry, dict) or not isinstance(entry.get("path"), str):
            raise PublishError(f"{location}[{index}] is malformed")
        if entry.get("kind", "file") == "file" and (
            not valid_sha256(entry.get("sha256"))
            or not isinstance(entry.get("bytes"), int)
            or isinstance(entry.get("bytes"), bool)
            or entry["bytes"] < 0
        ):
            raise PublishError(f"{location}[{index}] has invalid file evidence")
    return value


def valid_executable_evidence(value: Any) -> bool:
    return (
        isinstance(value, dict)
        and isinstance(value.get("path"), str)
        and bool(value["path"])
        and valid_sha256(value.get("sha256"))
        and isinstance(value.get("bytes"), int)
        and not isinstance(value.get("bytes"), bool)
        and value["bytes"] > 0
    )


def validate_tree_manifest_entries(value: Any, location: str) -> list[dict[str, Any]]:
    if not isinstance(value, list) or not value:
        raise PublishError(f"{location} must be a nonempty array")
    observed_paths: list[str] = []
    for index, entry in enumerate(value):
        entry_location = f"{location}[{index}]"
        if not isinstance(entry, dict):
            raise PublishError(f"{entry_location} is malformed")
        kind = entry.get("kind")
        if kind == "file":
            entry = require_exact_keys(
                entry,
                {"path", "kind", "sha256", "bytes", "executable"},
                entry_location,
            )
            nonnegative_integer(entry.get("bytes"), f"{entry_location}.bytes")
            if not valid_sha256(entry.get("sha256")) or not isinstance(
                entry.get("executable"), bool
            ):
                raise PublishError(f"{entry_location} has invalid file evidence")
        elif kind == "symlink":
            entry = require_exact_keys(
                entry, {"path", "kind", "target"}, entry_location
            )
            if not isinstance(entry.get("target"), str) or not entry["target"]:
                raise PublishError(f"{entry_location} has invalid symlink evidence")
        else:
            raise PublishError(f"{entry_location} has a noncanonical kind")
        if not isinstance(entry.get("path"), str) or not entry["path"]:
            raise PublishError(f"{entry_location}.path must be nonempty")
        observed_paths.append(entry["path"])
    if observed_paths != sorted(set(observed_paths)):
        raise PublishError(f"{location} is not canonically ordered")
    return value


def validate_frontend_launch_environment(value: Any) -> int:
    location = "frontend launch environment"
    value = require_exact_keys(
        value,
        {
            "schemaVersion",
            "inheritedEnvironmentCleared",
            "fixedVariables",
            "hostEnvironmentAllowlist",
            "explicitContractVariables",
            "unlistedEnvironmentPolicy",
            "explicitlyExcludedVariables",
            "explicitlyExcludedPrefixes",
        },
        location,
    )
    fixed = [
        f"{row['name']}={row['value']}" for row in FRONTEND_FIXED_ENVIRONMENT_VARIABLES
    ]
    if value != {
        "schemaVersion": 1,
        "inheritedEnvironmentCleared": True,
        "fixedVariables": fixed,
        "hostEnvironmentAllowlist": [],
        "explicitContractVariables": list(FRONTEND_EXPLICIT_ENVIRONMENT_NAMES),
        "unlistedEnvironmentPolicy": "excluded_by_env_clear_before_process_start",
        "explicitlyExcludedVariables": list(FRONTEND_LAUNCH_EXCLUDED_VARIABLES),
        "explicitlyExcludedPrefixes": ["BASH_FUNC_"],
    }:
        raise PublishError(
            "frontend launch environment is not the fixed empty-base policy"
        )
    return len(fixed) + len(FRONTEND_EXPLICIT_ENVIRONMENT_NAMES)


def validate_frontend_launch_tools(value: Any) -> tuple[int, int]:
    location = "frontend launch tools"
    value = require_exact_keys(
        value,
        {
            "algorithm",
            "selectionPolicy",
            "shellExecutable",
            "shellArguments",
            "commandBody",
            "scriptArgument",
            "toolCount",
            "frozenDirectJavaToolNames",
            "frontendPreparationToolNames",
            "tools",
            "dynamicLinking",
        },
        location,
    )
    tools = value.get("tools")
    if (
        value.get("algorithm") != FRONTEND_LAUNCH_TOOLS_ALGORITHM
        or value.get("selectionPolicy") != "fixed-absolute-paths-v1"
        or value.get("shellExecutable") != FRONTEND_LAUNCH_BASH
        or value.get("shellArguments") != list(FRONTEND_LAUNCH_ARGUMENTS)
        or value.get("commandBody") != FRONTEND_LAUNCH_COMMAND_BODY
        or value.get("scriptArgument") != CANONICAL_FRONTEND_SCRIPT_DISPLAY
        or value.get("frozenDirectJavaToolNames") != ["bash", "dirname", "readlink"]
        or value.get("frontendPreparationToolNames") != list(FRONTEND_LAUNCH_TOOL_NAMES)
        or not isinstance(tools, list)
        or value.get("toolCount") != len(tools)
        or len(tools) != len(FRONTEND_LAUNCH_TOOL_NAMES)
        or [row.get("name") for row in tools if isinstance(row, dict)]
        != list(FRONTEND_LAUNCH_TOOL_NAMES)
    ):
        raise PublishError(f"{location} is incomplete, reordered, or malformed")
    tools_by_name: dict[str, dict[str, Any]] = {}
    for index, tool in enumerate(tools):
        tool = require_exact_keys(
            tool,
            {
                "name",
                "selectedPath",
                "resolvedPath",
                "selectedPathIsSymlink",
                "selectedPathSymlinkTarget",
                "format",
                "sha256",
                "bytes",
            },
            f"{location}[{index}]",
        )
        name = tool["name"]
        if (
            tool.get("selectedPath") != FRONTEND_LAUNCH_TOOL_PATHS[name]
            or not isinstance(tool.get("resolvedPath"), str)
            or not tool["resolvedPath"].startswith("/")
            or not isinstance(tool.get("selectedPathIsSymlink"), bool)
            or (
                tool["selectedPathIsSymlink"]
                and (
                    not isinstance(tool.get("selectedPathSymlinkTarget"), str)
                    or not tool["selectedPathSymlinkTarget"]
                )
            )
            or (
                not tool["selectedPathIsSymlink"]
                and tool.get("selectedPathSymlinkTarget") is not None
            )
            or tool.get("format") != "elf"
            or not valid_sha256(tool.get("sha256"))
            or nonnegative_integer(tool.get("bytes"), f"{location}[{index}].bytes") == 0
        ):
            raise PublishError(f"{location}[{index}] has invalid executable evidence")
        tools_by_name[name] = tool
    dynamic_file_count = validate_dynamic_linking(
        value.get("dynamicLinking"),
        {name: tools_by_name[name]["sha256"] for name in FRONTEND_LAUNCH_TOOL_NAMES},
        FRONTEND_LAUNCH_TOOL_NAMES,
        "frontend launch-tool dynamic linking",
    )
    return len(tools), dynamic_file_count


def validate_frontend_stack(record: Any, run_root: Path) -> dict[str, Any]:
    record = require_exact_keys(
        record,
        {
            "manifestPath",
            "manifestSha256",
            "manifestSchemaVersion",
            "algorithm",
            "canonicalCommand",
            "effectiveCommand",
            "executionMode",
            "sourceSqlTransport",
            "normalizationLayer",
            "launchEnvironmentAlgorithm",
            "launchEnvironmentPolicy",
            "launchEnvironmentVariableCount",
            "launchToolCount",
            "launchToolDynamicLinkingAlgorithm",
            "launchToolDynamicRuntimeFileCount",
            "javaVersion",
            "mavenVersion",
            "calciteClassCount",
            "dependencyCount",
        },
        "configuration.frontendStack",
    )
    path, digest = validate_file_binding(
        record,
        path_key="manifestPath",
        digest_key="manifestSha256",
        location="configuration.frontendStack",
        run_root=run_root,
    )
    document = load_json(path)
    require_exact_keys(
        document,
        {
            "schemaVersion",
            "algorithm",
            "canonicalCommand",
            "effectiveCommand",
            "executionMode",
            "sourceSqlTransport",
            "normalizationLayer",
            "launchEnvironmentAlgorithm",
            "launchEnvironment",
            "launchTools",
            "commandComponents",
            "java",
            "maven",
            "calcite",
        },
        "frontend-stack manifest",
    )
    java = document.get("java")
    maven = document.get("maven")
    calcite = document.get("calcite")
    launch_environment = document.get("launchEnvironment")
    launch_tools = document.get("launchTools")
    if (
        record.get("algorithm") != FRONTEND_STACK_MANIFEST_ALGORITHM
        or record.get("manifestSchemaVersion") != FRONTEND_STACK_MANIFEST_SCHEMA_VERSION
        or document.get("schemaVersion") != FRONTEND_STACK_MANIFEST_SCHEMA_VERSION
        or document.get("algorithm") != FRONTEND_STACK_MANIFEST_ALGORITHM
        or document.get("canonicalCommand") != CANONICAL_FRONTEND_COMMAND
        or document.get("effectiveCommand") != CANONICAL_FRONTEND_COMMAND
        or document.get("executionMode") != "direct-java-bound-classpath-v1"
        or document.get("sourceSqlTransport") != "exact-input-bytes-v1"
        or document.get("normalizationLayer") != "none"
        or record.get("canonicalCommand") != CANONICAL_FRONTEND_COMMAND
        or record.get("effectiveCommand") != CANONICAL_FRONTEND_COMMAND
        or record.get("executionMode") != "direct-java-bound-classpath-v1"
        or record.get("sourceSqlTransport") != "exact-input-bytes-v1"
        or record.get("normalizationLayer") != "none"
        or document.get("launchEnvironmentAlgorithm")
        != FRONTEND_LAUNCH_ENVIRONMENT_ALGORITHM
        or record.get("launchEnvironmentAlgorithm")
        != document.get("launchEnvironmentAlgorithm")
        or not isinstance(java, dict)
        or record.get("javaVersion") != java.get("version")
        or not isinstance(maven, dict)
        or record.get("mavenVersion") != maven.get("version")
        or not isinstance(calcite, dict)
        or record.get("calciteClassCount") != calcite.get("classCount")
        or record.get("dependencyCount") != calcite.get("dependencyCount")
        or not isinstance(calcite.get("classCount"), int)
        or calcite["classCount"] < 1
        or not isinstance(calcite.get("dependencyCount"), int)
        or calcite["dependencyCount"] < 1
        or not valid_sha256(calcite.get("classpathSha256"))
        or calcite.get("runtimeClasspathEnvironmentVariable")
        != "LOGOS_CALCITE_RUNTIME_CLASSPATH_FILE"
        or not isinstance(calcite.get("classpath"), list)
        or len(calcite["classpath"]) != calcite["dependencyCount"]
    ):
        raise PublishError("frontend-stack manifest is malformed or not canonical")

    launch_variable_count = validate_frontend_launch_environment(launch_environment)
    launch_tool_count, launch_dynamic_file_count = validate_frontend_launch_tools(
        launch_tools
    )
    if (
        record.get("launchEnvironmentPolicy")
        != launch_environment["unlistedEnvironmentPolicy"]
        or record.get("launchEnvironmentVariableCount") != launch_variable_count
        or record.get("launchToolCount") != launch_tool_count
        or record.get("launchToolDynamicLinkingAlgorithm")
        != launch_tools["dynamicLinking"]["algorithm"]
        or record.get("launchToolDynamicRuntimeFileCount") != launch_dynamic_file_count
    ):
        raise PublishError("frontend launch closure is not cross-bound")

    commands = document.get("commandComponents")
    if not isinstance(commands, list) or not commands:
        raise PublishError("frontend commands must be a nonempty array")
    command_paths: list[str] = []
    for index, command in enumerate(commands):
        command = require_exact_keys(
            command,
            {"path", "sha256", "bytes", "executable"},
            f"frontend commands[{index}]",
        )
        if (
            not isinstance(command.get("path"), str)
            or not command["path"]
            or not valid_sha256(command.get("sha256"))
            or nonnegative_integer(
                command.get("bytes"), f"frontend commands[{index}].bytes"
            )
            == 0
            or not isinstance(command.get("executable"), bool)
        ):
            raise PublishError(f"frontend commands[{index}] is malformed")
        command_paths.append(command["path"])
    if len(command_paths) != len(set(command_paths)):
        raise PublishError("frontend commands contain duplicate paths")

    java = require_exact_keys(
        java,
        {
            "javaHome",
            "jdkRoot",
            "javaInvocationPath",
            "javaExecutable",
            "version",
            "files",
        },
        "frontend JDK",
    )
    if (
        any(
            not isinstance(java.get(key), str) or not java[key]
            for key in ("javaHome", "jdkRoot", "javaInvocationPath", "version")
        )
        or not valid_executable_evidence(java.get("javaExecutable"))
        or set(java["javaExecutable"]) != {"path", "sha256", "bytes"}
    ):
        raise PublishError("frontend JDK record is malformed")
    validate_tree_manifest_entries(java.get("files"), "JDK files")

    maven = require_exact_keys(
        maven,
        {"root", "executable", "version", "files", "settings"},
        "frontend Maven",
    )
    if (
        not isinstance(maven.get("root"), str)
        or not maven["root"]
        or not isinstance(maven.get("version"), str)
        or not maven["version"]
        or not valid_executable_evidence(maven.get("executable"))
        or set(maven["executable"]) != {"path", "sha256", "bytes"}
    ):
        raise PublishError("frontend Maven record is malformed")
    validate_tree_manifest_entries(maven.get("files"), "Maven files")
    settings = require_exact_keys(
        maven.get("settings"),
        {"path", "present", "sha256", "bytes"},
        "frontend Maven settings",
    )
    if (
        settings.get("path") != "/nonexistent/.m2/settings.xml"
        or not isinstance(settings.get("present"), bool)
        or (
            settings["present"]
            and (
                not valid_sha256(settings.get("sha256"))
                or nonnegative_integer(
                    settings.get("bytes"), "frontend Maven settings.bytes"
                )
                == 0
            )
        )
        or (
            not settings["present"]
            and (
                settings.get("sha256") is not None or settings.get("bytes") is not None
            )
        )
    ):
        raise PublishError("frontend Maven settings record is malformed")

    calcite = require_exact_keys(
        calcite,
        {
            "classesRoot",
            "classCount",
            "classes",
            "classpathPath",
            "runtimeClasspathEnvironmentVariable",
            "classpathSha256",
            "classpath",
            "dependencyCount",
            "dependencies",
        },
        "frontend Calcite",
    )
    classes = validate_tree_manifest_entries(calcite.get("classes"), "Calcite classes")
    dependencies = calcite.get("dependencies")
    if not isinstance(dependencies, list) or not dependencies:
        raise PublishError("Calcite dependencies must be a nonempty array")
    for index, dependency in enumerate(dependencies):
        dependency = require_exact_keys(
            dependency,
            {"classpathIndex", "path", "sha256", "bytes"},
            f"Calcite dependencies[{index}]",
        )
        if (
            dependency.get("classpathIndex") != index
            or not isinstance(dependency.get("path"), str)
            or not dependency["path"]
            or not valid_sha256(dependency.get("sha256"))
            or nonnegative_integer(
                dependency.get("bytes"), f"Calcite dependencies[{index}].bytes"
            )
            == 0
        ):
            raise PublishError(f"Calcite dependencies[{index}] is malformed")
    if (
        not isinstance(calcite.get("classesRoot"), str)
        or not calcite["classesRoot"]
        or not isinstance(calcite.get("classpathPath"), str)
        or not calcite["classpathPath"]
        or not isinstance(calcite.get("classpath"), list)
        or len(calcite["classpath"]) != calcite["dependencyCount"]
        or any(not isinstance(item, str) or not item for item in calcite["classpath"])
    ):
        raise PublishError("frontend Calcite path closure is malformed")
    if (
        sum(entry.get("kind", "file") == "file" for entry in classes)
        != calcite["classCount"]
        or len(dependencies) != calcite["dependencyCount"]
        or [entry.get("classpathIndex") for entry in dependencies]
        != list(range(len(dependencies)))
        or [entry.get("path") for entry in dependencies] != calcite["classpath"]
    ):
        raise PublishError("frontend Calcite classpath closure does not reconcile")
    canonical = (
        json.dumps(document, sort_keys=True, separators=(",", ":")) + "\n"
    ).encode("utf-8")
    if path.read_bytes() != canonical:
        raise PublishError("frontend-stack manifest is not canonical JSON")
    return {
        "path": path,
        "sha256": digest,
        "launchEnvironment": launch_environment,
    }


def validate_lexical_executable(value: Any, location: str) -> dict[str, Any]:
    value = require_exact_keys(
        value,
        {"path", "kind", "symlinkTarget", "resolvedPath", "sha256", "bytes"},
        location,
    )
    if (
        not isinstance(value.get("path"), str)
        or not value["path"].startswith("/")
        or value.get("kind") not in {"file", "symlink"}
        or (
            value["kind"] == "symlink"
            and (
                not isinstance(value.get("symlinkTarget"), str)
                or not value["symlinkTarget"]
            )
        )
        or (value["kind"] == "file" and value.get("symlinkTarget") is not None)
        or not isinstance(value.get("resolvedPath"), str)
        or not value["resolvedPath"]
        or not valid_sha256(value.get("sha256"))
        or nonnegative_integer(value.get("bytes"), f"{location}.bytes") == 0
    ):
        raise PublishError(f"{location} is malformed")
    return value


def validate_fixed_tool_evidence(
    value: Any, *, name: str, selected_path: str, location: str
) -> dict[str, Any]:
    value = require_exact_keys(
        value,
        {
            "name",
            "selectedPath",
            "resolvedPath",
            "selectedPathIsSymlink",
            "selectedPathSymlinkTarget",
            "format",
            "sha256",
            "bytes",
        },
        location,
    )
    if (
        value.get("name") != name
        or value.get("selectedPath") != selected_path
        or not isinstance(value.get("resolvedPath"), str)
        or not value["resolvedPath"].startswith("/")
        or not isinstance(value.get("selectedPathIsSymlink"), bool)
        or (
            value["selectedPathIsSymlink"]
            and (
                not isinstance(value.get("selectedPathSymlinkTarget"), str)
                or not value["selectedPathSymlinkTarget"]
            )
        )
        or (
            not value["selectedPathIsSymlink"]
            and value.get("selectedPathSymlinkTarget") is not None
        )
        or value.get("format") != "elf"
        or not valid_sha256(value.get("sha256"))
        or nonnegative_integer(value.get("bytes"), f"{location}.bytes") == 0
    ):
        raise PublishError(f"{location} is malformed")
    return value


def command_provider_environment_policy() -> dict[str, Any]:
    return {
        "schemaVersion": 1,
        "inheritedEnvironmentCleared": True,
        "fixedVariables": list(SOLVER_FIXED_ENVIRONMENT_VARIABLES),
        "hostEnvironmentAllowlist": [
            "PATH",
            "CODEX_HOME",
            "LOGOS_SOLVER_CODEX_HOME",
            "LOGOS_SOLVER_CODEX_CONFIG",
        ],
        "explicitContractVariables": ["LOGOS_PROPOSAL_JSON"],
        "unlistedEnvironmentPolicy": "excluded_by_env_clear_before_process_start",
        "explicitlyExcludedVariables": list(SOLVER_LAUNCH_EXCLUDED_VARIABLES),
        "explicitlyExcludedPrefixes": ["BASH_FUNC_"],
    }


def validate_codex_solver_path(
    value: Any,
    lexical_codex: dict[str, Any],
    lexical_node: dict[str, Any],
) -> dict[str, Any]:
    location = "Codex solver PATH"
    value = require_exact_keys(
        value, {"algorithm", "value", "directoryCount", "directories"}, location
    )
    directories = value.get("directories")
    if (
        value.get("algorithm") != "logos-codex-solver-path-v1"
        or not isinstance(directories, list)
        or value.get("directoryCount") != len(directories)
        or len(directories) != 4
    ):
        raise PublishError(f"{location} is malformed")
    expected = (
        (
            "codexLexicalWrapper",
            str(Path(lexical_codex["path"]).parent),
            lexical_codex["sha256"],
        ),
        (
            "nodeLexicalExecutable",
            str(Path(lexical_node["path"]).parent),
            lexical_node["sha256"],
        ),
        ("systemTools", "/usr/bin", None),
        ("systemTools", "/bin", None),
    )
    for index, (row, (role, path, executable_sha256)) in enumerate(
        zip(directories, expected, strict=True), start=1
    ):
        row = require_exact_keys(
            row,
            {"ordinal", "role", "path", "boundExecutableSha256"},
            f"{location}.directories[{index - 1}]",
        )
        if row != {
            "ordinal": index,
            "role": role,
            "path": path,
            "boundExecutableSha256": executable_sha256,
        }:
            raise PublishError(f"{location} directory closure drifted")
    expected_value = os.pathsep.join(path for _role, path, _sha256 in expected)
    if value.get("value") != expected_value:
        raise PublishError(f"{location} value does not reconcile")
    return value


def validate_codex_provider(record: Any, run_root: Path) -> dict[str, Any]:
    record = require_exact_keys(
        record,
        {
            "manifestPath",
            "manifestSha256",
            "algorithm",
            "configPath",
            "configSha256",
            "configBytes",
            "model",
            "reasoningEffort",
            "endpoint",
            "endpointSha256",
            "hostCodexVersion",
            "hostCodexInvocationPath",
            "hostCodexLexicalWrapper",
            "hostCodexNodeInvocationPath",
            "solverPath",
            "commandShell",
            "commandEnvironmentPolicy",
            "commands",
        },
        "configuration.codexProvider",
    )
    path, digest = validate_file_binding(
        record,
        path_key="manifestPath",
        digest_key="manifestSha256",
        location="configuration.codexProvider",
        run_root=run_root,
    )
    config_path, config_digest = validate_file_binding(
        record,
        path_key="configPath",
        digest_key="configSha256",
        location="configuration.codexProvider config",
        run_root=run_root,
        expected_path=run_root / "codex-provider-config.toml",
    )
    document = load_json(path)
    require_exact_keys(
        document,
        {
            "schemaVersion",
            "algorithm",
            "config",
            "model",
            "reasoningEffort",
            "endpoint",
            "hostCodexCli",
            "commandShell",
            "commandEnvironmentPolicy",
            "commands",
        },
        "Codex provider manifest",
    )
    endpoint = document.get("endpoint")
    commands = document.get("commands")
    host_cli = document.get("hostCodexCli")
    config_record = document.get("config")
    command_shell = document.get("commandShell")
    command_environment = document.get("commandEnvironmentPolicy")
    if (
        record.get("algorithm") != CODEX_PROVIDER_MANIFEST_ALGORITHM
        or document.get("schemaVersion") != 1
        or document.get("algorithm") != CODEX_PROVIDER_MANIFEST_ALGORITHM
        or document.get("model") != MODEL
        or document.get("reasoningEffort") != REASONING_EFFORT
        or record.get("model") != MODEL
        or record.get("reasoningEffort") != REASONING_EFFORT
        or not isinstance(config_record, dict)
        or set(config_record) != {"path", "sha256", "bytes", "kind"}
        or config_record.get("path") != "codex-provider-config.toml"
        or config_record.get("sha256") != config_digest
        or config_record.get("bytes") != config_path.stat().st_size
        or config_record.get("kind") != "sanitized-minimal-nonsecret-codex-config"
        or not isinstance(endpoint, dict)
        or set(endpoint)
        != {
            "providerId",
            "name",
            "baseUrl",
            "baseUrlSha256",
            "scheme",
            "host",
            "port",
            "path",
            "wireApi",
            "supportsWebsockets",
            "requiresOpenaiAuth",
        }
        or not isinstance(endpoint.get("baseUrl"), str)
        or endpoint.get("baseUrlSha256") != sha256_text(endpoint["baseUrl"])
        or record.get("endpoint") != endpoint
        or record.get("endpointSha256")
        != sha256_text(json.dumps(endpoint, sort_keys=True, separators=(",", ":")))
        or not isinstance(host_cli, dict)
        or set(host_cli)
        != {
            "invocationPath",
            "lexicalWrapper",
            "executable",
            "node",
            "interpreterChain",
            "packageRoot",
            "packageFiles",
            "solverPath",
            "version",
        }
        or record.get("hostCodexVersion") != host_cli.get("version")
        or not isinstance(host_cli.get("version"), str)
        or not host_cli["version"]
        or not valid_executable_evidence(host_cli.get("executable"))
        or set(host_cli["executable"]) != {"path", "sha256", "bytes"}
        or commands
        != {
            "counterexample": DEFAULT_COUNTEREXAMPLE_COMMAND,
            "proofAgent": DEFAULT_PROOF_AGENT_COMMAND,
            "proofAgentResume": DEFAULT_PROOF_AGENT_RESUME_COMMAND,
        }
        or record.get("commands") != commands
        or command_shell
        != {
            "shellExecutable": "/usr/bin/bash",
            "shellArguments": ["--noprofile", "--norc", "-c"],
        }
        or record.get("commandShell") != command_shell
        or command_environment != command_provider_environment_policy()
        or record.get("commandEnvironmentPolicy") != command_environment
    ):
        raise PublishError("Codex provider manifest is malformed or unbound")

    lexical_codex = validate_lexical_executable(
        host_cli.get("lexicalWrapper"), "Codex lexical wrapper"
    )
    if (
        host_cli.get("invocationPath") != lexical_codex["path"]
        or host_cli["executable"]["path"] != lexical_codex["resolvedPath"]
        or host_cli["executable"]["sha256"] != lexical_codex["sha256"]
        or record.get("hostCodexInvocationPath") != host_cli["invocationPath"]
        or record.get("hostCodexLexicalWrapper") != lexical_codex
    ):
        raise PublishError("Codex lexical wrapper is not cross-bound")

    node = require_exact_keys(
        host_cli.get("node"),
        {"invocationPath", "lexicalExecutable", "executable", "version"},
        "Codex Node runtime",
    )
    lexical_node = validate_lexical_executable(
        node.get("lexicalExecutable"), "Codex Node lexical executable"
    )
    if (
        node.get("invocationPath") != lexical_node["path"]
        or not valid_executable_evidence(node.get("executable"))
        or set(node["executable"]) != {"path", "sha256", "bytes"}
        or node["executable"]["path"] != lexical_node["resolvedPath"]
        or node["executable"]["sha256"] != lexical_node["sha256"]
        or not isinstance(node.get("version"), str)
        or not node["version"]
        or record.get("hostCodexNodeInvocationPath") != node["invocationPath"]
    ):
        raise PublishError("Codex Node runtime closure is malformed")

    interpreter = require_exact_keys(
        host_cli.get("interpreterChain"),
        {"shebang", "envExecutable", "nodeExecutable", "dynamicLinking"},
        "Codex interpreter chain",
    )
    env_tool = validate_fixed_tool_evidence(
        interpreter.get("envExecutable"),
        name="env",
        selected_path="/usr/bin/env",
        location="Codex /usr/bin/env interpreter",
    )
    node_tool = validate_fixed_tool_evidence(
        interpreter.get("nodeExecutable"),
        name="node",
        selected_path=node["executable"]["path"],
        location="Codex Node interpreter",
    )
    if (
        interpreter.get("shebang") != "#!/usr/bin/env node"
        or env_tool["selectedPathIsSymlink"] is not False
        or env_tool["resolvedPath"] != "/usr/bin/env"
        or node_tool["resolvedPath"] != node["executable"]["path"]
        or node_tool["sha256"] != node["executable"]["sha256"]
    ):
        raise PublishError("Codex interpreter chain is not fixed and cross-bound")
    validate_dynamic_linking(
        interpreter.get("dynamicLinking"),
        {"env": env_tool["sha256"], "node": node_tool["sha256"]},
        ("env", "node"),
        "Codex interpreter dynamic linking",
    )

    package_root = host_cli.get("packageRoot")
    if not isinstance(package_root, str) or not package_root:
        raise PublishError("Codex provider host CLI runtime closure is malformed")
    package_files = validate_tree_manifest_entries(
        host_cli.get("packageFiles"), "Codex host package files"
    )
    if not any(entry.get("kind") == "file" for entry in package_files):
        raise PublishError("Codex host package closure contains no regular files")

    solver_path = validate_codex_solver_path(
        host_cli.get("solverPath"), lexical_codex, lexical_node
    )
    if record.get("solverPath") != solver_path:
        raise PublishError("Codex solver PATH is not cross-bound")

    config_text = config_path.read_text(encoding="utf-8")
    if re.search(
        r"(?i)(api[_-]?key|access[_-]?token|secret|password|credential)\s*=",
        config_text,
    ):
        raise PublishError("sanitized Codex config contains credential material")
    try:
        config = tomllib.loads(config_text)
    except ValueError as error:
        raise PublishError("sanitized Codex config is invalid TOML") from error
    provider_id = config.get("model_provider")
    providers = config.get("model_providers")
    provider = providers.get(provider_id) if isinstance(providers, dict) else None
    if (
        set(config)
        != {
            "model",
            "model_reasoning_effort",
            "model_provider",
            "preferred_auth_method",
            "model_providers",
        }
        or config.get("model") != MODEL
        or config.get("model_reasoning_effort") != REASONING_EFFORT
        or not isinstance(provider, dict)
        or set(provider)
        != {
            "name",
            "base_url",
            "wire_api",
            "supports_websockets",
            "requires_openai_auth",
        }
        or provider.get("base_url") != endpoint.get("baseUrl")
        or provider.get("wire_api") != endpoint.get("wireApi")
    ):
        raise PublishError("sanitized Codex config is not the minimal frozen treatment")
    canonical = (
        json.dumps(document, sort_keys=True, separators=(",", ":")) + "\n"
    ).encode("utf-8")
    if path.read_bytes() != canonical:
        raise PublishError("Codex provider manifest is not canonical JSON")
    return {
        "path": path,
        "sha256": digest,
        "configPath": config_path,
        "configSha256": config_digest,
        "endpointSha256": record["endpointSha256"],
        "solverPath": solver_path,
        "commandEnvironmentPolicy": command_environment,
        "hostCodexInvocationPath": host_cli["invocationPath"],
        "hostCodexNodeInvocationPath": node["invocationPath"],
    }


def validate_runner_launch_environments(
    configuration: dict[str, Any],
    codex_provider: dict[str, Any],
    frontend_stack: dict[str, Any],
) -> dict[str, Any]:
    solver_path = codex_provider["solverPath"]
    expected_solver_policy = {
        "schemaVersion": 1,
        "inheritedEnvironmentCleared": True,
        "fixedVariables": [
            f"PATH={solver_path['value']}",
            *SOLVER_FIXED_ENVIRONMENT_VARIABLES,
        ],
        "hostEnvironmentAllowlist": [],
        "explicitContractVariables": list(SOLVER_EXPLICIT_ENVIRONMENT_NAMES),
        "unlistedEnvironmentPolicy": "excluded_by_env_clear_before_process_start",
        "explicitlyExcludedVariables": list(SOLVER_LAUNCH_EXCLUDED_VARIABLES),
        "explicitlyExcludedPrefixes": ["BASH_FUNC_"],
        "codexInvocationPath": codex_provider["hostCodexInvocationPath"],
        "nodeInvocationPath": codex_provider["hostCodexNodeInvocationPath"],
        "codexSolverPathAlgorithm": solver_path["algorithm"],
    }
    if configuration.get("solverLaunchEnvironmentPolicy") != expected_solver_policy:
        raise PublishError("solver launch environment policy is malformed or unbound")
    if (
        configuration.get("frontendLaunchEnvironmentPolicy")
        != frontend_stack["launchEnvironment"]
        or configuration.get("commandProviderEnvironmentPolicy")
        != codex_provider["commandEnvironmentPolicy"]
    ):
        raise PublishError("frontend/provider launch policies are not cross-bound")

    solver_environment = require_exact_keys(
        configuration.get("solverEnvironment"),
        {
            "algorithm",
            "variableCount",
            "variableNames",
            "normalization",
            "sha256",
        },
        "configuration.solverEnvironment",
    )
    expected_names = sorted(
        {
            "PATH",
            *(value.split("=", 1)[0] for value in SOLVER_FIXED_ENVIRONMENT_VARIABLES),
            *SOLVER_EXPLICIT_ENVIRONMENT_NAMES,
        }
    )
    symbolic_home = "<isolated-codex-runtime-home>"
    normalized_environment = {
        "PATH": solver_path["value"],
        "HOME": "/nonexistent",
        "TMPDIR": "/tmp",
        "LC_ALL": "C",
        "LANG": "C",
        "TZ": "UTC",
        "CODEX_HOME": symbolic_home,
        "LOGOS_SOLVER_CODEX_HOME": symbolic_home,
        "LOGOS_SOLVER_CODEX_CONFIG": f"{symbolic_home}/config.toml",
        "JAVA_HOME": str((WORKFLOW_ROOT / "PaperTools/envs/sqlsolver-jdk17").resolve()),
        "MAVEN_VERSION": "3.9.11",
        "LOGOS_CALCITE_RUNTIME_CLASSPATH_FILE": str(
            (
                LOGOS_ROOT
                / "frontend/calcite-wrapper/target/logos-runtime-classpath.txt"
            ).resolve()
        ),
    }
    expected_environment_sha256 = hashlib.sha256(
        (
            json.dumps(normalized_environment, sort_keys=True, separators=(",", ":"))
            + "\n"
        ).encode("utf-8")
    ).hexdigest()
    if (
        solver_environment.get("algorithm") != SOLVER_ENVIRONMENT_POLICY_ALGORITHM
        or solver_environment.get("variableCount") != len(expected_names)
        or solver_environment.get("variableNames") != expected_names
        or solver_environment.get("normalization")
        != "isolated-codex-runtime-home-symbolic-v1"
        or solver_environment.get("sha256") != expected_environment_sha256
    ):
        raise PublishError("solver launch environment record is malformed")
    return {
        "solverLaunchEnvironmentPolicy": expected_solver_policy,
        "solverEnvironment": solver_environment,
        "frontendLaunchEnvironmentPolicy": frontend_stack["launchEnvironment"],
        "commandProviderEnvironmentPolicy": codex_provider["commandEnvironmentPolicy"],
    }


def validate_postgres_profile(record: Any, run_root: Path) -> dict[str, Any]:
    path, digest = validate_file_binding(
        record,
        path_key="manifestPath",
        digest_key="manifestSha256",
        location="configuration.postgresServerProfile",
        run_root=run_root,
    )
    assert isinstance(record, dict)
    document = load_json(path)
    expected_profile = {
        "serverVersion": "17.4",
        "serverVersionNum": "170004",
        "databaseCollation": "C",
        "databaseCharacterClassification": "C",
        "localeProvider": "libc",
        "serverEncoding": "UTF8",
        "timeZone": "UTC",
        "maxConnections": "96",
    }
    if (
        record.get("algorithm") != POSTGRES_PROFILE_MANIFEST_ALGORITHM
        or document.get("schemaVersion") != 1
        or document.get("algorithm") != POSTGRES_PROFILE_MANIFEST_ALGORITHM
        or document.get("configured") is not True
        or not valid_sha256(document.get("urlSha256"))
        or document.get("profile") != expected_profile
        or record.get("configured") is not True
        or record.get("urlSha256") != document.get("urlSha256")
        or record.get("profile") != expected_profile
        or record.get("psql") != document.get("psql")
        or not isinstance(document.get("psql"), dict)
        or not valid_sha256(nested(document, "psql", "executable", "sha256"))
    ):
        raise PublishError("PostgreSQL server profile is not frozen PG17.4 UTC/C")
    canonical = (
        json.dumps(document, sort_keys=True, separators=(",", ":")) + "\n"
    ).encode("utf-8")
    if path.read_bytes() != canonical:
        raise PublishError("PostgreSQL server-profile manifest is not canonical JSON")
    return {"path": path, "sha256": digest, "urlSha256": document["urlSha256"]}


def cohort16_selected_authority_digests(
    expected: list[str],
    input_rows: dict[str, dict[str, str]],
    semantic_rows: dict[str, dict[str, Any]],
) -> tuple[str, str]:
    """Derive both selected-cohort authorities from their canonical rows."""

    if not set(expected) <= set(input_rows) or not set(expected) <= set(semantic_rows):
        raise PublishError("cohort16 gate inputs are missing frozen authority rows")
    selected_document = {
        "schemaVersion": 1,
        "algorithm": INPUT_MANIFEST_ALGORITHM,
        "caseCount": len(expected),
        "cases": [input_rows[case] for case in sorted(expected)],
    }
    selected_semantic_document = {
        "schemaVersion": 1,
        "algorithm": SEMANTIC_INPUT_AUTHORITY_ALGORITHM,
        "caseCount": len(expected),
        "cases": [semantic_rows[case] for case in sorted(expected)],
    }
    return (
        sha256_text(
            json.dumps(selected_document, sort_keys=True, separators=(",", ":"))
            + "\n"
        ),
        sha256_text(
            json.dumps(
                selected_semantic_document,
                sort_keys=True,
                separators=(",", ":"),
            )
            + "\n"
        ),
    )


def validate_cohort16_gate_case_input_authority(
    case: str,
    input_files: Any,
    input_row: dict[str, str],
    semantic_row: dict[str, Any],
    run_root: Path,
) -> tuple[dict[str, str], dict[str, Path], Path]:
    """Validate one gate row against SQL, metadata, and sidecar authority."""

    expected_input_names = {"schema", "source", "target", "metadata"}
    if semantic_row.get("semanticSidecarPath") is not None:
        expected_input_names.add("semanticSidecar")
    if not isinstance(input_files, dict) or set(input_files) != expected_input_names:
        raise PublishError(f"cohort16 gate case {case} input binding is malformed")
    input_digests: dict[str, str] = {}
    input_paths: dict[str, Path] = {}
    for name, manifest_key in (
        ("schema", "schemaSha256"),
        ("source", "sql1Sha256"),
        ("target", "sql2Sha256"),
    ):
        input_path, digest = validate_file_binding(
            input_files[name],
            path_key="path",
            digest_key="sha256",
            location=f"cohort16 gate {case}.inputFiles.{name}",
            run_root=run_root,
        )
        if digest != input_row[manifest_key]:
            raise PublishError(f"cohort16 gate case {case} exact input drifted")
        input_digests[name] = digest
        input_paths[name] = input_path
    metadata_path, metadata_digest = validate_file_binding(
        input_files["metadata"],
        path_key="path",
        digest_key="sha256",
        location=f"cohort16 gate {case}.inputFiles.metadata",
        run_root=run_root,
    )
    metadata = load_json(metadata_path)
    if (
        metadata_digest != semantic_row.get("metadataSha256")
        or not isinstance(metadata, dict)
        or metadata.get("flatCaseId") != semantic_row.get("flatCaseId")
    ):
        raise PublishError(
            f"cohort16 gate case {case} metadata semantic authority drifted"
        )
    input_digests["metadata"] = metadata_digest
    sidecar_declared = semantic_row.get("semanticSidecarPath")
    if sidecar_declared is not None:
        expected_sidecar = resolve_recorded_file(
            sidecar_declared,
            f"cohort16 gate {case}.semanticAuthority.semanticSidecarPath",
            run_root,
        )
        sidecar_path, sidecar_digest = validate_file_binding(
            input_files["semanticSidecar"],
            path_key="path",
            digest_key="sha256",
            location=f"cohort16 gate {case}.inputFiles.semanticSidecar",
            run_root=run_root,
            expected_path=expected_sidecar,
        )
        if sidecar_digest != semantic_row.get("semanticSidecarSha256"):
            raise PublishError(
                f"cohort16 gate case {case} semantic sidecar authority drifted"
            )
        input_digests["semanticSidecar"] = sidecar_digest
        input_paths["semanticSidecar"] = sidecar_path
    return input_digests, input_paths, metadata_path


def validate_cohort16_gate_report_with_runner(
    case: str,
    report_path: Path,
    row: dict[str, Any],
    metadata_path: Path,
    semantic_row: dict[str, Any],
    input_paths: dict[str, Path],
    input_files: dict[str, Any],
    full_configuration: dict[str, Any],
) -> None:
    """Delegate gate proof/lowering/recovery authority to the runner policy."""

    gate_case_authority = types.SimpleNamespace(
        case_id=case,
        cohort=case.split("__", 1)[0],
        input_dir=metadata_path.parent,
        relative_dir=metadata_path.parent.name,
        flat_case_id=semantic_row["flatCaseId"],
        schema=input_paths["schema"],
        source=input_paths["source"],
        target=input_paths["target"],
    )
    gate_config_authority = types.SimpleNamespace(
        verification_mode=VERIFICATION_MODE,
        case_timeout_seconds=CASE_TIMEOUT_SECONDS,
        proof_check_timeout_seconds=TRUSTED_CHECK_TIMEOUT_SECONDS,
        proof_agent_memory_limit_mib=PROOF_AGENT_MEMORY_LIMIT_MIB,
        proof_agent_storage_limit_mib=PROOF_AGENT_STORAGE_LIMIT_MIB,
        proof_docker_image_effective=nested(
            full_configuration, "proofAgent", "dockerImage", "imageId"
        ),
        input_files={case: input_files},
        trusted_stack=full_configuration.get("trustedStack"),
        sql_default_collation=nested(
            full_configuration, "sqlEnvironment", "defaultCollation"
        ),
        sql_character_classification=nested(
            full_configuration,
            "sqlEnvironment",
            "characterClassification",
        ),
        sql_locale_provider=nested(
            full_configuration, "sqlEnvironment", "localeProvider"
        ),
        sql_server_encoding=nested(
            full_configuration, "sqlEnvironment", "serverEncoding"
        ),
    )
    try:
        runner_validators()["validate_gate_report"](
            report_path,
            gate_case_authority,
            gate_config_authority,
            row.get("proofMetrics"),
        )
    except Exception as error:
        raise PublishError(
            f"cohort16 gate case {case} failed shared runner proof validation: "
            f"{error}"
        ) from error


def validate_cohort16_rocq_snapshot_bindings(
    record: Any,
    gate_configuration: Any,
    gate_integrity: Any,
    rows: Any,
    expected_authority_digest: str,
    expected_runtime: dict[str, Any],
) -> None:
    """Bind every gate summary surface to one immutable Rocq snapshot."""

    if (
        not isinstance(record, dict)
        or record.get("rocqAuthoritySnapshotManifestSha256")
        != expected_authority_digest
        or record.get("rocqRuntimeSnapshotManifestSha256")
        != expected_runtime.get("manifestSha256")
        or not isinstance(gate_configuration, dict)
        or gate_configuration.get("rocqRuntimeSnapshot") != expected_runtime
        or nested(gate_configuration, "trustedStack", "rocqRuntimeSnapshot")
        != expected_runtime
        or nested(gate_configuration, "proofAgent", "rocqOpamSwitch")
        != expected_runtime.get("root")
        or gate_configuration.get("rocqAuthoritySnapshotPolicy")
        != TRUSTED_ROCQ_AUTHORITY_SNAPSHOT_POLICY
        or nested(gate_configuration, "rocqAuthoritySnapshot", "policy")
        != TRUSTED_ROCQ_AUTHORITY_SNAPSHOT_POLICY
        or nested(gate_configuration, "rocqAuthoritySnapshot", "manifestSha256")
        != expected_authority_digest
        or not isinstance(gate_integrity, dict)
        or gate_integrity.get("rocqAuthoritySnapshotManifestSha256")
        != expected_authority_digest
        or gate_integrity.get("rocqRuntimeSnapshotManifestSha256")
        != expected_runtime.get("manifestSha256")
        or not isinstance(rows, list)
    ):
        raise PublishError("cohort16 gate Rocq authority snapshot drifted")
    for row in rows:
        effective = row.get("effectiveConfiguration") if isinstance(row, dict) else None
        if (
            not isinstance(effective, dict)
            or effective.get("rocqRuntimeSnapshotPolicy")
            != TRUSTED_ROCQ_RUNTIME_SNAPSHOT_POLICY
            or effective.get("rocqRuntimeSnapshotManifestSha256")
            != expected_runtime.get("manifestSha256")
            or effective.get("rocqAuthoritySnapshotPolicy")
            != TRUSTED_ROCQ_AUTHORITY_SNAPSHOT_POLICY
            or effective.get("rocqAuthoritySnapshotManifestSha256")
            != expected_authority_digest
        ):
            raise PublishError("cohort16 gate case Rocq authority snapshot drifted")


def validate_cohort16_gate(
    record: Any,
    run_root: Path,
    source_digest: str,
    full_started_at: Any,
    input_rows: dict[str, dict[str, str]],
    semantic_rows: dict[str, dict[str, Any]],
    solver_digest: str,
    rocq_snapshot_digest: str,
    trusted_stack_digest: str,
    frontend_stack_digest: str,
    codex_provider: dict[str, Any],
    postgres_profile_digest: str,
    full_configuration: dict[str, Any],
    *,
    legacy_catalog: bool,
) -> dict[str, Any]:
    gate_path, gate_digest = validate_file_binding(
        record,
        path_key="path",
        digest_key="sha256",
        location="configuration.cohort16Gate",
        run_root=run_root,
    )
    scope_path, scope_digest = validate_file_binding(
        record,
        path_key="scopePath",
        digest_key="scopeSha256",
        location="configuration.cohort16Gate scope",
        run_root=run_root,
    )
    assert isinstance(record, dict)
    validate_legacy_catalog_marker(
        record,
        "catalogGuidanceEnabled",
        legacy_catalog=legacy_catalog,
        location="configuration.cohort16Gate",
    )
    if record.get("frameworkSourceTreeManifestSha256") != source_digest:
        raise PublishError(
            "cohort16 gate and full run use different framework source trees"
        )
    scope = load_json(scope_path)
    cases = scope.get("ablationCases")
    extension = scope.get("extensionCases")
    if not isinstance(cases, list) or not isinstance(extension, list):
        raise PublishError("cohort16 gate scope has no frozen 8+8 cohort")
    expected = string_array(cases + extension, "cohort16 gate scope cases")
    if len(expected) != 16 or len(set(expected)) != 16:
        raise PublishError("cohort16 gate scope is not 16 unique cases")
    expected_digest = sha256_text("\n".join(sorted(expected)) + "\n")
    selected_input_digest, selected_semantic_digest = (
        cohort16_selected_authority_digests(expected, input_rows, semantic_rows)
    )
    if (
        record.get("caseSetSha256") != expected_digest
        or record.get("selectedInputManifestSha256") != selected_input_digest
        or record.get("semanticAuthoritySha256")
        != FROZEN_SEMANTIC_INPUT_AUTHORITY_SHA256
        or record.get("selectedSemanticAuthoritySha256")
        != selected_semantic_digest
        or record.get("solverBinarySha256") != solver_digest
        or record.get("rocqAuthoritySnapshotManifestSha256")
        != rocq_snapshot_digest
        or record.get("trustedStackManifestSha256") != trusted_stack_digest
        or record.get("frontendStackManifestSha256") != frontend_stack_digest
        or record.get("codexProviderManifestSha256") != codex_provider["sha256"]
        or record.get("codexConfigSha256") != codex_provider["configSha256"]
        or record.get("providerEndpointSha256") != codex_provider["endpointSha256"]
        or record.get("postgresServerProfileSha256") != postgres_profile_digest
        or record.get("verificationMode") != VERIFICATION_MODE
    ):
        raise PublishError("cohort16 gate records the wrong frozen treatment/bindings")
    gate = load_json(gate_path)
    gate_cases = string_array(gate.get("cases"), "cohort16 gate cases")
    rows = gate.get("results")
    gate_configuration = gate.get("configuration")
    gate_integrity = gate.get("integrityVerification")
    full_proof_agent = full_configuration.get("proofAgent")
    gate_proof_agent = (
        gate_configuration.get("proofAgent")
        if isinstance(gate_configuration, dict)
        else None
    )
    validate_cohort16_rocq_snapshot_bindings(
        record,
        gate_configuration,
        gate_integrity,
        rows,
        rocq_snapshot_digest,
        full_configuration["rocqRuntimeSnapshot"],
    )
    validate_legacy_catalog_marker(
        gate,
        "proofAgentCatalogGuidanceEnabled",
        legacy_catalog=legacy_catalog,
        location="cohort16 gate",
    )
    validate_legacy_catalog_marker(
        gate_proof_agent,
        "catalogGuidanceEnabled",
        legacy_catalog=legacy_catalog,
        location="cohort16 configuration.proofAgent",
    )
    validate_fixed_fields(
        full_proof_agent,
        proof_agent_diagnostic_configuration(legacy_catalog=legacy_catalog),
        "full configuration.proofAgent",
    )
    validate_fixed_fields(
        gate_proof_agent,
        proof_agent_diagnostic_configuration(legacy_catalog=legacy_catalog),
        "cohort16 configuration.proofAgent",
    )
    if (
        gate.get("status") != "complete"
        or len(gate_cases) != 16
        or set(gate_cases) != set(expected)
        or not isinstance(rows, list)
        or len(rows) != 16
        or gate.get("verificationMode") != VERIFICATION_MODE
        or gate.get("model") != MODEL
        or gate.get("reasoningEffort") != REASONING_EFFORT
        or gate.get("usageComplete") is not True
        or gate.get("caseTimeoutSeconds") != CASE_TIMEOUT_SECONDS
        or gate.get("counts")
        != {
            "selected": 16,
            "pending": 0,
            "completed": 16,
            "timedOut": 0,
            "failed": 0,
            "cancelled": 0,
        }
        or nested(gate, "configuration", "frameworkSourceTree", "manifestSha256")
        != source_digest
        or nested(gate, "configuration", "solverBinary", "sha256") != solver_digest
        or nested(
            gate,
            "configuration",
            "rocqAuthoritySnapshot",
            "manifestSha256",
        )
        != rocq_snapshot_digest
        or nested(gate, "configuration", "rocqAuthoritySnapshot", "policy")
        != TRUSTED_ROCQ_AUTHORITY_SNAPSHOT_POLICY
        or nested(gate, "configuration", "rocqAuthoritySnapshotPolicy")
        != TRUSTED_ROCQ_AUTHORITY_SNAPSHOT_POLICY
        or nested(gate, "configuration", "trustedStack", "manifestSha256")
        != trusted_stack_digest
        or nested(gate, "configuration", "frontendStack", "manifestSha256")
        != frontend_stack_digest
        or nested(gate, "configuration", "codexProvider", "manifestSha256")
        != codex_provider["sha256"]
        or nested(gate, "configuration", "codexProvider", "configSha256")
        != codex_provider["configSha256"]
        or nested(gate, "configuration", "postgresServerProfile", "manifestSha256")
        != postgres_profile_digest
        or nested(gate, "configuration", "inputManifest", "selectedSha256")
        != selected_input_digest
        or nested(
            gate,
            "configuration",
            "inputManifest",
            "semanticAuthoritySha256",
        )
        != FROZEN_SEMANTIC_INPUT_AUTHORITY_SHA256
        or nested(
            gate,
            "configuration",
            "inputManifest",
            "selectedSemanticAuthoritySha256",
        )
        != selected_semantic_digest
        or not isinstance(gate_configuration, dict)
        or gate_configuration.get("verificationMode")
        != full_configuration.get("verificationMode")
        or gate_configuration.get("model") != full_configuration.get("model")
        or gate_configuration.get("reasoningEffort")
        != full_configuration.get("reasoningEffort")
        or gate_configuration.get("caseTimeoutSeconds")
        != full_configuration.get("caseTimeoutSeconds")
        or gate_configuration.get("terminationGraceSeconds")
        != full_configuration.get("terminationGraceSeconds")
        or gate_configuration.get("solverArgs") != full_configuration.get("solverArgs")
        or gate_configuration.get("effectiveSolverArgs")
        != full_configuration.get("effectiveSolverArgs")
        or gate_configuration.get("postgresUrl")
        != full_configuration.get("postgresUrl")
        or gate_configuration.get("sqlEnvironment")
        != full_configuration.get("sqlEnvironment")
        or gate_configuration.get("solverLaunchEnvironmentPolicy")
        != full_configuration.get("solverLaunchEnvironmentPolicy")
        or gate_configuration.get("solverEnvironment")
        != full_configuration.get("solverEnvironment")
        or gate_configuration.get("frontendLaunchEnvironmentPolicy")
        != full_configuration.get("frontendLaunchEnvironmentPolicy")
        or gate_configuration.get("commandProviderEnvironmentPolicy")
        != full_configuration.get("commandProviderEnvironmentPolicy")
        or not isinstance(gate_proof_agent, dict)
        or not isinstance(full_proof_agent, dict)
        or gate_proof_agent.get("model") != full_proof_agent.get("model")
        or gate_proof_agent.get("reasoningEffort")
        != full_proof_agent.get("reasoningEffort")
        or gate_proof_agent.get("sessionRestartAfterFailedRounds")
        != full_proof_agent.get("sessionRestartAfterFailedRounds")
        or gate_proof_agent.get("sessionHomePolicy")
        != full_proof_agent.get("sessionHomePolicy")
        or gate_proof_agent.get("totalTimeoutSeconds")
        != full_proof_agent.get("totalTimeoutSeconds")
        or gate_proof_agent.get("trustedCheckTimeoutSeconds")
        != full_proof_agent.get("trustedCheckTimeoutSeconds")
        or gate_proof_agent.get("resourcePolicy")
        != full_proof_agent.get("resourcePolicy")
        or nested(gate_proof_agent, "dockerImage", "imageId")
        != nested(full_proof_agent, "dockerImage", "imageId")
        or not isinstance(gate_integrity, dict)
        or gate_integrity.get("verified") is not True
        or gate.get("integrityError") is not None
        or gate_integrity.get("frontendStackManifestSha256") != frontend_stack_digest
        or gate_integrity.get("codexProviderManifestSha256") != codex_provider["sha256"]
        or gate_integrity.get("codexConfigSha256") != codex_provider["configSha256"]
        or gate_integrity.get("providerEndpointSha256")
        != codex_provider["endpointSha256"]
        or gate_integrity.get("solverEnvironmentSha256")
        != nested(full_configuration, "solverEnvironment", "sha256")
        or gate_integrity.get("postgresServerProfileSha256") != postgres_profile_digest
        or gate_integrity.get("rocqAuthoritySnapshotManifestSha256")
        != rocq_snapshot_digest
        or gate_integrity.get("semanticAuthoritySha256")
        != FROZEN_SEMANTIC_INPUT_AUTHORITY_SHA256
        or gate_integrity.get("selectedSemanticAuthoritySha256")
        != selected_semantic_digest
    ):
        raise PublishError("cohort16 gate is not a complete compatible 16-case run")
    by_case = {
        row.get("caseId"): row
        for row in rows
        if isinstance(row, dict) and isinstance(row.get("caseId"), str)
    }
    if set(by_case) != set(expected) or len(by_case) != len(rows):
        raise PublishError("cohort16 gate result IDs do not match its frozen cohort")
    for case, row in by_case.items():
        if (
            row.get("status") != "completed"
            or not completed_return_code_is_coherent(row)
            or row.get("outcome") != "outcome_unconditional"
            or row.get("backendStatus") != "proof_complete"
            or row.get("certification") != "OUTCOME-UNCONDITIONAL"
            or row.get("usageComplete") is not True
        ):
            raise PublishError(
                f"cohort16 gate case {case} lacks a trusted EQ certificate"
            )
        effective = row.get("effectiveConfiguration")
        validate_legacy_catalog_marker(
            effective,
            "catalogGuidanceEnabled",
            legacy_catalog=legacy_catalog,
            location=f"cohort16 gate case {case}.effectiveConfiguration",
        )
        validate_fixed_fields(
            effective,
            effective_proof_agent_diagnostic_configuration(
                legacy_catalog=legacy_catalog
            ),
            f"cohort16 gate case {case}.effectiveConfiguration",
        )
        if (
            not isinstance(effective, dict)
            or effective.get("frameworkSourceTreeManifestSha256") != source_digest
            or effective.get("selectedInputManifestSha256") != selected_input_digest
            or effective.get("semanticAuthoritySha256")
            != FROZEN_SEMANTIC_INPUT_AUTHORITY_SHA256
            or effective.get("selectedSemanticAuthoritySha256")
            != selected_semantic_digest
            or effective.get("verificationMode") != VERIFICATION_MODE
            or effective.get("model") != MODEL
            or effective.get("reasoningEffort") != REASONING_EFFORT
            or effective.get("caseTimeoutSeconds") != CASE_TIMEOUT_SECONDS
            or effective.get("terminationGraceSeconds")
            != full_configuration.get("terminationGraceSeconds")
            or effective.get("proofAgentTotalTimeoutSeconds")
            != nested(full_configuration, "proofAgent", "totalTimeoutSeconds")
            or effective.get("proofAgentSessionRestartAfterFailedRounds")
            != nested(
                full_configuration,
                "proofAgent",
                "sessionRestartAfterFailedRounds",
            )
            or effective.get("proofAgentSessionHomePolicy")
            != nested(full_configuration, "proofAgent", "sessionHomePolicy")
            or effective.get("resourcePolicy")
            != nested(full_configuration, "proofAgent", "resourcePolicy")
            or effective.get("trustedCheckTimeoutSeconds")
            != TRUSTED_CHECK_TIMEOUT_SECONDS
            or effective.get("dockerImage")
            != nested(full_configuration, "proofAgent", "dockerImage", "imageId")
            or effective.get("solverArgs") != full_configuration.get("solverArgs")
            or effective.get("effectiveSolverArgs")
            != full_configuration.get("effectiveSolverArgs")
            or effective.get("postgresUrl") != full_configuration.get("postgresUrl")
            or effective.get("sqlEnvironment")
            != full_configuration.get("sqlEnvironment")
            or effective.get("solverLaunchEnvironmentPolicy")
            != full_configuration.get("solverLaunchEnvironmentPolicy")
            or effective.get("solverEnvironment")
            != full_configuration.get("solverEnvironment")
            or effective.get("frontendLaunchEnvironmentPolicy")
            != full_configuration.get("frontendLaunchEnvironmentPolicy")
            or effective.get("commandProviderEnvironmentPolicy")
            != full_configuration.get("commandProviderEnvironmentPolicy")
            or effective.get("solverBinarySha256") != solver_digest
            or effective.get("rocqAuthoritySnapshotPolicy")
            != TRUSTED_ROCQ_AUTHORITY_SNAPSHOT_POLICY
            or effective.get("rocqAuthoritySnapshotManifestSha256")
            != rocq_snapshot_digest
            or effective.get("trustedStackManifestSha256") != trusted_stack_digest
            or effective.get("frontendStackManifestSha256") != frontend_stack_digest
            or effective.get("codexProviderManifestSha256") != codex_provider["sha256"]
            or effective.get("codexConfigSha256") != codex_provider["configSha256"]
            or effective.get("providerEndpointSha256")
            != codex_provider["endpointSha256"]
            or effective.get("postgresServerProfileSha256") != postgres_profile_digest
        ):
            raise PublishError(f"cohort16 gate case {case} treatment binding drifted")
        input_files = row.get("inputFiles")
        semantic_row = semantic_rows.get(case)
        if not isinstance(semantic_row, dict):
            raise PublishError(
                f"cohort16 gate case {case} semantic authority is missing"
            )
        input_digests, input_paths, metadata_path = (
            validate_cohort16_gate_case_input_authority(
                case,
                input_files,
                input_rows[case],
                semantic_row,
                gate_path.parent,
            )
        )
        evidence = row.get("reportEvidence")
        report_path, _ = validate_file_binding(
            evidence,
            path_key="path",
            digest_key="sha256",
            location=f"cohort16 gate {case}.reportEvidence",
            run_root=gate_path.parent,
        )
        if not isinstance(evidence, dict) or evidence.get("present") is not True:
            raise PublishError(f"cohort16 gate case {case} has no report evidence")
        report = load_json(report_path)
        validate_cohort16_gate_report_with_runner(
            case,
            report_path,
            row,
            metadata_path,
            semantic_row,
            input_paths,
            input_files,
            full_configuration,
        )
        validate_counterexample_provider_commands(report, f"cohort16 gate {case}")
        proof = report.get("proof")
        agent = proof.get("proofAgent") if isinstance(proof, dict) else None
        agent_configuration = (
            proof.get("proofAgentConfiguration") if isinstance(proof, dict) else None
        )
        context = (
            agent_configuration.get("context")
            if isinstance(agent_configuration, dict)
            else None
        )
        validate_legacy_catalog_marker(
            agent_configuration,
            "catalogGuidance",
            legacy_catalog=legacy_catalog,
            location=f"cohort16 gate case {case}.proofAgentConfiguration",
        )
        validate_fixed_fields(
            agent_configuration,
            proof_agent_diagnostic_configuration(legacy_catalog=legacy_catalog),
            f"cohort16 gate case {case}.proofAgentConfiguration",
        )
        assert isinstance(agent_configuration, dict)
        validate_trusted_diagnostic_cache(
            f"cohort16 gate case {case}", report_path.parent, agent_configuration
        )
        if (
            report.get("outcome") != "outcome_unconditional"
            or not isinstance(proof, dict)
            or proof.get("verificationMode") != "outcome_unconditional"
            or proof.get("backendStatus") != "proof_complete"
            or proof.get("certification") != "OUTCOME-UNCONDITIONAL"
            or proof.get("sqlEnvironment")
            != {
                key: value
                for key, value in full_configuration.get("sqlEnvironment", {}).items()
                if key != "timeZone"
            }
            or not isinstance(agent_configuration, dict)
            or agent_configuration.get("enabled") is not True
            or agent_configuration.get("command") != DEFAULT_PROOF_AGENT_COMMAND
            or agent_configuration.get("resumeCommand")
            != DEFAULT_PROOF_AGENT_RESUME_COMMAND
            or agent_configuration.get("memoryLimitMib") != PROOF_AGENT_MEMORY_LIMIT_MIB
            or agent_configuration.get("writableStorageLimitBytes")
            != PROOF_AGENT_STORAGE_LIMIT_MIB * 1024 * 1024
            or agent_configuration.get("writableStoragePolicy")
            != PROOF_AGENT_WRITABLE_STORAGE_POLICY
            or agent_configuration.get("sessionRestartAfterFailedRounds")
            != PROOF_AGENT_SESSION_RESTART_AFTER_FAILED_ROUNDS
            or agent_configuration.get("sessionHomePolicy")
            != PROOF_AGENT_SESSION_HOME_POLICY
            or agent_configuration.get("timeoutSeconds") != CASE_TIMEOUT_SECONDS - 300
            or agent_configuration.get("trustedCheckTimeoutSeconds")
            != TRUSTED_CHECK_TIMEOUT_SECONDS
            or agent_configuration.get("dockerImage")
            != nested(full_configuration, "proofAgent", "dockerImage", "imageId")
            or not isinstance(context, dict)
            or context.get("sourceSqlSha256") != input_digests["source"]
            or context.get("targetSqlSha256") != input_digests["target"]
        ):
            raise PublishError(
                f"cohort16 gate case {case} report is not a trusted proof"
            )
    gate_completed_at = parse_timestamp(
        gate.get("updatedAt"), "cohort16 gate updatedAt"
    )
    if gate_completed_at > parse_timestamp(full_started_at, "full run startedAt"):
        raise PublishError("cohort16 gate did not complete before the full run started")
    return {
        "path": gate_path,
        "sha256": gate_digest,
        "scopePath": scope_path,
        "scopeSha256": scope_digest,
        "caseSetSha256": expected_digest,
        "selectedInputManifestSha256": selected_input_digest,
        "semanticAuthoritySha256": FROZEN_SEMANTIC_INPUT_AUTHORITY_SHA256,
        "selectedSemanticAuthoritySha256": selected_semantic_digest,
        "rocqAuthoritySnapshotManifestSha256": rocq_snapshot_digest,
    }


def resolve_case_input_directory(value: Any, case: str, run_root: Path) -> Path:
    if not isinstance(value, str) or not value:
        raise PublishError(f"{case}: inputDir must be a nonempty path")
    recorded = Path(value).expanduser()
    candidates = (
        (recorded,)
        if recorded.is_absolute()
        else (
            WORKFLOW_ROOT / recorded,
            LOGOS_ROOT / recorded,
            run_root / recorded,
        )
    )
    raw_matches = [candidate for candidate in candidates if candidate.is_dir()]
    if any(candidate.is_symlink() for candidate in raw_matches):
        raise PublishError(f"{case}: inputDir must not be a symlink")
    matches = [candidate.resolve() for candidate in raw_matches]
    unique = list(dict.fromkeys(matches))
    if len(unique) != 1:
        raise PublishError(f"{case}: inputDir is missing or ambiguous: {value}")
    return unique[0]


def expected_case_configuration(
    summary: dict[str, Any], bindings: dict[str, Any], *, legacy_catalog: bool
) -> dict[str, Any]:
    configuration = summary["configuration"]
    expected = {
        "verificationMode": VERIFICATION_MODE,
        "model": MODEL,
        "reasoningEffort": REASONING_EFFORT,
        "trustedCheckTimeoutSeconds": TRUSTED_CHECK_TIMEOUT_SECONDS,
        "dockerImage": bindings["dockerImage"],
        "caseTimeoutSeconds": CASE_TIMEOUT_SECONDS,
        "maxCounterexampleRounds": MAX_COUNTEREXAMPLE_ROUNDS,
        "statementTimeoutSeconds": STATEMENT_TIMEOUT_SECONDS,
        "terminationGraceSeconds": configuration.get("terminationGraceSeconds"),
        "proofAgentTotalTimeoutSeconds": nested(
            configuration, "proofAgent", "totalTimeoutSeconds"
        ),
        "proofAgentSessionRestartAfterFailedRounds": nested(
            configuration, "proofAgent", "sessionRestartAfterFailedRounds"
        ),
        "proofAgentSessionHomePolicy": nested(
            configuration, "proofAgent", "sessionHomePolicy"
        ),
        **effective_proof_agent_diagnostic_configuration(legacy_catalog=legacy_catalog),
        "solverLaunchEnvironmentPolicy": configuration.get(
            "solverLaunchEnvironmentPolicy"
        ),
        "solverEnvironment": configuration.get("solverEnvironment"),
        "frontendLaunchEnvironmentPolicy": configuration.get(
            "frontendLaunchEnvironmentPolicy"
        ),
        "commandProviderEnvironmentPolicy": configuration.get(
            "commandProviderEnvironmentPolicy"
        ),
        "resourcePolicy": nested(configuration, "proofAgent", "resourcePolicy"),
        "solverArgs": configuration.get("solverArgs"),
        "effectiveSolverArgs": bindings["effectiveSolverArgs"],
        "postgresUrl": configuration.get("postgresUrl"),
        "sqlEnvironment": configuration.get("sqlEnvironment"),
        "solverBinarySnapshotPolicy": configuration.get(
            "solverBinarySnapshotPolicy"
        ),
        "caseProcessIsolation": configuration.get("caseProcessIsolation"),
        "rocqRuntimeSnapshotPolicy": TRUSTED_ROCQ_RUNTIME_SNAPSHOT_POLICY,
        "rocqRuntimeSnapshotManifestSha256": bindings[
            "rocqRuntimeSnapshot"
        ]["manifestSha256"],
        "frameworkSourceTreeDigestPolicy": configuration.get(
            "frameworkSourceTreeDigestPolicy"
        ),
        "frameworkSourceTreeManifestSha256": bindings["source"]["sha256"],
        "inputManifestSha256": bindings["inputManifest"]["sha256"],
        "selectedInputManifestSha256": bindings["inputManifest"]["selectedSha256"],
        "semanticAuthoritySha256": bindings["inputManifest"]["semanticSha256"],
        "selectedSemanticAuthoritySha256": bindings["inputManifest"][
            "selectedSemanticSha256"
        ],
        "solverBinarySha256": bindings["solver"]["sha256"],
        "rocqAuthoritySnapshotPolicy": TRUSTED_ROCQ_AUTHORITY_SNAPSHOT_POLICY,
        "rocqAuthoritySnapshotManifestSha256": bindings[
            "rocqAuthoritySnapshot"
        ]["manifestSha256"],
        "trustedStackManifestSha256": bindings["trustedStack"]["sha256"],
        "frontendStackManifestSha256": bindings["frontendStack"]["sha256"],
        "codexProviderManifestSha256": bindings["codexProvider"]["sha256"],
        "codexConfigSha256": bindings["codexProvider"]["configSha256"],
        "providerEndpointSha256": bindings["codexProvider"]["endpointSha256"],
        "postgresServerProfileSha256": bindings["postgresServerProfile"]["sha256"],
        "cohort16GateSha256": bindings["cohort16Gate"]["sha256"],
    }
    if legacy_catalog:
        expected["catalogGuidanceEnabled"] = True
    return expected


def runner_validators() -> dict[str, Any]:
    """Load the runner's report validators as the single classification policy."""
    global _RUNNER_VALIDATORS
    if _RUNNER_VALIDATORS is None:
        _RUNNER_VALIDATORS = runpy.run_path(
            str(RUNNER_PATH), run_name="canonical_publisher_runner_validation"
        )
    return _RUNNER_VALIDATORS


def runner_case_authority(
    case: str,
    row: dict[str, Any],
    source_dir: Path,
    input_digests: dict[str, str],
    bindings: dict[str, Any],
) -> tuple[Any, Any]:
    """Project publisher input authority into the runner's pure validators."""
    run_root = source_dir.parent.parent
    input_dir = resolve_case_input_directory(row.get("inputDir"), case, run_root)
    metadata_path = input_dir / "metadata.json"
    if not metadata_path.is_file() or metadata_path.is_symlink():
        raise PublishError(f"{case}: selected case metadata is missing")
    metadata = load_json(metadata_path)
    flat_case_id = metadata.get("flatCaseId") if isinstance(metadata, dict) else None
    if not isinstance(flat_case_id, str) or not flat_case_id:
        raise PublishError(f"{case}: selected case metadata has no flatCaseId")
    case_authority = types.SimpleNamespace(
        case_id=case,
        input_dir=input_dir,
        flat_case_id=flat_case_id,
        schema=input_dir / "schema.sql",
        source=input_dir / "sql1.sql",
        target=input_dir / "sql2.sql",
    )
    sql_environment = bindings.get("sqlEnvironment")
    if not isinstance(sql_environment, dict):
        raise PublishError(f"{case}: SQL environment authority is malformed")
    input_files = {
        name: {
            "path": row["inputFiles"][name]["path"],
            "sha256": input_digests[name],
        }
        for name in ("schema", "source", "target")
    }
    metadata_binding = row["inputFiles"].get("metadata")
    if not isinstance(metadata_binding, dict) or set(metadata_binding) != {
        "path",
        "sha256",
    }:
        raise PublishError(f"{case}: selected metadata binding is malformed")
    metadata_recorded_path = resolve_recorded_file(
        metadata_binding.get("path"), f"{case}.inputFiles.metadata.path", run_root
    )
    if (
        metadata_recorded_path != metadata_path.resolve()
        or metadata_binding.get("sha256") != sha256(metadata_path)
    ):
        raise PublishError(f"{case}: selected metadata binding drifted")
    input_files["metadata"] = dict(metadata_binding)
    declared_contract = metadata.get("integrityContract")
    semantic_sidecar = (
        declared_contract.get("semanticSidecar")
        if isinstance(declared_contract, dict)
        else None
    )
    if semantic_sidecar is not None:
        sidecar_binding = row["inputFiles"].get("semanticSidecar")
        if not isinstance(sidecar_binding, dict) or set(sidecar_binding) != {
            "path",
            "sha256",
        }:
            raise PublishError(f"{case}: semantic sidecar binding is malformed")
        sidecar_path = resolve_recorded_file(
            semantic_sidecar,
            f"{case}.metadata.integrityContract.semanticSidecar",
            run_root,
        )
        bound_sidecar_path = resolve_recorded_file(
            sidecar_binding.get("path"),
            f"{case}.inputFiles.semanticSidecar.path",
            run_root,
        )
        if (
            bound_sidecar_path != sidecar_path
            or sidecar_binding.get("sha256") != sha256(sidecar_path)
        ):
            raise PublishError(f"{case}: semantic sidecar binding drifted")
        input_files["semanticSidecar"] = dict(sidecar_binding)
    elif "semanticSidecar" in row["inputFiles"]:
        raise PublishError(f"{case}: undeclared semantic sidecar binding is present")
    config_authority = types.SimpleNamespace(
        verification_mode=VERIFICATION_MODE,
        proof_check_timeout_seconds=TRUSTED_CHECK_TIMEOUT_SECONDS,
        input_files={case: input_files},
        trusted_stack={
            "manifestPath": str(bindings["trustedStack"]["path"]),
            "manifestSha256": bindings["trustedStack"]["sha256"],
        },
        sql_default_collation=sql_environment.get("defaultCollation"),
        sql_character_classification=sql_environment.get(
            "characterClassification"
        ),
        sql_locale_provider=sql_environment.get("localeProvider"),
        sql_server_encoding=sql_environment.get("serverEncoding"),
    )
    return case_authority, config_authority


def validate_with_runner_report_policy(
    case: str,
    row: dict[str, Any],
    report: dict[str, Any],
    source_dir: Path,
    input_digests: dict[str, str],
    bindings: dict[str, Any],
    *,
    validate_current_context: bool,
) -> None:
    validators = runner_validators()
    case_authority, config_authority = runner_case_authority(
        case, row, source_dir, input_digests, bindings
    )
    try:
        proof = report.get("proof")
        agent_configuration = (
            proof.get("proofAgentConfiguration")
            if isinstance(proof, dict)
            else None
        )
        context = (
            agent_configuration.get("context")
            if isinstance(agent_configuration, dict)
            else None
        )
        if validate_current_context and isinstance(context, dict):
            validators["validate_proof_context_manifest"](
                source_dir,
                case_authority,
                context,
                config_authority,
                agent_configuration.get("staticPromptAndPrimerBytes"),
            )
        if isinstance(proof, dict):
            validators["validate_materialized_trusted_scripts"](
                source_dir,
                proof,
                config_authority,
            )
        validators["validate_completed_report"](
            report,
            row,
            source_dir,
            case_authority,
            config_authority,
        )
    except Exception as error:
        raise PublishError(
            f"{case}: runner report policy rejected canonical evidence: {error}"
        ) from error


def validate_report_semantics(
    case: str,
    row: dict[str, Any],
    report: dict[str, Any],
    source_dir: Path,
    input_digests: dict[str, str],
    bindings: dict[str, Any],
    *,
    legacy_catalog: bool,
) -> None:
    validate_counterexample_provider_commands(report, case)
    if report.get("outcome") != row.get("outcome") or report.get("reason") != row.get(
        "reason"
    ):
        raise PublishError(
            f"{case}: report outcome/reason disagrees with runner result"
        )
    report_usage = canonical_usage(report.get("llmUsage"), f"{case}.report.llmUsage")
    row_usage = canonical_usage(row.get("llmUsage"), f"{case}.llmUsage")
    if report_usage != row_usage:
        raise PublishError(f"{case}: report and runner LLM usage differ")
    proof = report.get("proof")
    backend = proof.get("backendStatus") if isinstance(proof, dict) else None
    certification = proof.get("certification") if isinstance(proof, dict) else None
    if row.get("backendStatus") != backend or row.get("certification") != certification:
        raise PublishError(f"{case}: report proof status disagrees with runner result")
    if (
        isinstance(proof, dict)
        and report.get("outcome")
        in {
            "safe_unconditional",
            "outcome_unconditional",
            "conditional_derived",
            "conditional_external",
        }
        and proof.get("deterministicTailRecovery") is None
    ):
        # Repeat this publication boundary independently of the delegated
        # runner policy: the canonical package must never promote a mutable
        # live Problem.v that differs from the terminal checked candidate.
        validate_ordinary_terminal_problem_binding(
            case, row, proof, source_dir, report["outcome"]
        )
    if isinstance(proof, dict):
        if proof.get("verificationMode") != "outcome_unconditional":
            raise PublishError(f"{case}: report proof uses the wrong verification mode")
        if proof.get("sqlEnvironment") != {
            key: value
            for key, value in bindings["sqlEnvironment"].items()
            if key != "timeZone"
        }:
            raise PublishError(f"{case}: report SQL environment drifted")
        agent_configuration = proof.get("proofAgentConfiguration")
        validate_legacy_catalog_marker(
            agent_configuration,
            "catalogGuidance",
            legacy_catalog=legacy_catalog,
            location=f"{case}.proofAgentConfiguration",
        )
        validate_fixed_fields(
            agent_configuration,
            proof_agent_diagnostic_configuration(legacy_catalog=legacy_catalog),
            f"{case}.proofAgentConfiguration",
        )
        if not isinstance(agent_configuration, dict) or (
            agent_configuration.get("enabled") is not True
            or agent_configuration.get("command") != DEFAULT_PROOF_AGENT_COMMAND
            or agent_configuration.get("resumeCommand")
            != DEFAULT_PROOF_AGENT_RESUME_COMMAND
            or agent_configuration.get("memoryLimitMib") != PROOF_AGENT_MEMORY_LIMIT_MIB
            or agent_configuration.get("writableStorageLimitBytes")
            != PROOF_AGENT_STORAGE_LIMIT_MIB * 1024 * 1024
            or agent_configuration.get("writableStoragePolicy")
            != PROOF_AGENT_WRITABLE_STORAGE_POLICY
            or agent_configuration.get("sessionRestartAfterFailedRounds")
            != PROOF_AGENT_SESSION_RESTART_AFTER_FAILED_ROUNDS
            or agent_configuration.get("sessionHomePolicy")
            != PROOF_AGENT_SESSION_HOME_POLICY
            or agent_configuration.get("timeoutSeconds") != CASE_TIMEOUT_SECONDS - 300
            or agent_configuration.get("trustedCheckTimeoutSeconds")
            != TRUSTED_CHECK_TIMEOUT_SECONDS
            or agent_configuration.get("dockerImage") != bindings["dockerImage"]
        ):
            raise PublishError(f"{case}: proof report treatment/configuration drifted")
        context = agent_configuration.get("context")
        if isinstance(context, dict):
            if (
                context.get("sourceSqlSha256") != input_digests["source"]
                or context.get("targetSqlSha256") != input_digests["target"]
                or not valid_sha256(context.get("manifestSha256"))
            ):
                raise PublishError(
                    f"{case}: proof context is not bound to exact SQL inputs"
                )

    # Classification is intentionally delegated to the same strict policy the
    # benchmark runner used. This keeps direct PostgreSQL evidence, proof-agent
    # terminal handoffs, ordinary Rocq certificates, and deterministic-tail
    # recovery on one fail-closed contract instead of maintaining a weaker
    # publication-only interpretation.
    validate_with_runner_report_policy(
        case,
        row,
        report,
        source_dir,
        input_digests,
        bindings,
        validate_current_context=not legacy_catalog,
    )


def validate_formal_countermodel_certificate(
    case: str,
    row: dict[str, Any],
    report: dict[str, Any],
    source_dir: Path,
    counterexample: dict[str, Any],
) -> None:
    """Require a FORMAL-COUNTERMODEL to be the exact trusted Rocq result."""
    proof = report.get("proof")
    workspace = proof.get("proofWorkspace") if isinstance(proof, dict) else None
    agent = proof.get("proofAgent") if isinstance(proof, dict) else None
    audit = agent.get("audit") if isinstance(agent, dict) else None
    configuration = (
        proof.get("proofAgentConfiguration") if isinstance(proof, dict) else None
    )
    context = configuration.get("context") if isinstance(configuration, dict) else None
    metrics = row.get("proofMetrics")
    rounds = proof.get("proofAgentRounds") if isinstance(proof, dict) else None
    if (
        counterexample.get("kind") != "formalSqlCountermodel"
        or not isinstance(proof, dict)
        or proof.get("backendStatus") != "proof_complete"
        or proof.get("certification") != "FORMAL-COUNTERMODEL"
        or not isinstance(workspace, dict)
        or not isinstance(agent, dict)
        or not isinstance(rounds, list)
        or not rounds
        or any(not isinstance(value, dict) for value in rounds)
        or agent != rounds[-1]
        or agent.get("success") is not True
        or agent.get("candidateClaim") != "formal_countermodel"
        or agent.get("candidateProblemCompilePassed") is not True
        or agent.get("candidateHasFinalTheorem") is not True
        or agent.get("proofCheckExitCode") != 0
        or agent.get("proofCheckTimedOut") is not False
        or not isinstance(audit, dict)
        or audit.get("passed") is not True
        or audit.get("findings") != []
        or counterexample.get("theorem") != "generated_verification_certificate"
        or counterexample.get("trusted_check_exit_code") != 0
        or counterexample.get("problem_path") != workspace.get("problemPath")
        or counterexample.get("goal_path") != workspace.get("goalPath")
        or counterexample.get("problem_sha256")
        != agent.get("candidateProblemSha256")
        or counterexample.get("context_manifest_sha256")
        != agent.get("contextManifestSha256")
        or counterexample.get("authority_closure_sha256")
        != agent.get("authorityClosureSha256")
        or not isinstance(context, dict)
        or configuration.get("enabled") is not True
        or counterexample.get("context_manifest_sha256")
        != context.get("manifestSha256")
        or not isinstance(metrics, dict)
        or metrics.get("proofRoundCount", 0) < 1
        or metrics.get("finalProofCheckElapsedMs") is None
        or not isinstance(metrics.get("proofSource"), dict)
        or metrics["proofSource"].get("present") is not True
        or metrics["proofSource"].get("sha256")
        != counterexample.get("problem_sha256")
    ):
        raise PublishError(
            f"{case}: FORMAL-COUNTERMODEL lacks a fully bound trusted Rocq certificate"
        )

    resolved: dict[str, Path] = {}
    for field, workspace_field, digest_field in (
        ("problem_path", "problemPath", "problem_sha256"),
        ("goal_path", "goalPath", None),
    ):
        value = counterexample.get(field)
        if not isinstance(value, str) or value != workspace.get(workspace_field):
            raise PublishError(
                f"{case}: FORMAL-COUNTERMODEL {field} binding is malformed"
            )
        path = resolve_case_artifact(
            source_dir, value, f"{case}.counterexample.{field}"
        )
        resolved[field] = path
        if digest_field is not None and sha256(path) != counterexample.get(
            digest_field
        ):
            raise PublishError(
                f"{case}: FORMAL-COUNTERMODEL {field} digest drifted"
            )

    verification_mode = proof.get("verificationMode")
    try:
        problem_text = resolved["problem_path"].read_text(encoding="utf-8")
        goal_text = resolved["goal_path"].read_text(encoding="utf-8")
    except (OSError, UnicodeError) as error:
        raise PublishError(
            f"{case}: FORMAL-COUNTERMODEL source is not readable UTF-8: {error}"
        ) from error
    if (
        not isinstance(verification_mode, str)
        or not problem_declares_formal_countermodel_claim(problem_text)
        or not problem_declares_final_theorem(problem_text, verification_mode)
        or not rocq_declares_direct_theorem(
            goal_text, "generated_verification_certificate"
        )
    ):
        raise PublishError(
            f"{case}: FORMAL-COUNTERMODEL source does not declare the certified claim"
        )

    context_value = context.get("manifestPath")
    if context_value != workspace.get("contextManifestPath"):
        raise PublishError(
            f"{case}: FORMAL-COUNTERMODEL context manifest binding is malformed"
        )
    context_path = resolve_case_artifact(
        source_dir, context_value, f"{case}.counterexample.contextManifest"
    )
    if sha256(context_path) != counterexample.get("context_manifest_sha256"):
        raise PublishError(
            f"{case}: FORMAL-COUNTERMODEL context manifest digest drifted"
        )
    manifest = load_json(context_path)
    goal_binding = manifest.get("goalModule") if isinstance(manifest, dict) else None
    if (
        not isinstance(goal_binding, dict)
        or goal_binding.get("path") != "Goal.v"
        or goal_binding.get("sha256") != sha256(resolved["goal_path"])
        or nonnegative_integer(
            goal_binding.get("bytes"), f"{case}.counterexample.goalModule.bytes"
        )
        != resolved["goal_path"].stat().st_size
    ):
        raise PublishError(
            f"{case}: FORMAL-COUNTERMODEL Goal.v context binding drifted"
        )

    closure_path = resolve_case_artifact(
        source_dir,
        agent.get("authorityClosurePath"),
        f"{case}.counterexample.authorityClosure",
    )
    if sha256(closure_path) != counterexample.get("authority_closure_sha256"):
        raise PublishError(
            f"{case}: FORMAL-COUNTERMODEL authority closure digest drifted"
        )
    checked_problem = closure_path.parent / "Problem.v"
    checked_goal = closure_path.parent / "Goal.v"
    if (
        not checked_problem.is_file()
        or checked_problem.is_symlink()
        or sha256(checked_problem) != sha256(resolved["problem_path"])
        or not checked_goal.is_file()
        or checked_goal.is_symlink()
        or sha256(checked_goal) != sha256(resolved["goal_path"])
    ):
        raise PublishError(
            f"{case}: FORMAL-COUNTERMODEL checked workspace binding drifted"
        )


def validate_counterexample_provider_commands(
    report: dict[str, Any], case: str
) -> None:
    rounds = report.get("rounds")
    if not isinstance(rounds, list):
        raise PublishError(f"{case}: report counterexample rounds are malformed")
    for index, round_record in enumerate(rounds):
        assessment = (
            round_record.get("assessment") if isinstance(round_record, dict) else None
        )
        provider = assessment.get("provider") if isinstance(assessment, dict) else None
        if provider is None:
            continue
        if (
            not isinstance(provider, dict)
            or provider.get("command") != DEFAULT_COUNTEREXAMPLE_COMMAND
        ):
            raise PublishError(
                f"{case}: counterexample round {index + 1} used an overridden provider command"
            )
        if provider.get("usage") is not None:
            canonical_usage(
                provider.get("usage"),
                f"{case}.rounds[{index}].assessment.provider.usage",
            )


def nonnegative_integer(value: Any, location: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value < 0:
        raise PublishError(f"{location} must be a nonnegative integer")
    return value


def diagnostic_elapsed_warning(
    *,
    round_number: int,
    sequence: int,
    requested_timeout_seconds: int,
    effective_timeout_seconds: int,
    elapsed_ms: int,
) -> dict[str, Any] | None:
    """Derive non-semantic host scheduling/reap telemetry from bound evidence."""

    limit_ms = (
        effective_timeout_seconds * 1000 + DIAGNOSTIC_ELAPSED_KILL_MARGIN_MS
    )
    if elapsed_ms <= limit_ms:
        return None
    return {
        "code": DIAGNOSTIC_ELAPSED_WARNING_CODE,
        "round": round_number,
        "sequence": sequence,
        "requestedTimeoutSeconds": requested_timeout_seconds,
        "effectiveTimeoutSeconds": effective_timeout_seconds,
        "elapsedMs": elapsed_ms,
        "timeoutPlusKillMarginMs": limit_ms,
        "overrunMs": elapsed_ms - limit_ms,
    }


def diagnostic_clock_warning(
    *,
    round_number: int,
    sequence: int,
    prior_estimated_end_unix_ms: int | None,
    started_at_unix_ms: int,
) -> dict[str, Any] | None:
    """Describe wall-clock regression without making it proof authority."""

    if (
        prior_estimated_end_unix_ms is None
        or started_at_unix_ms >= prior_estimated_end_unix_ms
    ):
        return None
    return {
        "code": "diagnostic_wall_clock_regressed_or_overlapped",
        "round": round_number,
        "sequence": sequence,
        "startedAtUnixMs": started_at_unix_ms,
        "priorEstimatedEndUnixMs": prior_estimated_end_unix_ms,
        "apparentRegressionMs": prior_estimated_end_unix_ms
        - started_at_unix_ms,
    }


def trusted_elapsed_warning(
    *,
    phase: str,
    timeout_seconds: int,
    elapsed_ms: int,
    workspace_generation: int | None = None,
    round_number: int | None = None,
) -> dict[str, Any] | None:
    limit_ms = timeout_seconds * 1000 + DIAGNOSTIC_ELAPSED_KILL_MARGIN_MS
    if elapsed_ms <= limit_ms:
        return None
    warning: dict[str, Any] = {
        "code": TRUSTED_ELAPSED_WARNING_CODE,
        "phase": phase,
        "timeoutSeconds": timeout_seconds,
        "elapsedMs": elapsed_ms,
        "timeoutPlusKillMarginMs": limit_ms,
        "overrunMs": elapsed_ms - limit_ms,
    }
    if workspace_generation is not None:
        warning["workspaceGeneration"] = workspace_generation
    if round_number is not None:
        warning["round"] = round_number
    return warning


def validate_trusted_elapsed_warnings(
    value: Any, location: str
) -> list[dict[str, Any]]:
    if not isinstance(value, list):
        raise PublishError(f"{location} is malformed")
    base_keys = {
        "code",
        "phase",
        "timeoutSeconds",
        "elapsedMs",
        "timeoutPlusKillMarginMs",
        "overrunMs",
    }
    allowed_phases = {
        "trusted_environment_preflight",
        "initial_problem_compile",
        "final_trusted_check",
        "deterministic_tail_trusted_check",
    }
    for index, warning in enumerate(value):
        item_location = f"{location}[{index}]"
        if (
            not isinstance(warning, dict)
            or set(warning) not in (
                base_keys | {"workspaceGeneration"},
                base_keys | {"round"},
            )
            or warning.get("code") != TRUSTED_ELAPSED_WARNING_CODE
            or warning.get("phase") not in allowed_phases
        ):
            raise PublishError(f"{item_location} is malformed")
        timeout = nonnegative_integer(
            warning.get("timeoutSeconds"), f"{item_location}.timeoutSeconds"
        )
        elapsed = nonnegative_integer(
            warning.get("elapsedMs"), f"{item_location}.elapsedMs"
        )
        limit = nonnegative_integer(
            warning.get("timeoutPlusKillMarginMs"),
            f"{item_location}.timeoutPlusKillMarginMs",
        )
        overrun = nonnegative_integer(
            warning.get("overrunMs"), f"{item_location}.overrunMs"
        )
        if (
            timeout < 1
            or limit != timeout * 1000 + DIAGNOSTIC_ELAPSED_KILL_MARGIN_MS
            or overrun < 1
            or elapsed != limit + overrun
        ):
            raise PublishError(f"{item_location} has incoherent elapsed telemetry")
        if "workspaceGeneration" in warning:
            generation = nonnegative_integer(
                warning["workspaceGeneration"],
                f"{item_location}.workspaceGeneration",
            )
            if generation < 1 or warning["phase"] not in {
                "trusted_environment_preflight",
                "initial_problem_compile",
            }:
                raise PublishError(f"{item_location} has an invalid generation phase")
        else:
            round_number = nonnegative_integer(
                warning["round"], f"{item_location}.round"
            )
            if round_number < 1 or warning["phase"] not in {
                "final_trusted_check",
                "deterministic_tail_trusted_check",
            }:
                raise PublishError(f"{item_location} has an invalid round phase")
    return value


def validate_diagnostic_elapsed_warnings(
    value: Any, location: str
) -> list[dict[str, Any]]:
    """Require the exact canonical warning schema before evidence comparison."""

    if not isinstance(value, list):
        raise PublishError(f"{location} is malformed")
    expected_keys = {
        "code",
        "round",
        "sequence",
        "requestedTimeoutSeconds",
        "effectiveTimeoutSeconds",
        "elapsedMs",
        "timeoutPlusKillMarginMs",
        "overrunMs",
    }
    for index, warning in enumerate(value):
        item_location = f"{location}[{index}]"
        if not isinstance(warning, dict) or set(warning) != expected_keys:
            raise PublishError(f"{item_location} is malformed")
        if warning.get("code") != DIAGNOSTIC_ELAPSED_WARNING_CODE:
            raise PublishError(f"{item_location}.code is malformed")
        numeric = {
            key: nonnegative_integer(warning.get(key), f"{item_location}.{key}")
            for key in expected_keys - {"code"}
        }
        if (
            numeric["round"] < 1
            or numeric["sequence"] < 1
            or numeric["requestedTimeoutSeconds"] < 1
            or numeric["effectiveTimeoutSeconds"] < 1
            or numeric["effectiveTimeoutSeconds"]
            > numeric["requestedTimeoutSeconds"]
        ):
            raise PublishError(f"{item_location} has an invalid identity or timeout")
        expected_limit = (
            numeric["effectiveTimeoutSeconds"] * 1000
            + DIAGNOSTIC_ELAPSED_KILL_MARGIN_MS
        )
        if (
            numeric["timeoutPlusKillMarginMs"] != expected_limit
            or numeric["overrunMs"] < 1
            or numeric["elapsedMs"]
            != numeric["timeoutPlusKillMarginMs"] + numeric["overrunMs"]
        ):
            raise PublishError(f"{item_location} has incoherent elapsed telemetry")
    return value


def validate_diagnostic_clock_warnings(
    value: Any, location: str
) -> list[dict[str, Any]]:
    """Require the exact non-semantic wall-clock warning schema."""

    if not isinstance(value, list):
        raise PublishError(f"{location} is malformed")
    expected_keys = {
        "code",
        "round",
        "sequence",
        "startedAtUnixMs",
        "priorEstimatedEndUnixMs",
        "apparentRegressionMs",
    }
    for index, warning in enumerate(value):
        item_location = f"{location}[{index}]"
        if (
            not isinstance(warning, dict)
            or set(warning) != expected_keys
            or warning.get("code")
            != "diagnostic_wall_clock_regressed_or_overlapped"
        ):
            raise PublishError(f"{item_location} is malformed")
        numeric = {
            key: nonnegative_integer(warning.get(key), f"{item_location}.{key}")
            for key in expected_keys - {"code"}
        }
        if (
            numeric["round"] < 1
            or numeric["sequence"] < 1
            or numeric["apparentRegressionMs"] < 1
            or numeric["priorEstimatedEndUnixMs"]
            - numeric["startedAtUnixMs"]
            != numeric["apparentRegressionMs"]
        ):
            raise PublishError(f"{item_location} has incoherent clock telemetry")
    return value


def strip_rocq_comments(text: str) -> str:
    """Replace nested Rocq comments with whitespace while preserving strings."""
    output: list[str] = []
    index = 0
    comment_depth = 0
    in_string = False
    while index < len(text):
        if comment_depth > 0:
            if text.startswith("(*", index):
                comment_depth += 1
                output.append("  ")
                index += 2
            elif text.startswith("*)", index):
                comment_depth -= 1
                output.append("  ")
                index += 2
            else:
                output.append("\n" if text[index] == "\n" else " ")
                index += 1
            continue

        if not in_string and text.startswith("(*", index):
            comment_depth = 1
            output.append("  ")
            index += 2
        elif text[index] == '"':
            output.append(text[index])
            index += 1
            if in_string and index < len(text) and text[index] == '"':
                output.append(text[index])
                index += 1
            else:
                in_string = not in_string
        else:
            output.append(text[index])
            index += 1
    return "".join(output)


def rocq_sentences(text: str) -> list[str]:
    """Split Rocq text at sentence-ending periods outside string literals."""
    sentences: list[str] = []
    start = 0
    index = 0
    in_string = False
    while index < len(text):
        if text[index] == '"':
            if in_string and index + 1 < len(text) and text[index + 1] == '"':
                index += 2
                continue
            in_string = not in_string
        elif (
            not in_string
            and text[index] == "."
            and (index + 1 == len(text) or text[index + 1] in " \t\n\r\v\f")
        ):
            sentences.append(text[start : index + 1])
            start = index + 1
        index += 1
    if any(not character.isspace() for character in text[start:]):
        sentences.append(text[start:])
    return sentences


def final_theorem_name(verification_mode: str) -> str:
    """Return the generated final theorem required by one verification mode."""
    normalized = verification_mode.replace("-", "_")
    if normalized in {"safe_unconditional", "outcome_unconditional"}:
        return "generated_queries_verified"
    if normalized == "conditional":
        return "generated_queries_equivalent"
    raise PublishError(f"unknown verification mode {verification_mode!r}")


def problem_declares_final_theorem(text: str, verification_mode: str) -> bool:
    """Recognize this mode's direct final theorem outside Rocq comments."""
    required_name = final_theorem_name(verification_mode)
    uncommented = strip_rocq_comments(text)
    return any(
        re.findall(r"[A-Za-z0-9_]+", sentence)[:2]
        == ["Theorem", required_name]
        for sentence in rocq_sentences(uncommented)
    )


def problem_declares_formal_countermodel_claim(text: str) -> bool:
    expected = [
        "Definition",
        "generated_verification_claim",
        "Logos",
        "FormalSQL",
        "VerificationConditions",
        "verification_claim_kind",
        "Logos",
        "FormalSQL",
        "VerificationConditions",
        "VerificationCountermodel",
    ]
    declarations = [
        re.findall(r"[A-Za-z0-9_]+", sentence)
        for sentence in rocq_sentences(strip_rocq_comments(text))
        if re.findall(r"[A-Za-z0-9_]+", sentence)[:2]
        == ["Definition", "generated_verification_claim"]
    ]
    return declarations == [expected]


def problem_declares_equivalence_claim(text: str) -> bool:
    expected = [
        "Definition",
        "generated_verification_claim",
        "Logos",
        "FormalSQL",
        "VerificationConditions",
        "verification_claim_kind",
        "Logos",
        "FormalSQL",
        "VerificationConditions",
        "VerificationEquivalence",
    ]
    declarations = [
        re.findall(r"[A-Za-z0-9_]+", sentence)
        for sentence in rocq_sentences(strip_rocq_comments(text))
        if re.findall(r"[A-Za-z0-9_]+", sentence)[:2]
        == ["Definition", "generated_verification_claim"]
    ]
    return declarations == [expected]


def problem_conditional_provenance(text: str) -> tuple[str, str] | None:
    uncommented = strip_rocq_comments(text)
    sentences = rocq_sentences(uncommented)
    if any(
        re.findall(r"[A-Za-z0-9_]+", sentence)[:2]
        == ["Definition", "generated_verification_claim"]
        for sentence in sentences
    ):
        return None
    sources = [
        re.findall(r"[A-Za-z0-9_]+", sentence)
        for sentence in sentences
        if re.findall(r"[A-Za-z0-9_]+", sentence)[:2]
        == ["Definition", "generated_precondition_source"]
    ]
    prefix = [
        "Definition",
        "generated_precondition_source",
        "Logos",
        "FormalSQL",
        "VerificationConditions",
        "precondition_source",
        "Logos",
        "FormalSQL",
        "VerificationConditions",
    ]
    constructors = {
        "PreconditionDerived": "derived",
        "PreconditionExternal": "external",
    }
    if len(sources) != 1 or sources[0][:-1] != prefix:
        return None
    definitions = [
        sentence.strip()
        for sentence in sentences
        if re.findall(r"[A-Za-z0-9_]+", sentence)[:6]
        == [
            "Definition",
            "generated_precondition",
            "Logos",
            "FormalSQL",
            "VerificationConditions",
            "verification_condition",
        ]
    ]
    source = constructors.get(sources[0][-1])
    return (source, definitions[0]) if source is not None and len(definitions) == 1 else None


def rocq_declares_direct_theorem(text: str, name: str) -> bool:
    return any(
        re.findall(r"[A-Za-z0-9_]+", sentence)[:2] == ["Theorem", name]
        for sentence in rocq_sentences(strip_rocq_comments(text))
    )


def load_json_array(path: Path, location: str) -> list[Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise PublishError(f"cannot read {location} {path}: {error}") from error
    if not isinstance(value, list):
        raise PublishError(f"{location} {path} must contain one JSON array")
    return value


def resolve_case_artifact(source_dir: Path, value: Any, location: str) -> Path:
    if not isinstance(value, str) or not value:
        raise PublishError(f"{location} must be a nonempty path")
    recorded = Path(value).expanduser()
    candidate = recorded if recorded.is_absolute() else source_dir / recorded
    if not candidate.is_file() or candidate.is_symlink():
        raise PublishError(f"{location} is missing, non-regular, or symlinked")
    resolved = candidate.resolve()
    try:
        resolved.relative_to(source_dir.resolve())
    except ValueError as error:
        raise PublishError(f"{location} escapes its case evidence") from error
    return resolved


def require_real_directory_chain(
    source_dir: Path, directory: Path, location: str
) -> None:
    try:
        relative = directory.relative_to(source_dir)
    except ValueError as error:
        raise PublishError(f"{location} escapes its case evidence") from error
    current = source_dir
    for component in (Path("."), *relative.parts):
        if component != Path("."):
            current /= component
        try:
            metadata = current.lstat()
        except OSError as error:
            raise PublishError(f"{location} directory is missing: {current}") from error
        if not stat.S_ISDIR(metadata.st_mode):
            raise PublishError(
                f"{location} contains a symlink or non-directory component: {current}"
            )


def publisher_workspace_display_path(path: Path) -> str:
    resolved = path.resolve()
    try:
        return resolved.relative_to(WORKFLOW_ROOT).as_posix()
    except ValueError:
        return str(resolved)


def validate_ordinary_terminal_problem_binding(
    case: str,
    row: dict[str, Any],
    proof: dict[str, Any],
    source_dir: Path,
    outcome: str,
) -> None:
    workspace = proof.get("proofWorkspace")
    final_agent = proof.get("proofAgent")
    metrics = row.get("proofMetrics")
    proof_source = metrics.get("proofSource") if isinstance(metrics, dict) else None
    expected_problem_value = "proof-stage/formal-sql/Problem.v"
    terminal_round = final_agent.get("round") if isinstance(final_agent, dict) else None
    if (
        isinstance(terminal_round, bool)
        or not isinstance(terminal_round, int)
        or terminal_round < 1
    ):
        raise PublishError(f"{case}: ordinary terminal proof has invalid round")
    expected_closure_value = (
        f"proof-stage/proof-agent/rounds/{terminal_round:02d}/"
        "checked-workspace/authority-closure.txt"
    )
    live_problem = source_dir / expected_problem_value
    checked_problem = source_dir / Path(expected_closure_value).parent / "Problem.v"
    if (
        not isinstance(workspace, dict)
        or workspace.get("problemPath") != expected_problem_value
        or not isinstance(final_agent, dict)
        or final_agent.get("authorityClosurePath") != expected_closure_value
        or not isinstance(proof_source, dict)
        or proof_source.get("path") != publisher_workspace_display_path(live_problem)
        or proof_source.get("present") is not True
    ):
        raise PublishError(f"{case}: ordinary terminal proof paths are not canonical")
    for path, label in (
        (live_problem, "live Problem.v"),
        (checked_problem, "checked Problem.v"),
    ):
        require_real_directory_chain(source_dir, path.parent, f"{case}.{label}")
        try:
            metadata = path.lstat()
        except OSError as error:
            raise PublishError(f"{case}: {label} is missing") from error
        if not stat.S_ISREG(metadata.st_mode) or metadata.st_size == 0:
            raise PublishError(f"{case}: {label} is not a regular non-symlink file")
    live_bytes = live_problem.read_bytes()
    checked_bytes = checked_problem.read_bytes()
    live_sha256 = hashlib.sha256(live_bytes).hexdigest()
    if (
        live_bytes != checked_bytes
        or final_agent.get("candidateProblemSha256") != live_sha256
        or proof_source.get("sha256") != live_sha256
        or proof_source.get("bytes") != len(live_bytes)
    ):
        raise PublishError(
            f"{case}: ordinary terminal live/checked/candidate Problem.v binding drifted"
        )
    try:
        problem_text = live_bytes.decode("utf-8", errors="strict")
    except UnicodeError as error:
        raise PublishError(f"{case}: ordinary Problem.v is not UTF-8") from error
    verification_mode = proof.get("verificationMode")
    if not isinstance(verification_mode, str) or not problem_declares_final_theorem(
        problem_text, verification_mode
    ):
        raise PublishError(f"{case}: ordinary Problem.v lacks its direct final theorem")
    normalized_mode = verification_mode.replace("-", "_")
    if final_agent.get("candidateClaim") != "equivalence":
        raise PublishError(f"{case}: ordinary report claim is not equivalence")
    if normalized_mode in {"safe_unconditional", "outcome_unconditional"}:
        if (
            not problem_declares_equivalence_claim(problem_text)
            or final_agent.get("preconditionSource") is not None
            or final_agent.get("preconditionDefinition") is not None
        ):
            raise PublishError(
                f"{case}: ordinary Problem.v lacks exact unconditional equivalence provenance"
            )
    elif normalized_mode == "conditional":
        provenance = problem_conditional_provenance(problem_text)
        expected_source = {
            "conditional_derived": "derived",
            "conditional_external": "external",
        }.get(outcome)
        if (
            provenance is None
            or provenance[0] != expected_source
            or final_agent.get("preconditionSource") != provenance[0]
            or final_agent.get("preconditionDefinition") != provenance[1]
        ):
            raise PublishError(
                f"{case}: ordinary conditional Problem.v provenance drifted"
            )
    else:
        raise PublishError(f"{case}: ordinary proof has unknown verification mode")


def validate_diagnostic_artifact_binding(
    case: str,
    source_dir: Path,
    value: Any,
    expected_relative_path: str,
    location: str,
) -> tuple[Path, dict[str, Any]]:
    """Validate one exact case-relative broker artifact binding."""
    if not isinstance(value, dict) or set(value) != {"path", "sha256", "bytes"}:
        raise PublishError(f"{location} must be an exact diagnostic artifact binding")
    if value.get("path") != expected_relative_path:
        raise PublishError(f"{location}.path does not identify the expected artifact")
    digest = value.get("sha256")
    if not valid_sha256(digest):
        raise PublishError(f"{location}.sha256 must be a lowercase SHA-256")
    size = nonnegative_integer(value.get("bytes"), f"{location}.bytes")
    path = resolve_case_artifact(source_dir, expected_relative_path, location)
    if sha256(path) != digest or path.stat().st_size != size:
        raise PublishError(f"{case}: diagnostic artifact binding drifted at {location}")
    return path, {
        "sourceRelativePath": expected_relative_path,
        "canonicalRelativePath": (
            Path("proof-agent-evidence")
            / Path(expected_relative_path).relative_to("proof-stage/proof-agent")
        ).as_posix(),
        "sha256": digest,
        "bytes": size,
    }


def validate_diagnostic_source_audit(
    path: Path, location: str, *, expected_passed: bool
) -> None:
    """Independently validate the serialized deterministic source-audit result."""
    audit = load_json(path)
    if set(audit) != {"passed", "scannedFiles", "findings"}:
        raise PublishError(f"{location} has a malformed source-audit schema")
    scanned_files = audit.get("scannedFiles")
    findings = audit.get("findings")
    if (
        audit.get("passed") is not expected_passed
        or not isinstance(scanned_files, list)
        or not scanned_files
        or any(not isinstance(value, str) or not value for value in scanned_files)
        or not isinstance(findings, list)
    ):
        raise PublishError(f"{location} has an incoherent source-audit outcome")
    for index, finding in enumerate(findings):
        finding_location = f"{location}.findings[{index}]"
        if not isinstance(finding, dict) or set(finding) != {
            "path",
            "line",
            "token",
            "excerpt",
        }:
            raise PublishError(f"{finding_location} is malformed")
        if nonnegative_integer(finding.get("line"), f"{finding_location}.line") == 0:
            raise PublishError(f"{finding_location}.line must be positive")
        for key in ("path", "token", "excerpt"):
            if not isinstance(finding.get(key), str) or not finding[key]:
                raise PublishError(f"{finding_location}.{key} must be nonempty text")
    if expected_passed and findings:
        raise PublishError(f"{location} is marked clean but contains findings")
    if not expected_passed and not findings:
        raise PublishError(f"{location} rejected no source construct")


DIAGNOSTIC_MODES = {"problem", "module", "scratch"}
DIAGNOSTIC_PURPOSES = {"static-obligation", "semantic-equivalence", "assembly"}


def validate_diagnostic_identity(
    mode: Any,
    candidate_path: Any,
    purpose: Any,
    candidate_sha256: Any,
    location: str,
) -> None:
    """Validate the exact identity carried by one protocol-v2 request."""
    if mode not in DIAGNOSTIC_MODES:
        raise PublishError(f"{location}.mode is invalid")
    if purpose not in DIAGNOSTIC_PURPOSES:
        raise PublishError(f"{location}.purpose is invalid")
    if not valid_sha256(candidate_sha256):
        raise PublishError(f"{location}.candidateSha256 is invalid")
    if not isinstance(candidate_path, str) or not candidate_path:
        raise PublishError(f"{location}.candidatePath is invalid")
    if mode == "problem":
        if candidate_path != "Problem.v":
            raise PublishError(
                f"{location}.candidatePath must be Problem.v in problem mode"
            )
        return
    if mode == "module":
        candidate = Path(candidate_path)
        parts = candidate.parts
        if (
            "\\" in candidate_path
            or candidate.is_absolute()
            or len(parts) != 2
            or parts[0] != "ProofModules"
            or candidate.as_posix() != candidate_path
            or re.fullmatch(r"[A-Z][A-Za-z0-9_]*\.v", parts[1]) is None
        ):
            raise PublishError(
                f"{location}.candidatePath must be "
                "ProofModules/<UppercaseRocqIdentifier>.v in module mode"
            )
        return
    if (
        "\\" in candidate_path
        or any(
            ord(character) < 32 or 127 <= ord(character) <= 159
            for character in candidate_path
        )
    ):
        raise PublishError(f"{location}.candidatePath is invalid")
    candidate = Path(candidate_path)
    parts = candidate.parts
    if (
        candidate.is_absolute()
        or len(parts) < 2
        or parts[0] != "scratch"
        or any(part in {"", ".", ".."} for part in parts)
        or candidate.as_posix() != candidate_path
        or candidate.suffix != ".v"
    ):
        raise PublishError(
            f"{location}.candidatePath must be normalized scratch/*.v"
        )


def validate_diagnostic_checkpoint_dedup(
    mode: str,
    candidate_sha256: str,
    active_checkpoint_sha256: str | None,
    location: str,
) -> None:
    if mode == "problem" and candidate_sha256 == active_checkpoint_sha256:
        raise PublishError(
            f"{location} duplicates the active successful Problem checkpoint"
        )


def candidate_problem_has_compile_authority(
    candidate_sha256: str,
    active_checkpoint_sha256: str | None,
    invocations: list[dict[str, Any]],
) -> bool:
    """Recognize a current pass or the exact active compile-clean checkpoint."""
    return candidate_sha256 == active_checkpoint_sha256 or any(
        invocation.get("compilePassed") is True
        and invocation.get("problemCompilePassed") is True
        and invocation.get("mode") == "problem"
        and invocation.get("candidatePath") == "Problem.v"
        and invocation.get("compileCheckpointAdvanced") is True
        and invocation.get("candidateSha256") == candidate_sha256
        for invocation in invocations
    )


def expected_diagnostic_compile_passed(
    *,
    mode: str,
    exit_code: int | None,
    timed_out: bool,
    error: str | None,
    reported_compile_passed: bool,
    durable_module_path: Path,
    trusted_cache_module_path: Path,
    candidate_sha256: str,
) -> tuple[bool, bool]:
    """Recognize ordinary success or a host-reconciled late module publication."""
    ordinary = exit_code == 0 and timed_out is False and error is None
    module_publication_bound = (
        trusted_cache_module_path.is_file()
        and not trusted_cache_module_path.is_symlink()
        and sha256(trusted_cache_module_path) == candidate_sha256
    )
    late_module_publication = (
        mode == "module"
        and not ordinary
        and reported_compile_passed is True
        and error is None
        and module_publication_bound
        and durable_module_path.is_file()
        and not durable_module_path.is_symlink()
        and sha256(durable_module_path) == candidate_sha256
    )
    if mode == "module" and reported_compile_passed is True:
        ordinary = ordinary and module_publication_bound
    return ordinary or late_module_publication, late_module_publication


def validate_diagnostic_request_v2(
    value: Any,
    *,
    mode: str,
    candidate_path: str,
    purpose: str,
    candidate_sha256: str,
    candidate_bytes: int,
    requested_timeout_seconds: int,
    location: str,
) -> None:
    expected_keys = {
        "schemaVersion",
        "nonce",
        "mode",
        "candidatePath",
        "purpose",
        "candidateSha256",
        "candidateBytes",
        "requestedTimeoutSeconds",
    }
    if not isinstance(value, dict) or set(value) != expected_keys:
        raise PublishError(f"{location} is not strict diagnostic schemaVersion 2")
    if (
        value.get("schemaVersion") != 2
        or not valid_sha256(value.get("nonce"))
        or value.get("mode") != mode
        or value.get("candidatePath") != candidate_path
        or value.get("purpose") != purpose
        or value.get("candidateSha256") != candidate_sha256
        or value.get("candidateBytes") != candidate_bytes
        or value.get("requestedTimeoutSeconds") != requested_timeout_seconds
    ):
        raise PublishError(f"{location} identity drifted")
    validate_diagnostic_identity(
        mode, candidate_path, purpose, candidate_sha256, location
    )


def validate_trusted_diagnostic_cache(
    case: str,
    source_dir: Path,
    agent_configuration: dict[str, Any],
    *,
    cache_binding: dict[str, Any] | None = None,
    authoritative_root: Path | None = None,
) -> tuple[Path, str, tuple[str, ...]]:
    manifest_value = (
        cache_binding.get("manifestPath")
        if cache_binding is not None
        else agent_configuration.get("diagnosticCacheManifestPath")
    )
    expected_manifest_sha256 = (
        cache_binding.get("manifestSha256")
        if cache_binding is not None
        else agent_configuration.get("diagnosticCacheManifestSha256")
    )
    if cache_binding is None and manifest_value != (
        "proof-stage/proof-agent/trusted-diagnostic-cache/SHA256SUMS"
    ):
        raise PublishError(f"{case}: trusted diagnostic cache path is invalid")
    manifest_path = resolve_case_artifact(
        source_dir, manifest_value, f"{case}.diagnosticCacheManifestPath"
    )
    manifest_sha256 = sha256(manifest_path)
    if expected_manifest_sha256 != manifest_sha256:
        raise PublishError(f"{case}: trusted diagnostic cache manifest drifted")
    cache_root = manifest_path.parent
    module_root = cache_root / "ProofModules"
    order_path = module_root / "ORDER"
    if (
        not module_root.is_dir()
        or module_root.is_symlink()
        or not order_path.is_file()
        or order_path.is_symlink()
    ):
        raise PublishError(f"{case}: trusted diagnostic module cache is invalid")
    try:
        order_text = order_path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as error:
        raise PublishError(f"{case}: cannot read trusted module order: {error}") from error
    module_names = order_text.splitlines()
    if order_text != "".join(f"{name}\n" for name in module_names):
        raise PublishError(f"{case}: trusted module order is noncanonical")
    if len(set(module_names)) != len(module_names) or any(
        re.fullmatch(r"[A-Z][A-Za-z0-9_]*\.v", name) is None
        for name in module_names
    ):
        raise PublishError(f"{case}: trusted module order contains an invalid entry")
    entries = list(TRUSTED_DIAGNOSTIC_CACHE_BASE_ENTRIES)
    for name in module_names:
        entries.extend((f"ProofModules/{name}", f"ProofModules/{name[:-2]}.vo"))
    for name in entries:
        path = cache_root / name
        if (
            not path.is_file()
            or path.is_symlink()
            or (name != "ProofModules/ORDER" and path.stat().st_size == 0)
        ):
            raise PublishError(f"{case}: trusted diagnostic cache entry is invalid")
    expected_manifest = "".join(
        f"{sha256(cache_root / name)}  {name}\n" for name in entries
    )
    if manifest_path.read_text(encoding="utf-8") != expected_manifest:
        raise PublishError(f"{case}: trusted diagnostic cache manifest is noncanonical")
    expected_root_names = {
        "Schema.v",
        "Schema.vo",
        "Queries.v",
        "Queries.vo",
        "Witness.v",
        "Witness.vo",
        "ProofModules",
        "SHA256SUMS",
    }
    if {path.name for path in cache_root.iterdir()} != expected_root_names:
        raise PublishError(f"{case}: trusted diagnostic cache has unexpected entries")
    expected_module_names = {"ORDER"}
    for name in module_names:
        expected_module_names.update((name, f"{name[:-2]}.vo"))
    if {path.name for path in module_root.iterdir()} != expected_module_names:
        raise PublishError(f"{case}: trusted module cache has unexpected entries")
    for name in TRUSTED_DIAGNOSTIC_CACHE_SOURCE_ENTRIES:
        authoritative = (
            authoritative_root or source_dir / "proof-stage/formal-sql"
        ) / name
        if (
            not authoritative.is_file()
            or authoritative.is_symlink()
            or (cache_root / name).read_bytes() != authoritative.read_bytes()
        ):
            raise PublishError(
                f"{case}: trusted diagnostic cache source binding drifted"
            )
    for name in module_names:
        authoritative = (
            authoritative_root or source_dir / "proof-stage/formal-sql"
        ) / "ProofModules" / name
        cached = module_root / name
        if (
            not authoritative.is_file()
            or authoritative.is_symlink()
            or cached.read_bytes() != authoritative.read_bytes()
        ):
            raise PublishError(f"{case}: trusted proof module source binding drifted")
    return manifest_path, manifest_sha256, tuple(entries)


CONTEXT_MANIFEST_BINDINGS = {
    "sourceSql": "source.sql",
    "targetSql": "target.sql",
    "queryShape": "query-shape.json",
    "orderedSignatures": "ordered-signatures.json",
    "observationCertificates": "observation-certificates.json",
    "semanticPrimer": "semantic-primer.md",
    "declarationSearch": "search-rocq-declarations.py",
    "schemaModule": "Schema.v",
    "queriesModule": "Queries.v",
    "witnessModule": "Witness.v",
    "goalModule": "Goal.v",
}


def canonical_json_sha256(value: Any) -> str:
    """Match Rust's recursively key-sorted compact UTF-8 JSON binding."""
    return hashlib.sha256(
        json.dumps(
            value,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
        ).encode("utf-8")
    ).hexdigest()


def validate_context_snapshot(
    case: str,
    root: Path,
    expected_manifest_sha256: Any,
    verification_mode: str,
    location: str,
) -> set[Path]:
    manifest_path = root / "context-manifest.json"
    if (
        not root.is_dir()
        or root.is_symlink()
        or not manifest_path.is_file()
        or manifest_path.is_symlink()
        or not valid_sha256(expected_manifest_sha256)
        or sha256(manifest_path) != expected_manifest_sha256
    ):
        raise PublishError(f"{case}: {location} context manifest drifted")
    manifest = load_json(manifest_path)
    expected_keys = {
        "schemaVersion",
        "authority",
        "verificationMode",
        "staticPromptAndPrimerBytes",
        *CONTEXT_MANIFEST_BINDINGS,
    }
    if (
        not isinstance(manifest, dict)
        or set(manifest) != expected_keys
        or manifest.get("schemaVersion") != 8
        or manifest.get("verificationMode") != verification_mode
        or not isinstance(manifest.get("authority"), str)
        or not manifest["authority"]
    ):
        raise PublishError(f"{case}: {location} context manifest is malformed")
    nonnegative_integer(
        manifest.get("staticPromptAndPrimerBytes"),
        f"{case}.{location}.staticPromptAndPrimerBytes",
    )
    selected = {manifest_path.resolve()}
    for field, name in CONTEXT_MANIFEST_BINDINGS.items():
        binding = manifest.get(field)
        path = root / name
        if (
            not isinstance(binding, dict)
            or set(binding) != {"path", "bytes", "sha256"}
            or binding.get("path") != name
            or not path.is_file()
            or path.is_symlink()
            or binding.get("sha256") != sha256(path)
            or nonnegative_integer(
                binding.get("bytes"), f"{case}.{location}.{field}.bytes"
            )
            != path.stat().st_size
        ):
            raise PublishError(f"{case}: {location} context binding {field} drifted")
        selected.add(path.resolve())
    return selected


CONTEXT_REPORT_BINDINGS = {
    "sourceSql": ("sourceSqlSha256", "sourceSqlBytes"),
    "targetSql": ("targetSqlSha256", "targetSqlBytes"),
    "queryShape": ("queryShapeSha256", "queryShapeBytes"),
    "orderedSignatures": (
        "orderedSignaturesSha256",
        "orderedSignaturesBytes",
    ),
    "observationCertificates": (
        "observationCertificatesSha256",
        "observationCertificatesBytes",
    ),
    "schemaModule": ("schemaModuleSha256", "schemaModuleBytes"),
    "queriesModule": ("queriesModuleSha256", "queriesModuleBytes"),
    "witnessModule": ("witnessModuleSha256", "witnessModuleBytes"),
    "declarationSearch": ("declarationSearchSha256", "declarationSearchBytes"),
}


def validate_final_context_report(
    case: str,
    root: Path,
    context: dict[str, Any],
    verification_mode: str,
    static_prompt_and_primer_bytes: Any,
) -> set[Path]:
    selected = validate_context_snapshot(
        case,
        root,
        context.get("manifestSha256"),
        verification_mode,
        "final live workspace",
    )
    manifest_path = root / "context-manifest.json"
    manifest = load_json(manifest_path)
    if (
        context.get("manifestBytes") != manifest_path.stat().st_size
        or manifest.get("staticPromptAndPrimerBytes")
        != static_prompt_and_primer_bytes
    ):
        raise PublishError(f"{case}: final proof-agent context summary drifted")
    for binding_name, (digest_field, bytes_field) in CONTEXT_REPORT_BINDINGS.items():
        binding = manifest[binding_name]
        if (
            context.get(digest_field) != binding["sha256"]
            or context.get(bytes_field) != binding["bytes"]
        ):
            raise PublishError(
                f"{case}: final proof-agent context {binding_name} summary drifted"
            )
    for binding_name, bytes_field in (
        ("semanticPrimer", "semanticPrimerBytes"),
        ("goalModule", "goalModuleBytes"),
    ):
        if context.get(bytes_field) != manifest[binding_name]["bytes"]:
            raise PublishError(
                f"{case}: final proof-agent context {binding_name} size drifted"
            )
    for field in ("problemModuleBytes", "generatedContextBytes"):
        nonnegative_integer(context.get(field), f"{case}.proofAgentContext.{field}")
    return selected


def validate_trusted_preflight_evidence(
    case: str,
    evidence_root: Path,
    generation: int,
    reported: Any,
) -> tuple[set[Path], int, dict[str, Any] | None]:
    location = f"workspace generation {generation} trusted preflight"
    required_keys = {"timeoutSeconds", "elapsedMs", "exitCode", "timedOut"}
    if not isinstance(reported, dict) or set(reported) != required_keys:
        raise PublishError(f"{case}: {location} record is malformed")
    root = (
        evidence_root
        / "workspace-generations"
        / f"{generation:04}"
        / "trusted-environment-preflight"
    )
    paths = {name: root / name for name in ("stdout.txt", "stderr.txt", "invocation.json")}
    if any(not path.is_file() or path.is_symlink() for path in paths.values()):
        raise PublishError(f"{case}: {location} evidence is missing")
    if load_json(paths["invocation.json"]) != reported:
        raise PublishError(f"{case}: {location} invocation drifted")
    elapsed = nonnegative_integer(reported.get("elapsedMs"), f"{case}.{location}.elapsedMs")
    if (
        reported.get("timeoutSeconds") != TRUSTED_CHECK_TIMEOUT_SECONDS
        or reported.get("exitCode") != 0
        or reported.get("timedOut") is not False
        or reported.get("error") is not None
    ):
        raise PublishError(f"{case}: {location} did not pass")
    warning = trusted_elapsed_warning(
        phase="trusted_environment_preflight",
        timeout_seconds=TRUSTED_CHECK_TIMEOUT_SECONDS,
        elapsed_ms=elapsed,
        workspace_generation=generation,
    )
    return ({path.resolve() for path in paths.values()}, elapsed, warning)


def validate_initial_checkpoint_evidence(
    case: str,
    evidence_root: Path,
    generation: int,
    expected: dict[str, Any] | None,
) -> tuple[set[Path], str, int, dict[str, Any] | None]:
    root = (
        evidence_root
        / "workspace-generations"
        / f"{generation:04}"
        / "initial-problem-checkpoint"
    )
    paths = {
        name: root / name
        for name in ("Problem.v", "stdout.txt", "stderr.txt", "invocation.json")
    }
    if any(not path.is_file() or path.is_symlink() for path in paths.values()):
        raise PublishError(
            f"{case}: workspace generation {generation} initial checkpoint is missing"
        )
    relative_problem = paths["Problem.v"].relative_to(evidence_root.parent.parent).as_posix()
    problem_sha256 = sha256(paths["Problem.v"])
    if expected is not None and (
        set(expected) != {"workspaceGeneration", "path", "sha256", "round", "sequence"}
        or expected.get("workspaceGeneration") != generation
        or expected.get("path") != relative_problem
        or expected.get("sha256") != problem_sha256
        or expected.get("round") != 0
        or expected.get("sequence") != 0
    ):
        raise PublishError(
            f"{case}: workspace generation {generation} checkpoint binding drifted"
        )
    invocation = load_json(paths["invocation.json"])
    elapsed = nonnegative_integer(
        invocation.get("elapsedMs"),
        f"{case}.workspaceGeneration[{generation}].initialProblemCompile.elapsedMs",
    )
    if (
        invocation.get("sequence") != 0
        or invocation.get("mode") != "problem"
        or invocation.get("candidatePath") != "Problem.v"
        or invocation.get("purpose") != "assembly"
        or invocation.get("candidateSha256") != problem_sha256
        or invocation.get("compilePassed") is not True
        or invocation.get("problemCompilePassed") is not True
        or invocation.get("compileCheckpointAdvanced") is not True
        or invocation.get("requestedTimeoutSeconds") != TRUSTED_CHECK_TIMEOUT_SECONDS
        or invocation.get("effectiveTimeoutSeconds") != TRUSTED_CHECK_TIMEOUT_SECONDS
        or invocation.get("exitCode") != 0
        or invocation.get("timedOut") is not False
        or invocation.get("error") is not None
        or invocation.get("stdoutSha256") != sha256(paths["stdout.txt"])
        or invocation.get("stderrSha256") != sha256(paths["stderr.txt"])
    ):
        raise PublishError(
            f"{case}: workspace generation {generation} initial checkpoint is incoherent"
        )
    warning = trusted_elapsed_warning(
        phase="initial_problem_compile",
        timeout_seconds=TRUSTED_CHECK_TIMEOUT_SECONDS,
        elapsed_ms=elapsed,
        workspace_generation=generation,
    )
    return (
        {path.resolve() for path in paths.values()},
        problem_sha256,
        elapsed,
        warning,
    )


def validate_proof_workspace_transitions(
    case: str,
    proof: dict[str, Any],
    rounds: list[dict[str, Any]],
    agent_configuration: dict[str, Any],
) -> tuple[list[dict[str, Any]], dict[int, dict[str, Any] | None]]:
    value = proof.get("proofWorkspaceTransitions", [])
    if not isinstance(value, list) or any(not isinstance(item, dict) for item in value):
        raise PublishError(f"{case}: proofWorkspaceTransitions is malformed")
    transitions: list[dict[str, Any]] = value
    by_generation: dict[int, dict[str, Any] | None] = {1: None}
    expected_from = 1
    previous_after = 0
    expected_keys = {
        "afterRound",
        "fromWorkspaceGeneration",
        "toWorkspaceGeneration",
        "reason",
        "triggeringHandoffSha256",
        "fromContextManifestSha256",
        "toContextManifestSha256",
        "fromTrustedDiagnosticCache",
        "newTrustedEnvironmentPreflight",
        "newInitialProblemCompileCheckpoint",
    }
    for transition_index, transition in enumerate(transitions):
        location = f"{case}.proofWorkspaceTransitions[{transition_index}]"
        after_round = nonnegative_integer(
            transition.get("afterRound"), f"{location}.afterRound"
        )
        from_generation = nonnegative_integer(
            transition.get("fromWorkspaceGeneration"),
            f"{location}.fromWorkspaceGeneration",
        )
        to_generation = nonnegative_integer(
            transition.get("toWorkspaceGeneration"),
            f"{location}.toWorkspaceGeneration",
        )
        from_cache = transition.get("fromTrustedDiagnosticCache")
        expected_cache_path = (
            "proof-stage/proof-agent/workspace-generations/"
            f"{from_generation:04}/trusted-diagnostic-cache/SHA256SUMS"
        )
        if (
            set(transition) != expected_keys
            or not (previous_after < after_round <= len(rounds))
            or from_generation != expected_from
            or to_generation != from_generation + 1
            or transition.get("reason") != "fixedWitnessReplacement"
            or not valid_sha256(transition.get("triggeringHandoffSha256"))
            or not valid_sha256(transition.get("fromContextManifestSha256"))
            or not valid_sha256(transition.get("toContextManifestSha256"))
            or not isinstance(from_cache, dict)
            or set(from_cache)
            != {"workspaceGeneration", "manifestPath", "manifestSha256"}
            or from_cache.get("workspaceGeneration") != from_generation
            or from_cache.get("manifestPath") != expected_cache_path
            or not valid_sha256(from_cache.get("manifestSha256"))
        ):
            raise PublishError(f"{location} is incoherent")
        triggering_round = rounds[after_round - 1]
        handoff = triggering_round.get("counterexampleHandoff")
        if (
            not isinstance(handoff, dict)
            or set(handoff) != {"decision", "reason", "guidance"}
            or handoff.get("decision") != "counterexample_candidate"
            or not isinstance(handoff.get("reason"), str)
            or not handoff["reason"].strip()
            or not isinstance(handoff.get("guidance"), str)
            or not handoff["guidance"].strip()
            or canonical_json_sha256(handoff)
            != transition.get("triggeringHandoffSha256")
            or triggering_round.get("workspaceGeneration") != from_generation
            or triggering_round.get("contextManifestSha256")
            != transition.get("fromContextManifestSha256")
        ):
            raise PublishError(f"{location} triggering handoff binding drifted")
        if after_round < len(rounds):
            next_round = rounds[after_round]
            if (
                next_round.get("workspaceGeneration") != to_generation
                or next_round.get("contextManifestSha256")
                != transition.get("toContextManifestSha256")
            ):
                raise PublishError(f"{location} next-round context binding drifted")
        by_generation[to_generation] = transition
        expected_from = to_generation
        previous_after = after_round

    expected_generation = 1
    transition_after = {item["afterRound"]: item for item in transitions}
    for round_index, record in enumerate(rounds, start=1):
        if record.get("workspaceGeneration") != expected_generation:
            raise PublishError(
                f"{case}: workspace generation drifted at proof round {round_index}"
            )
        if round_index in transition_after:
            expected_generation = transition_after[round_index][
                "toWorkspaceGeneration"
            ]
    context = agent_configuration.get("context")
    if not isinstance(context, dict) or context.get("manifestPath") != (
        "proof-stage/formal-sql/context-manifest.json"
    ):
        raise PublishError(f"{case}: final proof-agent context is malformed")
    final_context_sha256 = context.get("manifestSha256")
    expected_final_context_sha256 = (
        transitions[-1]["toContextManifestSha256"]
        if transitions
        else (rounds[-1].get("contextManifestSha256") if rounds else final_context_sha256)
    )
    if (
        not valid_sha256(final_context_sha256)
        or final_context_sha256 != expected_final_context_sha256
    ):
        raise PublishError(f"{case}: final proof-agent context generation drifted")
    return transitions, by_generation


def collect_proof_agent_broker_evidence(
    case: str,
    source_dir: Path,
    report: dict[str, Any] | None,
    source_full_run_summary_sha256: str,
    *,
    legacy_catalog: bool,
) -> dict[str, Any] | None:
    """Validate and enumerate self-contained host-broker evidence for one case."""
    if not valid_sha256(source_full_run_summary_sha256):
        raise PublishError(f"{case}: source full-run summary digest is malformed")
    proof = report.get("proof") if isinstance(report, dict) else None
    agent_configuration = (
        proof.get("proofAgentConfiguration") if isinstance(proof, dict) else None
    )
    if not isinstance(agent_configuration, dict):
        return None
    verification_mode = proof.get("verificationMode")
    if not isinstance(verification_mode, str):
        raise PublishError(f"{case}: proof verification mode is missing or malformed")
    validate_fixed_fields(
        agent_configuration,
        proof_agent_diagnostic_configuration(legacy_catalog=legacy_catalog),
        f"{case}.proofAgentConfiguration",
    )
    (
        cache_manifest_path,
        cache_manifest_sha256,
        trusted_cache_entries,
    ) = validate_trusted_diagnostic_cache(
        case, source_dir, agent_configuration
    )
    selected_paths = {cache_manifest_path}
    for relative in (
        "proof-stage/formal-sql/run-rocq-check.sh",
        "proof-stage/proof-agent/trusted-launcher/run-proof-agent-docker.sh",
        "proof-stage/proof-agent/trusted-launcher/run-trusted-rocq-check.sh",
    ):
        path = source_dir / relative
        if not path.is_file() or path.is_symlink():
            raise PublishError(
                f"{case}: materialized trusted script is missing or symlinked: {relative}"
            )
        selected_paths.add(path.resolve())
    cache_entries = []
    for name in trusted_cache_entries:
        path = cache_manifest_path.parent / name
        selected_paths.add(path.resolve())
        entry = {
            "name": name,
            "sha256": sha256(path),
            "bytes": path.stat().st_size,
        }
        if name in TRUSTED_DIAGNOSTIC_CACHE_SOURCE_ENTRIES:
            entry["authoritativeSourceSha256"] = sha256(
                source_dir / "proof-stage/formal-sql" / name
            )
        elif name.startswith("ProofModules/") and name.endswith(".v"):
            entry["authoritativeSourceSha256"] = sha256(
                source_dir / "proof-stage/formal-sql" / name
            )
        cache_entries.append(entry)

    evidence_root = source_dir / "proof-stage/proof-agent"
    if (
        not evidence_root.is_dir()
        or evidence_root.is_symlink()
        or evidence_root.resolve().parent.parent != source_dir.resolve()
    ):
        raise PublishError(f"{case}: proof-agent broker evidence root is missing")
    rounds_value = proof.get("proofAgentRounds", [])
    if not isinstance(rounds_value, list) or any(
        not isinstance(record, dict) for record in rounds_value
    ):
        raise PublishError(f"{case}: malformed proof-agent rounds")
    rounds: list[dict[str, Any]] = rounds_value
    transitions, generation_records = validate_proof_workspace_transitions(
        case, proof, rounds, agent_configuration
    )
    validate_proof_agent_session_sequence(
        rounds,
        transitions,
        case,
        allow_terminal_unavailable_session=(
            proof.get("deterministicTailRecovery") is not None
        ),
    )
    final_workspace_generation = max(generation_records)
    trusted_cache_roots_by_generation = {
        final_workspace_generation: cache_manifest_path.parent
    }
    workspace_generation_cache_evidence = [
        {
            "workspaceGeneration": final_workspace_generation,
            "archive": False,
            "manifestSourceRelativePath": cache_manifest_path.relative_to(
                source_dir
            ).as_posix(),
            "manifestSha256": cache_manifest_sha256,
            "entries": list(trusted_cache_entries),
        }
    ]
    for transition in transitions:
        generation = transition["fromWorkspaceGeneration"]
        triggering_round = rounds[transition["afterRound"] - 1]
        triggering_closure = resolve_case_artifact(
            source_dir,
            triggering_round.get("authorityClosurePath"),
            f"{case}.workspaceGeneration[{generation}].authorityClosurePath",
        )
        archived_manifest, archived_sha256, archived_entries = (
            validate_trusted_diagnostic_cache(
                case,
                source_dir,
                agent_configuration,
                cache_binding=transition["fromTrustedDiagnosticCache"],
                authoritative_root=triggering_closure.parent,
            )
        )
        trusted_cache_roots_by_generation[generation] = archived_manifest.parent
        selected_paths.add(archived_manifest.resolve())
        for name in archived_entries:
            selected_paths.add((archived_manifest.parent / name).resolve())
        workspace_generation_cache_evidence.append(
            {
                "workspaceGeneration": generation,
                "archive": True,
                "manifestSourceRelativePath": archived_manifest.relative_to(
                    source_dir
                ).as_posix(),
                "manifestSha256": archived_sha256,
                "entries": list(archived_entries),
            }
        )
    if set(trusted_cache_roots_by_generation) != set(generation_records):
        raise PublishError(f"{case}: workspace generation cache authority is incomplete")
    initial_checkpoint_by_generation: dict[int, str] = {}
    initial_checkpoint_path_by_generation: dict[int, str] = {}
    initial_elapsed_by_generation: dict[int, int] = {}
    preflight_elapsed_by_generation: dict[int, int] = {}
    initial_elapsed_warnings: list[dict[str, Any]] = []
    preflight_elapsed_warnings: list[dict[str, Any]] = []
    trusted_elapsed_warnings: list[dict[str, Any]] = []
    for generation, transition in sorted(generation_records.items()):
        expected_checkpoint = (
            transition.get("newInitialProblemCompileCheckpoint")
            if transition is not None
            else None
        )
        checkpoint_paths, checkpoint_sha256, checkpoint_elapsed, checkpoint_warning = (
            validate_initial_checkpoint_evidence(
                case,
                evidence_root,
                generation,
                expected_checkpoint,
            )
        )
        selected_paths.update(checkpoint_paths)
        initial_checkpoint_by_generation[generation] = checkpoint_sha256
        initial_checkpoint_path_by_generation[generation] = (
            expected_checkpoint["path"]
            if expected_checkpoint is not None
            else (
                "proof-stage/proof-agent/workspace-generations/"
                f"{generation:04}/initial-problem-checkpoint/Problem.v"
            )
        )
        initial_elapsed_by_generation[generation] = checkpoint_elapsed

        reported_preflight = (
            agent_configuration.get("trustedEnvironmentPreflight")
            if transition is None
            else transition.get("newTrustedEnvironmentPreflight")
        )
        preflight_paths, preflight_elapsed, preflight_warning = (
            validate_trusted_preflight_evidence(
                case,
                evidence_root,
                generation,
                reported_preflight,
            )
        )
        selected_paths.update(preflight_paths)
        preflight_elapsed_by_generation[generation] = preflight_elapsed
        if preflight_warning is not None:
            preflight_elapsed_warnings.append(preflight_warning)
            trusted_elapsed_warnings.append(preflight_warning)
        if checkpoint_warning is not None:
            initial_elapsed_warnings.append(checkpoint_warning)
            trusted_elapsed_warnings.append(checkpoint_warning)

    final_context = agent_configuration["context"]
    selected_paths.update(
        validate_final_context_report(
            case,
            source_dir / "proof-stage/formal-sql",
            final_context,
            verification_mode,
            agent_configuration.get("staticPromptAndPrimerBytes"),
        )
    )
    initial_sha256 = initial_checkpoint_by_generation[1]
    initial_elapsed = sum(initial_elapsed_by_generation.values())
    active_workspace_generation: int | None = None
    active_checkpoint_sha256: str | None = None
    previous_diagnostic_end: int | None = None
    invocations: list[dict[str, Any]] = []
    diagnostic_elapsed_warnings: list[dict[str, Any]] = []
    diagnostic_clock_warnings: list[dict[str, Any]] = []
    accepted_source_audit_evidence: list[dict[str, Any]] = []
    rejected_source_audit_evidence: list[dict[str, Any]] = []
    broker_metrics = {key: 0 for key in PROOF_AGENT_BROKER_METRIC_KEYS}
    for round_index, record in enumerate(rounds, start=1):
        if record.get("round") != round_index:
            raise PublishError(f"{case}: proof-agent rounds are not consecutive")
        workspace_generation = nonnegative_integer(
            record.get("workspaceGeneration"),
            f"{case}.proofAgentRounds[{round_index - 1}].workspaceGeneration",
        )
        if workspace_generation != active_workspace_generation:
            active_workspace_generation = workspace_generation
            active_checkpoint_sha256 = initial_checkpoint_by_generation.get(
                workspace_generation
            )
            if active_checkpoint_sha256 is None:
                raise PublishError(f"{case}: proof round has no generation checkpoint")
        if (
            record.get("diagnosticCheckerRequestPath") is not None
            or record.get("diagnosticCheckerRequestError") is not None
            or record.get("diagnosticCheckerTelemetryError") is not None
        ):
            raise PublishError(
                f"{case}: legacy diagnostic request-file state is not permitted"
            )
        closure_path = resolve_case_artifact(
            source_dir,
            record.get("authorityClosurePath"),
            f"{case}.proofAgentRounds[{round_index - 1}].authorityClosurePath",
        )
        selected_paths.add(closure_path)
        selected_paths.update(
            validate_context_snapshot(
                case,
                closure_path.parent,
                record.get("contextManifestSha256"),
                verification_mode,
                f"proof round {round_index}",
            )
        )
        closure_sha256 = record.get("authorityClosureSha256")
        closure_bytes = record.get("authorityClosureBytes")
        if (
            closure_sha256 != sha256(closure_path)
            or nonnegative_integer(
                closure_bytes,
                f"{case}.proofAgentRounds[{round_index - 1}].authorityClosureBytes",
            )
            != closure_path.stat().st_size
        ):
            raise PublishError(f"{case}: authority-closure evidence drifted")

        round_invocations = record.get("diagnosticCheckerInvocations", [])
        if (
            not isinstance(round_invocations, list)
            or any(not isinstance(invocation, dict) for invocation in round_invocations)
        ):
            raise PublishError(f"{case}: diagnostic checker evidence is malformed")
        telemetry_value = record.get("diagnosticCheckerTelemetryPath")
        telemetry_path: Path | None = None
        if round_invocations:
            telemetry_path = resolve_case_artifact(
                source_dir,
                telemetry_value,
                f"{case}.proofAgentRounds[{round_index - 1}].diagnosticTelemetry",
            )
            if load_json_array(telemetry_path, f"{case} diagnostic telemetry") != (
                round_invocations
            ):
                raise PublishError(f"{case}: host telemetry differs from the report")
            selected_paths.add(telemetry_path)
        elif telemetry_value is not None:
            raise PublishError(f"{case}: empty diagnostic round records telemetry")

        round_location = f"{case}.proofAgentRounds[{round_index - 1}]"
        requests_seen = nonnegative_integer(
            record.get("diagnosticRequestsSeen"),
            f"{round_location}.diagnosticRequestsSeen",
        )
        timeout_seconds_reserved = nonnegative_integer(
            record.get("diagnosticRequestedTimeoutSecondsReserved"),
            f"{round_location}.diagnosticRequestedTimeoutSecondsReserved",
        )
        accepted_count = nonnegative_integer(
            record.get("diagnosticAcceptedCount"),
            f"{round_location}.diagnosticAcceptedCount",
        )
        rejected_source_audit_count = nonnegative_integer(
            record.get("diagnosticRejectedSourceAuditCount"),
            f"{round_location}.diagnosticRejectedSourceAuditCount",
        )
        other_rejected_count = nonnegative_integer(
            record.get("diagnosticOtherRejectedRequestCount"),
            f"{round_location}.diagnosticOtherRejectedRequestCount",
        )
        accepted_source_audits = record.get("diagnosticAcceptedSourceAudits", [])
        rejected_source_audits = record.get("diagnosticRejectedSourceAudits", [])
        if (
            not isinstance(accepted_source_audits, list)
            or any(not isinstance(value, dict) for value in accepted_source_audits)
            or not isinstance(rejected_source_audits, list)
            or any(not isinstance(value, dict) for value in rejected_source_audits)
        ):
            raise PublishError(f"{case}: diagnostic source-audit records are malformed")
        if accepted_count != len(round_invocations) or accepted_count != len(
            accepted_source_audits
        ):
            raise PublishError(
                f"{case}: accepted diagnostic request evidence does not reconcile"
            )
        if rejected_source_audit_count != len(rejected_source_audits):
            raise PublishError(
                f"{case}: rejected diagnostic source-audit evidence does not reconcile"
            )
        classified_count = accepted_count + rejected_source_audit_count
        if (
            classified_count > requests_seen
            or other_rejected_count != requests_seen - classified_count
        ):
            raise PublishError(
                f"{case}: diagnostic broker request totals do not reconcile"
            )

        broker_metrics["diagnosticRequestCount"] += requests_seen
        broker_metrics["diagnosticRequestedTimeoutSecondsReserved"] += (
            timeout_seconds_reserved
        )
        broker_metrics["diagnosticAcceptedRequestCount"] += accepted_count
        broker_metrics["diagnosticRejectedSourceAuditCount"] += (
            rejected_source_audit_count
        )
        broker_metrics["diagnosticOtherRejectedRequestCount"] += other_rejected_count
        broker_metrics["diagnosticAcceptedAuditArtifactCount"] += accepted_count
        broker_metrics["diagnosticRejectedSourceAuditArtifactCount"] += (
            4 * rejected_source_audit_count
        )
        broker_metrics["diagnosticPreservedArtifactCount"] += (
            accepted_count + 4 * rejected_source_audit_count
        )

        classified_requested_total = 0
        request_ordinals: set[int] = set()
        previous_accepted_request_ordinal = 0
        latest_passed_sha256: str | None = None
        for sequence, invocation in enumerate(round_invocations, start=1):
            accepted = accepted_source_audits[sequence - 1]
            required_invocation_keys = {
                "sequence",
                "mode",
                "candidateSha256",
                "candidatePath",
                "purpose",
                "compilePassed",
                "problemCompilePassed",
                "compileCheckpointAdvanced",
                "stdoutSha256",
                "stderrSha256",
                "requestedTimeoutSeconds",
                "effectiveTimeoutSeconds",
                "startedAtUnixMs",
                "elapsedMs",
                "exitCode",
                "timedOut",
            }
            if set(invocation) not in (
                required_invocation_keys,
                required_invocation_keys | {"error"},
            ):
                raise PublishError(
                    f"{case}: diagnostic invocation schema is not strict"
                )
            candidate_sha256 = invocation.get("candidateSha256")
            mode = invocation.get("mode")
            candidate_path_value = invocation.get("candidatePath")
            purpose = invocation.get("purpose")
            validate_diagnostic_identity(
                mode,
                candidate_path_value,
                purpose,
                candidate_sha256,
                f"{case}.diagnosticCheckerInvocations[{sequence - 1}]",
            )
            validate_diagnostic_checkpoint_dedup(
                mode,
                candidate_sha256,
                latest_passed_sha256 or active_checkpoint_sha256,
                f"{case}.diagnosticCheckerInvocations[{sequence - 1}]",
            )
            if invocation.get("sequence") != sequence:
                raise PublishError(f"{case}: diagnostic identity is malformed")
            requested = nonnegative_integer(
                invocation.get("requestedTimeoutSeconds"),
                f"{case}.diagnostic.requestedTimeoutSeconds",
            )
            effective = nonnegative_integer(
                invocation.get("effectiveTimeoutSeconds"),
                f"{case}.diagnostic.effectiveTimeoutSeconds",
            )
            if not (1 <= effective <= requested):
                raise PublishError(f"{case}: diagnostic timeout escaped safe bounds")
            accepted_request_ordinal = nonnegative_integer(
                accepted.get("requestOrdinal"),
                f"{round_location}.diagnosticAcceptedSourceAudits[{sequence - 1}]"
                ".requestOrdinal",
            )
            if (
                set(accepted)
                != {
                    "requestOrdinal",
                    "sequence",
                    "mode",
                    "candidatePath",
                    "purpose",
                    "candidateSha256",
                    "requestedTimeoutSeconds",
                    "candidate",
                    "audit",
                }
                or accepted.get("sequence") != sequence
                or accepted.get("mode") != mode
                or accepted.get("candidatePath") != candidate_path_value
                or accepted.get("purpose") != purpose
                or accepted.get("candidateSha256") != candidate_sha256
                or accepted.get("requestedTimeoutSeconds") != requested
                or accepted_request_ordinal <= previous_accepted_request_ordinal
                or accepted_request_ordinal > requests_seen
                or accepted_request_ordinal in request_ordinals
            ):
                raise PublishError(
                    f"{case}: accepted diagnostic source-audit identity drifted"
                )
            previous_accepted_request_ordinal = accepted_request_ordinal
            request_ordinals.add(accepted_request_ordinal)
            accepted_audit_relative = (
                f"proof-stage/proof-agent/rounds/{round_index:02}/"
                f"interactive-diagnostics/{sequence:02}/audit.json"
            )
            checked_candidate_relative = (
                candidate_path_value if mode == "module" else "Problem.v"
            )
            accepted_candidate_relative = (
                f"proof-stage/proof-agent/rounds/{round_index:02}/"
                f"interactive-diagnostics/{sequence:02}/checked-workspace/"
                f"{checked_candidate_relative}"
            )
            accepted_candidate_path, accepted_candidate_binding = (
                validate_diagnostic_artifact_binding(
                    case,
                    source_dir,
                    accepted.get("candidate"),
                    accepted_candidate_relative,
                    f"{round_location}.diagnosticAcceptedSourceAudits"
                    f"[{sequence - 1}].candidate",
                )
            )
            accepted_audit_path, accepted_audit_binding = (
                validate_diagnostic_artifact_binding(
                    case,
                    source_dir,
                    accepted.get("audit"),
                    accepted_audit_relative,
                    f"{round_location}.diagnosticAcceptedSourceAudits"
                    f"[{sequence - 1}].audit",
                )
            )
            if sha256(accepted_candidate_path) != candidate_sha256:
                raise PublishError(
                    f"{case}: accepted diagnostic candidate identity drifted"
                )
            validate_diagnostic_source_audit(
                accepted_audit_path,
                f"{round_location}.diagnosticAcceptedSourceAudits"
                f"[{sequence - 1}].audit",
                expected_passed=True,
            )
            selected_paths.add(accepted_candidate_path)
            selected_paths.add(accepted_audit_path)
            accepted_source_audit_evidence.append(
                {
                    "round": round_index,
                    "requestOrdinal": accepted_request_ordinal,
                    "sequence": sequence,
                    "mode": mode,
                    "candidatePath": candidate_path_value,
                    "purpose": purpose,
                    "candidateSha256": candidate_sha256,
                    "requestedTimeoutSeconds": requested,
                    "candidate": accepted_candidate_binding,
                    "audit": accepted_audit_binding,
                }
            )
            classified_requested_total += requested
            assert telemetry_path is not None
            diagnostic_root = (
                telemetry_path.parent / "interactive-diagnostics" / f"{sequence:02d}"
            )
            request_path = diagnostic_root / "request.json"
            invocation_path = diagnostic_root / "invocation.json"
            stdout_path = diagnostic_root / "stdout.txt"
            stderr_path = diagnostic_root / "stderr.txt"
            checked_root = diagnostic_root / "checked-workspace"
            checked_candidate_path = checked_root / checked_candidate_relative
            required_checked_paths = [
                checked_root / name
                for name in ("Schema.v", "Queries.v", "Witness.v", "Goal.v")
            ]
            if mode == "module":
                required_checked_paths.append(checked_root / "Problem.v")
            required_checked_paths.append(checked_candidate_path)
            for path in (
                request_path,
                invocation_path,
                stdout_path,
                stderr_path,
                *required_checked_paths,
            ):
                if not path.is_file() or path.is_symlink():
                    raise PublishError(
                        f"{case}: interactive diagnostic evidence is missing"
                    )
                try:
                    path.resolve().relative_to(source_dir.resolve())
                except ValueError as error:
                    raise PublishError(
                        f"{case}: interactive diagnostic evidence escapes its case"
                    ) from error
                selected_paths.add(path.resolve())
            validate_diagnostic_request_v2(
                load_json(request_path),
                mode=mode,
                candidate_path=candidate_path_value,
                purpose=purpose,
                candidate_sha256=candidate_sha256,
                candidate_bytes=checked_candidate_path.stat().st_size,
                requested_timeout_seconds=requested,
                location=f"{case}.diagnostic.request",
            )
            if (
                load_json(invocation_path) != invocation
                or sha256(checked_candidate_path) != candidate_sha256
                or invocation.get("stdoutSha256") != sha256(stdout_path)
                or invocation.get("stderrSha256") != sha256(stderr_path)
            ):
                raise PublishError(f"{case}: interactive diagnostic evidence drifted")
            started = nonnegative_integer(
                invocation.get("startedAtUnixMs"), f"{case}.diagnostic.startedAtUnixMs"
            )
            elapsed = nonnegative_integer(
                invocation.get("elapsedMs"), f"{case}.diagnostic.elapsedMs"
            )
            elapsed_warning = diagnostic_elapsed_warning(
                round_number=round_index,
                sequence=sequence,
                requested_timeout_seconds=requested,
                effective_timeout_seconds=effective,
                elapsed_ms=elapsed,
            )
            if elapsed_warning is not None:
                diagnostic_elapsed_warnings.append(elapsed_warning)
            clock_warning = diagnostic_clock_warning(
                round_number=round_index,
                sequence=sequence,
                prior_estimated_end_unix_ms=previous_diagnostic_end,
                started_at_unix_ms=started,
            )
            if clock_warning is not None:
                diagnostic_clock_warnings.append(clock_warning)
            previous_diagnostic_end = started + elapsed
            timed_out = invocation.get("timedOut")
            exit_code = invocation.get("exitCode")
            error = invocation.get("error")
            compile_passed = invocation.get("compilePassed")
            problem_compile_passed = invocation.get("problemCompilePassed")
            checkpoint_advanced = invocation.get("compileCheckpointAdvanced")
            if (
                not isinstance(timed_out, bool)
                or not isinstance(compile_passed, bool)
                or not isinstance(problem_compile_passed, bool)
                or not isinstance(checkpoint_advanced, bool)
            ):
                raise PublishError(f"{case}: diagnostic status is malformed")
            if error is not None and (not isinstance(error, str) or not error):
                raise PublishError(f"{case}: diagnostic error is malformed")
            if exit_code is not None and (
                isinstance(exit_code, bool) or not isinstance(exit_code, int)
            ):
                raise PublishError(f"{case}: diagnostic exit code is malformed")
            if timed_out and exit_code not in (124, 137) and not error:
                raise PublishError(
                    f"{case}: timed-out diagnostic has no failure evidence"
                )
            durable_module_path = closure_path.parent / str(candidate_path_value)
            trusted_cache_module_path = (
                trusted_cache_roots_by_generation[workspace_generation]
                / str(candidate_path_value)
            )
            expected_compile_passed, late_module_publication = (
                expected_diagnostic_compile_passed(
                    mode=mode,
                    exit_code=exit_code,
                    timed_out=timed_out,
                    error=error,
                    reported_compile_passed=compile_passed,
                    durable_module_path=durable_module_path,
                    trusted_cache_module_path=trusted_cache_module_path,
                    candidate_sha256=candidate_sha256,
                )
            )
            if late_module_publication:
                selected_paths.add(durable_module_path.resolve())
            expected_problem_compile_passed = (
                expected_compile_passed and mode == "problem"
            )
            if (
                compile_passed is not expected_compile_passed
                or problem_compile_passed is not expected_problem_compile_passed
                or checkpoint_advanced is not expected_problem_compile_passed
            ):
                raise PublishError(f"{case}: compile checkpoint status is incoherent")
            if problem_compile_passed:
                latest_passed_sha256 = candidate_sha256
            invocations.append(invocation)

        previous_rejected_request_ordinal = 0
        for rejected_index, rejected in enumerate(rejected_source_audits):
            rejected_location = (
                f"{round_location}.diagnosticRejectedSourceAudits[{rejected_index}]"
            )
            rejected_request_ordinal = nonnegative_integer(
                rejected.get("requestOrdinal"), f"{rejected_location}.requestOrdinal"
            )
            rejected_candidate_sha256 = rejected.get("candidateSha256")
            rejected_requested_timeout = nonnegative_integer(
                rejected.get("requestedTimeoutSeconds"),
                f"{rejected_location}.requestedTimeoutSeconds",
            )
            rejected_mode = rejected.get("mode")
            rejected_candidate_path = rejected.get("candidatePath")
            rejected_purpose = rejected.get("purpose")
            validate_diagnostic_identity(
                rejected_mode,
                rejected_candidate_path,
                rejected_purpose,
                rejected_candidate_sha256,
                rejected_location,
            )
            if (
                set(rejected)
                != {
                    "requestOrdinal",
                    "mode",
                    "candidatePath",
                    "purpose",
                    "candidateSha256",
                    "requestedTimeoutSeconds",
                    "problem",
                    "request",
                    "audit",
                    "feedback",
                }
                or rejected_request_ordinal <= previous_rejected_request_ordinal
                or rejected_request_ordinal > requests_seen
                or rejected_request_ordinal in request_ordinals
                or not valid_sha256(rejected_candidate_sha256)
                or rejected_candidate_sha256
                in {
                    invocation.get("candidateSha256")
                    for invocation in round_invocations
                }
                or rejected_requested_timeout < 1
            ):
                raise PublishError(
                    f"{case}: rejected diagnostic source-audit identity drifted"
                )
            previous_rejected_request_ordinal = rejected_request_ordinal
            request_ordinals.add(rejected_request_ordinal)
            rejected_root = (
                f"proof-stage/proof-agent/rounds/{round_index:02}/"
                "rejected-diagnostic-source-audits/"
                f"{rejected_request_ordinal:02}"
            )
            rejected_bindings: dict[str, dict[str, Any]] = {}
            rejected_paths: dict[str, Path] = {}
            for field, filename in (
                ("problem", "Problem.v"),
                ("request", "request.json"),
                ("audit", "audit.json"),
                ("feedback", "feedback.txt"),
            ):
                rejected_path, rejected_binding = validate_diagnostic_artifact_binding(
                    case,
                    source_dir,
                    rejected.get(field),
                    f"{rejected_root}/{filename}",
                    f"{rejected_location}.{field}",
                )
                rejected_paths[field] = rejected_path
                rejected_bindings[field] = rejected_binding
                selected_paths.add(rejected_path)
            if sha256(rejected_paths["problem"]) != rejected_candidate_sha256:
                raise PublishError(f"{case}: rejected diagnostic Problem.v drifted")
            rejected_request = load_json(rejected_paths["request"])
            validate_diagnostic_request_v2(
                rejected_request,
                mode=rejected_mode,
                candidate_path=rejected_candidate_path,
                purpose=rejected_purpose,
                candidate_sha256=rejected_candidate_sha256,
                candidate_bytes=rejected_paths["problem"].stat().st_size,
                requested_timeout_seconds=rejected_requested_timeout,
                location=f"{rejected_location}.request",
            )
            validate_diagnostic_source_audit(
                rejected_paths["audit"],
                f"{rejected_location}.audit",
                expected_passed=False,
            )
            try:
                rejected_feedback = rejected_paths["feedback"].read_text(
                    encoding="utf-8"
                )
            except (OSError, UnicodeError) as error:
                raise PublishError(
                    f"{case}: cannot read rejected diagnostic feedback: {error}"
                ) from error
            if (
                rejected_candidate_sha256 not in rejected_feedback
                or "checker was not executed" not in rejected_feedback
            ):
                raise PublishError(f"{case}: rejected diagnostic feedback drifted")
            classified_requested_total += rejected_requested_timeout
            rejected_source_audit_evidence.append(
                {
                    "round": round_index,
                    "requestOrdinal": rejected_request_ordinal,
                    "mode": rejected_mode,
                    "candidatePath": rejected_candidate_path,
                    "purpose": rejected_purpose,
                    "candidateSha256": rejected_candidate_sha256,
                    "requestedTimeoutSeconds": rejected_requested_timeout,
                    **rejected_bindings,
                }
            )
        if classified_requested_total > timeout_seconds_reserved:
            raise PublishError(
                f"{case}: classified diagnostic timeout exceeds reserved timeout"
            )

        candidate_path = closure_path.parent / "Problem.v"
        if not candidate_path.is_file() or candidate_path.is_symlink():
            raise PublishError(f"{case}: round candidate Problem.v snapshot is missing")
        selected_paths.add(candidate_path.resolve())
        candidate_sha256 = sha256(candidate_path)
        candidate_passed = candidate_problem_has_compile_authority(
            candidate_sha256,
            active_checkpoint_sha256,
            round_invocations,
        )
        candidate_has_theorem = problem_declares_final_theorem(
            candidate_path.read_text(encoding="utf-8"),
            verification_mode,
        )
        if (
            record.get("candidateProblemSha256") != candidate_sha256
            or record.get("candidateProblemCompilePassed") is not candidate_passed
            or record.get("candidateHasFinalTheorem") is not candidate_has_theorem
            or record.get("activeProblemCompileCheckpointSha256")
            != active_checkpoint_sha256
            or record.get("updatedProblemCompileCheckpointSha256")
            != latest_passed_sha256
            or record.get("compileCheckpointRestored")
            is not (record.get("checkpointTransition") == "restoredExisting")
        ):
            raise PublishError(f"{case}: compile-checkpoint chain is incoherent")
        if latest_passed_sha256 is not None:
            active_checkpoint_sha256 = latest_passed_sha256

    files: list[dict[str, Any]] = []
    for path in sorted(selected_paths):
        if not path.is_file() or path.is_symlink():
            raise PublishError(f"{case}: selected proof-agent evidence drifted")
        try:
            evidence_relative = path.relative_to(evidence_root)
            source_relative = Path("proof-stage/proof-agent") / evidence_relative
            canonical_relative = Path("proof-agent-evidence") / evidence_relative
        except ValueError:
            formal_root = source_dir / "proof-stage/formal-sql"
            try:
                formal_relative = path.relative_to(formal_root)
            except ValueError as error:
                raise PublishError(
                    f"{case}: selected proof-agent evidence escapes known roots"
                ) from error
            source_relative = Path("proof-stage/formal-sql") / formal_relative
            canonical_relative = (
                Path("proof-agent-evidence/final-workspace") / formal_relative
            )
        files.append(
            {
                "sourceRelativePath": source_relative.as_posix(),
                "canonicalRelativePath": canonical_relative.as_posix(),
                "sha256": sha256(path),
                "bytes": path.stat().st_size,
            }
        )
    if not files:
        raise PublishError(f"{case}: proof-agent evidence root is empty")
    return {
        "schemaVersion": 3,
        "artifactKind": "logos-proof-agent-broker-evidence",
        "caseId": case,
        "sourceFullRunSummarySha256": source_full_run_summary_sha256,
        "diagnosticTransport": PROOF_AGENT_DIAGNOSTIC_TRANSPORT,
        "diagnosticCachePolicy": PROOF_AGENT_DIAGNOSTIC_CACHE_POLICY,
        "diagnosticCacheManifestSourceRelativePath": (
            cache_manifest_path.relative_to(source_dir).as_posix()
        ),
        "diagnosticCacheManifestCanonicalRelativePath": (
            Path("proof-agent-evidence")
            / cache_manifest_path.relative_to(evidence_root)
        ).as_posix(),
        "diagnosticCacheManifestSha256": cache_manifest_sha256,
        "diagnosticCacheEntries": cache_entries,
        "workspaceGenerationCaches": sorted(
            workspace_generation_cache_evidence,
            key=lambda value: value["workspaceGeneration"],
        ),
        "compileCheckpointPolicy": PROOF_AGENT_COMPILE_CHECKPOINT_POLICY,
        "initialProblemCheckpointSha256": initial_sha256,
        "initialProblemCompileElapsedMs": initial_elapsed,
        "initialProblemCompileInvocationCount": len(initial_elapsed_by_generation),
        "initialProblemCompileGenerations": [
            {
                "workspaceGeneration": generation,
                "path": initial_checkpoint_path_by_generation[generation],
                "sha256": initial_checkpoint_by_generation[generation],
                "elapsedMs": initial_elapsed_by_generation[generation],
            }
            for generation in sorted(initial_elapsed_by_generation)
        ],
        "initialProblemCompileElapsedWarnings": initial_elapsed_warnings,
        "trustedEnvironmentPreflightInvocationCount": len(
            preflight_elapsed_by_generation
        ),
        "trustedEnvironmentPreflightElapsedMs": sum(
            preflight_elapsed_by_generation.values()
        ),
        "preflightGenerations": [
            {
                "workspaceGeneration": generation,
                "elapsedMs": preflight_elapsed_by_generation[generation],
            }
            for generation in sorted(preflight_elapsed_by_generation)
        ],
        "trustedEnvironmentPreflightElapsedWarnings": preflight_elapsed_warnings,
        "trustedElapsedWarnings": trusted_elapsed_warnings,
        "workspaceGenerations": [
            {
                "workspaceGeneration": generation,
                "initialProblemCheckpointPath": initial_checkpoint_path_by_generation[
                    generation
                ],
                "initialProblemCheckpointSha256": initial_checkpoint_by_generation[
                    generation
                ],
                "initialProblemCompileElapsedMs": initial_elapsed_by_generation[
                    generation
                ],
                "trustedEnvironmentPreflightElapsedMs": preflight_elapsed_by_generation[
                    generation
                ],
            }
            for generation in sorted(initial_checkpoint_by_generation)
        ],
        "diagnosticInvocationCount": len(invocations),
        "diagnosticElapsedWarnings": diagnostic_elapsed_warnings,
        "diagnosticClockWarnings": diagnostic_clock_warnings,
        **broker_metrics,
        "diagnosticAcceptedSourceAudits": accepted_source_audit_evidence,
        "diagnosticRejectedSourceAudits": rejected_source_audit_evidence,
        "fileCount": len(files),
        "files": files,
    }


def validate_proof_agent_session_sequence(
    rounds: list[dict[str, Any]],
    transitions: list[dict[str, Any]],
    context: str,
    *,
    allow_terminal_unavailable_session: bool = False,
) -> None:
    generation_sessions: dict[int, str] = {}
    generation_rounds: dict[int, list[dict[str, Any]]] = {}
    seen_sessions: set[str] = set()
    fixed_restart_rounds = {
        transition["afterRound"] + 1: transition for transition in transitions
    }
    previous_generation: int | None = None
    for index, record in enumerate(rounds, start=1):
        generation = nonnegative_integer(
            record.get("sessionGeneration"),
            f"{context}.proofAgentRounds[{index - 1}].sessionGeneration",
        )
        restarted = record.get("sessionRestarted")
        restart_reason = record.get("sessionRestartReason")
        checkpoint_transition = record.get("checkpointTransition")
        if index == 1:
            coherent = (
                generation == 1
                and restarted is False
                and restart_reason is None
                and checkpoint_transition == "newWorkspaceInitial"
            )
        elif index in fixed_restart_rounds:
            transition = fixed_restart_rounds[index]
            coherent = (
                previous_generation is not None
                and generation == previous_generation + 1
                and restarted is True
                and restart_reason == "fixedWitnessReplacement"
                and checkpoint_transition == "newWorkspaceInitial"
                and record.get("workspaceGeneration")
                == transition["toWorkspaceGeneration"]
            )
        elif generation == previous_generation:
            coherent = (
                restarted is False
                and restart_reason is None
                and checkpoint_transition == "continued"
            )
        else:
            previous_records = generation_rounds.get(previous_generation or 0, [])
            coherent = (
                previous_generation is not None
                and generation == previous_generation + 1
                and restarted is True
                and restart_reason == "failedRoundLimit"
                and checkpoint_transition == "restoredExisting"
                and len(previous_records)
                == PROOF_AGENT_SESSION_RESTART_AFTER_FAILED_ROUNDS
                and all(previous.get("success") is False for previous in previous_records)
                and record.get("workspaceGeneration")
                == rounds[index - 2].get("workspaceGeneration")
                and record.get("contextManifestSha256")
                == rounds[index - 2].get("contextManifestSha256")
            )
        if not coherent:
            raise PublishError(
                f"{context}: proof-agent session transition drifted at round {index}"
            )
        session_id = record.get("sessionId")
        if (
            allow_terminal_unavailable_session
            and index == len(rounds)
            and runner_validators()["terminal_round_has_unavailable_session"](
                record
            )
        ):
            generation_rounds.setdefault(generation, []).append(record)
            previous_generation = generation
            continue
        if not isinstance(session_id, str) or not session_id.strip():
            raise PublishError(f"{context}: proof-agent round {index} has no sessionId")
        active = generation_sessions.get(generation)
        if active is None:
            if session_id in seen_sessions:
                raise PublishError(
                    f"{context}: proof-agent session was reused after restart"
                )
            generation_sessions[generation] = session_id
            seen_sessions.add(session_id)
        elif active != session_id:
            raise PublishError(
                f"{context}: proof-agent session changed inside generation {generation}"
            )
        generation_rounds.setdefault(generation, []).append(record)
        previous_generation = generation


def validate_proof_metrics(
    case: str,
    row: dict[str, Any],
    source_dir: Path,
    run_root: Path,
    report: dict[str, Any] | None,
    source_full_run_summary_sha256: str,
    *,
    legacy_catalog: bool,
) -> dict[str, Any] | None:
    metrics = row.get("proofMetrics")
    expected_keys = {
        "proofRoundCount",
        "preflightInvocationCount",
        "preflightElapsedMs",
        "preflightGenerations",
        "diagnosticInvocationCount",
        "diagnosticElapsedMs",
        "requestedTimeoutSeconds",
        "effectiveTimeoutSeconds",
        "initialProblemCompileElapsedMs",
        "initialProblemCompileTimeoutSeconds",
        "initialProblemCompileInvocationCount",
        "initialProblemCompileGenerations",
        "finalProofCheckInvocationCount",
        "finalProofCheckElapsedTotalMs",
        "checkerInvocationCount",
        "checkerElapsedMs",
        "finalProofCheckElapsedMs",
        "proofSource",
        "staticPromptAndPrimerBytes",
        "queryShapeBytes",
        "generatedContextBytes",
        "contextManifestBytes",
        *PROOF_AGENT_BROKER_METRIC_KEYS,
    }
    if legacy_catalog:
        expected_keys.add("catalogBytes")
    optional_keys = {
        "diagnosticElapsedWarnings",
        "diagnosticClockWarnings",
        "trustedElapsedWarnings",
    }
    if (
        not isinstance(metrics, dict)
        or not expected_keys.issubset(metrics)
        or not set(metrics).issubset(expected_keys | optional_keys)
    ):
        raise PublishError(f"{case}: proofMetrics is incomplete or noncanonical")
    reported_elapsed_warnings = validate_diagnostic_elapsed_warnings(
        metrics.get("diagnosticElapsedWarnings", []),
        f"{case}: proofMetrics.diagnosticElapsedWarnings",
    )
    reported_clock_warnings = validate_diagnostic_clock_warnings(
        metrics.get("diagnosticClockWarnings", []),
        f"{case}: proofMetrics.diagnosticClockWarnings",
    )
    reported_trusted_elapsed_warnings = validate_trusted_elapsed_warnings(
        metrics.get("trustedElapsedWarnings", []),
        f"{case}: proofMetrics.trustedElapsedWarnings",
    )
    round_count = nonnegative_integer(
        metrics.get("proofRoundCount"), f"{case}.proofMetrics.proofRoundCount"
    )
    invocation_count = nonnegative_integer(
        metrics.get("diagnosticInvocationCount"),
        f"{case}.proofMetrics.diagnosticInvocationCount",
    )
    diagnostic_elapsed = nonnegative_integer(
        metrics.get("diagnosticElapsedMs"),
        f"{case}.proofMetrics.diagnosticElapsedMs",
    )
    preflight_invocation_count = nonnegative_integer(
        metrics.get("preflightInvocationCount"),
        f"{case}.proofMetrics.preflightInvocationCount",
    )
    preflight_elapsed = metrics.get("preflightElapsedMs")
    if preflight_invocation_count == 0:
        if preflight_elapsed is not None:
            raise PublishError(
                f"{case}: preflight elapsed exists without an invocation"
            )
    else:
        preflight_elapsed = nonnegative_integer(
            preflight_elapsed, f"{case}.proofMetrics.preflightElapsedMs"
        )
    preflight_generations = metrics.get("preflightGenerations")
    initial_compile_invocation_count = nonnegative_integer(
        metrics.get("initialProblemCompileInvocationCount"),
        f"{case}.proofMetrics.initialProblemCompileInvocationCount",
    )
    initial_compile_generations = metrics.get("initialProblemCompileGenerations")
    if not isinstance(preflight_generations, list) or not isinstance(
        initial_compile_generations, list
    ):
        raise PublishError(f"{case}: workspace-generation checker metrics are malformed")
    final_invocation_count = nonnegative_integer(
        metrics.get("finalProofCheckInvocationCount"),
        f"{case}.proofMetrics.finalProofCheckInvocationCount",
    )
    final_elapsed_total = nonnegative_integer(
        metrics.get("finalProofCheckElapsedTotalMs"),
        f"{case}.proofMetrics.finalProofCheckElapsedTotalMs",
    )
    checker_invocation_count = nonnegative_integer(
        metrics.get("checkerInvocationCount"),
        f"{case}.proofMetrics.checkerInvocationCount",
    )
    checker_elapsed = nonnegative_integer(
        metrics.get("checkerElapsedMs"), f"{case}.proofMetrics.checkerElapsedMs"
    )
    reported_broker_metrics = {
        key: nonnegative_integer(metrics.get(key), f"{case}.proofMetrics.{key}")
        for key in PROOF_AGENT_BROKER_METRIC_KEYS
    }
    requested = metrics.get("requestedTimeoutSeconds")
    effective = metrics.get("effectiveTimeoutSeconds")
    if (
        not isinstance(requested, list)
        or not isinstance(effective, list)
        or len(requested) != invocation_count
        or len(effective) != invocation_count
    ):
        raise PublishError(f"{case}: diagnostic timeout arrays/counts are incoherent")
    for index, (requested_value, effective_value) in enumerate(
        zip(requested, effective, strict=True)
    ):
        requested_seconds = nonnegative_integer(
            requested_value,
            f"{case}.proofMetrics.requestedTimeoutSeconds[{index}]",
        )
        effective_seconds = nonnegative_integer(
            effective_value,
            f"{case}.proofMetrics.effectiveTimeoutSeconds[{index}]",
        )
        if not (1 <= effective_seconds <= requested_seconds):
            raise PublishError(
                f"{case}: diagnostic checker timeout escaped safe bounds"
            )

    final_elapsed = metrics.get("finalProofCheckElapsedMs")
    if row.get("outcome") == "outcome_unconditional":
        nonnegative_integer(
            final_elapsed, f"{case}.proofMetrics.finalProofCheckElapsedMs"
        )
    elif final_elapsed is not None:
        nonnegative_integer(
            final_elapsed, f"{case}.proofMetrics.finalProofCheckElapsedMs"
        )

    proof_source = metrics.get("proofSource")
    if not isinstance(proof_source, dict) or set(proof_source) != {
        "path",
        "present",
        "sha256",
        "bytes",
    }:
        raise PublishError(f"{case}: proofMetrics.proofSource is malformed")
    if proof_source.get("present") is True:
        proof_path, _ = validate_file_binding(
            proof_source,
            path_key="path",
            digest_key="sha256",
            location=f"{case}.proofMetrics.proofSource",
            run_root=run_root,
        )
        try:
            proof_path.relative_to(source_dir.resolve())
        except ValueError as error:
            raise PublishError(
                f"{case}: proof source escapes its case evidence"
            ) from error
        if proof_source.get("bytes") != proof_path.stat().st_size:
            raise PublishError(f"{case}: proof source byte count disagrees with file")
    elif proof_source.get("present") is False:
        expected_path = source_dir / "proof-stage/formal-sql/Problem.v"
        recorded = proof_source.get("path")
        if not isinstance(recorded, str) or not recorded:
            raise PublishError(f"{case}: absent proof source has no canonical path")
        candidate = Path(recorded).expanduser()
        candidates = (
            (candidate,)
            if candidate.is_absolute()
            else (
                WORKFLOW_ROOT / candidate,
                LOGOS_ROOT / candidate,
                run_root / candidate,
            )
        )
        if expected_path.resolve() not in {value.resolve() for value in candidates}:
            raise PublishError(f"{case}: absent proof source records the wrong path")
        if (
            proof_source.get("sha256") is not None
            or proof_source.get("bytes") is not None
            or expected_path.exists()
        ):
            raise PublishError(f"{case}: absent proof source carries invented metadata")
    else:
        raise PublishError(f"{case}: proofSource.present must be boolean")
    if (
        row.get("outcome") == "outcome_unconditional"
        and proof_source.get("present") is not True
    ):
        raise PublishError(f"{case}: certified result has no bound proof source")

    proof = report.get("proof") if isinstance(report, dict) else None
    rounds = proof.get("proofAgentRounds") if isinstance(proof, dict) else None
    rounds = rounds if isinstance(rounds, list) else []
    if any(not isinstance(round_record, dict) for round_record in rounds):
        raise PublishError(f"{case}: malformed proof-agent round")
    transitions = proof.get("proofWorkspaceTransitions", []) if isinstance(proof, dict) else []
    if not isinstance(transitions, list) or any(
        not isinstance(transition, dict) for transition in transitions
    ):
        raise PublishError(f"{case}: malformed proof workspace transitions")
    validate_proof_agent_session_sequence(
        rounds,
        transitions,
        case,
        allow_terminal_unavailable_session=(
            isinstance(proof, dict)
            and proof.get("deterministicTailRecovery") is not None
        ),
    )
    for index, round_record in enumerate(rounds, start=1):
        validate_legacy_catalog_marker(
            round_record,
            "catalogGuidance",
            legacy_catalog=legacy_catalog,
            location=f"{case}.proofAgentRounds[{index}]",
        )
    broker_evidence = collect_proof_agent_broker_evidence(
        case,
        source_dir,
        report,
        source_full_run_summary_sha256,
        legacy_catalog=legacy_catalog,
    )
    if broker_evidence is None:
        if (
            preflight_invocation_count != 0
            or preflight_elapsed is not None
            or preflight_generations != []
            or initial_compile_invocation_count != 0
            or initial_compile_generations != []
            or metrics.get("initialProblemCompileElapsedMs") is not None
            or metrics.get("initialProblemCompileTimeoutSeconds") is not None
            or any(reported_broker_metrics.values())
        ):
            raise PublishError(
                f"{case}: initial compile metrics exist without broker evidence"
            )
    else:
        agent_configuration = (
            proof.get("proofAgentConfiguration") if isinstance(proof, dict) else None
        )
        preflight = (
            agent_configuration.get("trustedEnvironmentPreflight")
            if isinstance(agent_configuration, dict)
            else None
        )
        if (
            not isinstance(preflight, dict)
            or preflight.get("exitCode") != 0
            or preflight.get("timedOut") is not False
            or preflight.get("error") is not None
            or preflight_invocation_count
            != broker_evidence["trustedEnvironmentPreflightInvocationCount"]
            or preflight_elapsed
            != broker_evidence["trustedEnvironmentPreflightElapsedMs"]
            or preflight_generations != broker_evidence["preflightGenerations"]
            or initial_compile_invocation_count
            != broker_evidence["initialProblemCompileInvocationCount"]
            or initial_compile_generations
            != broker_evidence["initialProblemCompileGenerations"]
            or metrics.get("initialProblemCompileElapsedMs")
            != broker_evidence["initialProblemCompileElapsedMs"]
            or metrics.get("initialProblemCompileTimeoutSeconds")
            != TRUSTED_CHECK_TIMEOUT_SECONDS
            or invocation_count != broker_evidence["diagnosticInvocationCount"]
            or reported_broker_metrics
            != {key: broker_evidence[key] for key in PROOF_AGENT_BROKER_METRIC_KEYS}
        ):
            raise PublishError(f"{case}: broker/preflight metrics disagree with report")
    expected_elapsed_warnings = (
        broker_evidence["diagnosticElapsedWarnings"]
        if broker_evidence is not None
        else []
    )
    if reported_elapsed_warnings != expected_elapsed_warnings:
        raise PublishError(
            f"{case}: diagnostic elapsed warnings disagree with bound evidence"
        )
    expected_clock_warnings = (
        broker_evidence["diagnosticClockWarnings"]
        if broker_evidence is not None
        else []
    )
    if reported_clock_warnings != expected_clock_warnings:
        raise PublishError(
            f"{case}: diagnostic clock warnings disagree with bound evidence"
        )
    expected_trusted_elapsed_warnings = (
        list(broker_evidence["trustedElapsedWarnings"])
        if broker_evidence is not None
        else []
    )
    for index, round_record in enumerate(rounds, start=1):
        elapsed_value = round_record.get("proofCheckElapsedMs")
        if elapsed_value is None:
            if round_record.get("proofCheckTimeoutSeconds") is not None:
                raise PublishError(
                    f"{case}: final proof-check timeout exists without elapsed evidence"
                )
            continue
        proof_check_timeout = nonnegative_integer(
            round_record.get("proofCheckTimeoutSeconds"),
            f"{case}.proofAgentRounds[{index - 1}].proofCheckTimeoutSeconds",
        )
        if not (1 <= proof_check_timeout <= TRUSTED_CHECK_TIMEOUT_SECONDS):
            raise PublishError(f"{case}: final proof-check timeout escaped policy")
        warning = trusted_elapsed_warning(
            phase="final_trusted_check",
            timeout_seconds=proof_check_timeout,
            elapsed_ms=nonnegative_integer(
                elapsed_value,
                f"{case}.proofAgentRounds[{index - 1}].proofCheckElapsedMs",
            ),
            round_number=index,
        )
        if warning is not None:
            expected_trusted_elapsed_warnings.append(warning)
    recovery = proof.get("deterministicTailRecovery") if isinstance(proof, dict) else None
    trusted_recovery = recovery.get("trustedCheck") if isinstance(recovery, dict) else None
    if isinstance(trusted_recovery, dict):
        recovery_timeout = nonnegative_integer(
            trusted_recovery.get("timeoutSeconds"),
            f"{case}.deterministicTailRecovery.trustedCheck.timeoutSeconds",
        )
        if not (1 <= recovery_timeout <= TRUSTED_CHECK_TIMEOUT_SECONDS):
            raise PublishError(f"{case}: deterministic-tail timeout escaped policy")
        recovery_warning = trusted_elapsed_warning(
            phase="deterministic_tail_trusted_check",
            timeout_seconds=recovery_timeout,
            elapsed_ms=nonnegative_integer(
                trusted_recovery.get("elapsedMs"),
                f"{case}.deterministicTailRecovery.trustedCheck.elapsedMs",
            ),
            round_number=len(rounds),
        )
        if recovery_warning is not None:
            expected_trusted_elapsed_warnings.append(recovery_warning)
    if reported_trusted_elapsed_warnings != expected_trusted_elapsed_warnings:
        raise PublishError(
            f"{case}: trusted elapsed warnings disagree with bound evidence"
        )
    if round_count != len(rounds):
        raise PublishError(f"{case}: proof round metric disagrees with report")
    invocations: list[dict[str, Any]] = []
    for round_record in rounds:
        values = round_record.get("diagnosticCheckerInvocations", [])
        if not isinstance(values, list) or any(
            not isinstance(value, dict) for value in values
        ):
            raise PublishError(f"{case}: malformed diagnostic checker evidence")
        invocations.extend(values)
    if invocation_count != len(invocations):
        raise PublishError(
            f"{case}: diagnostic invocation metric disagrees with report"
        )
    if requested != [
        value.get("requestedTimeoutSeconds") for value in invocations
    ] or effective != [value.get("effectiveTimeoutSeconds") for value in invocations]:
        raise PublishError(f"{case}: diagnostic timeout metrics disagree with report")
    if diagnostic_elapsed != sum(
        nonnegative_integer(
            value.get("elapsedMs"), f"{case}.diagnosticCheckerInvocations.elapsedMs"
        )
        for value in invocations
    ):
        raise PublishError(f"{case}: diagnostic elapsed metric disagrees with report")

    final_attempt_elapsed = [
        nonnegative_integer(
            round_record.get("proofCheckElapsedMs"),
            f"{case}.proofAgentRounds.proofCheckElapsedMs",
        )
        for round_record in rounds
        if round_record.get("proofCheckElapsedMs") is not None
    ]
    if isinstance(trusted_recovery, dict):
        final_attempt_elapsed.append(
            nonnegative_integer(
                trusted_recovery.get("elapsedMs"),
                f"{case}.deterministicTailRecovery.trustedCheck.elapsedMs",
            )
        )
    if final_invocation_count != len(
        final_attempt_elapsed
    ) or final_elapsed_total != sum(final_attempt_elapsed):
        raise PublishError(f"{case}: final checker aggregate metrics disagree")
    initial_invocation_count = (
        broker_evidence["initialProblemCompileInvocationCount"]
        if broker_evidence is not None
        else 0
    )
    initial_elapsed = (
        broker_evidence["initialProblemCompileElapsedMs"]
        if broker_evidence is not None
        else 0
    )
    if (
        checker_invocation_count
        != preflight_invocation_count
        + initial_invocation_count
        + invocation_count
        + final_invocation_count
        or checker_elapsed
        != (preflight_elapsed or 0)
        + initial_elapsed
        + diagnostic_elapsed
        + final_elapsed_total
    ):
        raise PublishError(f"{case}: total checker metrics disagree with evidence")

    agent = proof.get("proofAgent") if isinstance(proof, dict) else None
    if isinstance(trusted_recovery, dict):
        observed_final_elapsed = trusted_recovery.get("elapsedMs")
    else:
        observed_final_elapsed = (
            agent.get("proofCheckElapsedMs")
            if isinstance(agent, dict)
            and agent.get("proofCheckExitCode") == 0
            and agent.get("proofCheckTimedOut") is False
            else None
        )
    if final_elapsed != observed_final_elapsed:
        raise PublishError(
            f"{case}: final checker elapsed metric disagrees with report"
        )
    agent_configuration = (
        proof.get("proofAgentConfiguration") if isinstance(proof, dict) else None
    )
    context = (
        agent_configuration.get("context")
        if isinstance(agent_configuration, dict)
        else None
    )
    context_fields = {
        "staticPromptAndPrimerBytes": (
            agent_configuration.get("staticPromptAndPrimerBytes")
            if isinstance(agent_configuration, dict)
            else None
        ),
        "queryShapeBytes": context.get("queryShapeBytes")
        if isinstance(context, dict)
        else None,
        "generatedContextBytes": (
            context.get("generatedContextBytes") if isinstance(context, dict) else None
        ),
        "contextManifestBytes": (
            context.get("manifestBytes") if isinstance(context, dict) else None
        ),
    }
    if legacy_catalog:
        context_fields["catalogBytes"] = (
            context.get("catalogBytes") if isinstance(context, dict) else None
        )
    if isinstance(context, dict):
        if not legacy_catalog and "catalogBytes" in context:
            raise PublishError(f"{case}: current proof context contains catalogBytes")
        for name, observed in context_fields.items():
            if metrics.get(name) != nonnegative_integer(
                observed, f"{case}.report.{name}"
            ):
                raise PublishError(f"{case}: {name} metric disagrees with report")
        if (
            legacy_catalog
            and row.get("outcome") == "outcome_unconditional"
            and metrics["catalogBytes"] <= 0
        ):
            raise PublishError(f"{case}: catalog-on certified proof exposes no catalog")
    elif any(metrics.get(name) is not None for name in context_fields):
        raise PublishError(f"{case}: context byte metrics exist without report context")
    return broker_evidence


def validate_case_evidence(
    summary: dict[str, Any],
    run_root: Path,
    bindings: dict[str, Any],
    source_full_run_summary_sha256: str,
) -> dict[str, dict[str, Any]]:
    legacy_catalog = bindings["legacyCatalogArtifacts"]
    expected_configuration = expected_case_configuration(
        summary, bindings, legacy_catalog=legacy_catalog
    )
    manifest = bindings["inputManifest"]["rows"]
    semantic_manifest = bindings["inputManifest"]["semanticRows"]
    broker_evidence_by_case: dict[str, dict[str, Any]] = {}
    for row in summary["results"]:
        case = row["caseId"]
        source_dir = run_root / "cases" / case
        runner_result_path = source_dir / "runner-result.json"
        if not runner_result_path.is_file() or runner_result_path.is_symlink():
            raise PublishError(f"{case}: runner-result.json is missing or symlinked")
        if load_json(runner_result_path) != row:
            raise PublishError(f"{case}: runner-result.json disagrees with summary row")
        if row.get("effectiveConfiguration") != expected_configuration:
            raise PublishError(f"{case}: effective per-case configuration drifted")
        input_dir = resolve_case_input_directory(row.get("inputDir"), case, run_root)
        input_files = row.get("inputFiles")
        semantic_row = semantic_manifest.get(case)
        if not isinstance(semantic_row, dict):
            raise PublishError(f"{case}: semantic input authority is missing")
        expected_input_names = {"schema", "source", "target", "metadata"}
        if semantic_row.get("semanticSidecarPath") is not None:
            expected_input_names.add("semanticSidecar")
        if not isinstance(input_files, dict) or set(input_files) != expected_input_names:
            raise PublishError(f"{case}: inputFiles is incomplete")
        input_digests: dict[str, str] = {}
        for name, filename, manifest_key in (
            ("schema", "schema.sql", "schemaSha256"),
            ("source", "sql1.sql", "sql1Sha256"),
            ("target", "sql2.sql", "sql2Sha256"),
        ):
            file_path, digest = validate_file_binding(
                input_files[name],
                path_key="path",
                digest_key="sha256",
                location=f"{case}.inputFiles.{name}",
                run_root=run_root,
                expected_path=input_dir / filename,
            )
            del file_path
            if digest != manifest[case][manifest_key]:
                raise PublishError(f"{case}: {name} input differs from frozen manifest")
            input_digests[name] = digest

        metadata_path, metadata_digest = validate_file_binding(
            input_files["metadata"],
            path_key="path",
            digest_key="sha256",
            location=f"{case}.inputFiles.metadata",
            run_root=run_root,
            expected_path=input_dir / "metadata.json",
        )
        metadata = load_json(metadata_path)
        if (
            metadata_digest != semantic_row.get("metadataSha256")
            or not isinstance(metadata, dict)
            or metadata.get("flatCaseId") != semantic_row.get("flatCaseId")
        ):
            raise PublishError(f"{case}: metadata differs from frozen semantic authority")
        input_digests["metadata"] = metadata_digest
        sidecar_declared = semantic_row.get("semanticSidecarPath")
        if sidecar_declared is not None:
            expected_sidecar = resolve_recorded_file(
                sidecar_declared,
                f"{case}.semanticAuthority.semanticSidecarPath",
                run_root,
            )
            _, sidecar_digest = validate_file_binding(
                input_files["semanticSidecar"],
                path_key="path",
                digest_key="sha256",
                location=f"{case}.inputFiles.semanticSidecar",
                run_root=run_root,
                expected_path=expected_sidecar,
            )
            if sidecar_digest != semantic_row.get("semanticSidecarSha256"):
                raise PublishError(
                    f"{case}: sidecar differs from frozen semantic authority"
                )
            input_digests["semanticSidecar"] = sidecar_digest

        evidence = row.get("reportEvidence")
        if not isinstance(evidence, dict) or set(evidence) != {
            "path",
            "present",
            "sha256",
        }:
            raise PublishError(f"{case}: reportEvidence is malformed")
        expected_report = source_dir / "report.json"
        if row.get("status") == "completed" and evidence.get("present") is not True:
            raise PublishError(f"{case}: completed result has no report evidence")
        if evidence.get("present") is False:
            if evidence.get("sha256") is not None or expected_report.exists():
                raise PublishError(f"{case}: absent report evidence is incoherent")
            validate_proof_metrics(
                case,
                row,
                source_dir,
                run_root,
                None,
                source_full_run_summary_sha256,
                legacy_catalog=legacy_catalog,
            )
            continue
        if evidence.get("present") is not True:
            raise PublishError(f"{case}: reportEvidence.present must be boolean")
        report_path, _ = validate_file_binding(
            evidence,
            path_key="path",
            digest_key="sha256",
            location=f"{case}.reportEvidence",
            run_root=run_root,
            expected_path=expected_report,
        )
        recorded_report_path = resolve_recorded_file(
            row.get("reportPath"), f"{case}.reportPath", run_root
        )
        if recorded_report_path != report_path:
            raise PublishError(f"{case}: reportPath and reportEvidence.path differ")
        report = load_json(report_path)
        validate_report_semantics(
            case,
            row,
            report,
            source_dir,
            input_digests,
            bindings,
            legacy_catalog=legacy_catalog,
        )
        broker_evidence = validate_proof_metrics(
            case,
            row,
            source_dir,
            run_root,
            report,
            source_full_run_summary_sha256,
            legacy_catalog=legacy_catalog,
        )
        if broker_evidence is not None:
            canonical = canonical_case(case)
            broker_evidence["caseId"] = canonical
            broker_evidence_by_case[canonical] = broker_evidence
    return broker_evidence_by_case


def validate_full_summary(path: Path) -> tuple[dict[str, Any], dict[str, Any]]:
    document = load_json(path / "runner-summary.json")
    cases = document.get("cases")
    results = document.get("results")
    configuration = document.get("configuration")
    source_digest = nested(
        document, "configuration", "frameworkSourceTree", "manifestSha256"
    )
    image = nested(document, "configuration", "proofAgent", "dockerImage")
    resource_policy = nested(document, "configuration", "proofAgent", "resourcePolicy")
    integrity = document.get("integrityVerification")
    image_id = image.get("imageId") if isinstance(image, dict) else None
    legacy_catalog = legacy_catalog_artifact_mode(document, configuration)
    validate_fixed_fields(
        nested(document, "configuration", "proofAgent"),
        proof_agent_diagnostic_configuration(legacy_catalog=legacy_catalog),
        "configuration.proofAgent",
    )
    if (
        document.get("status") != "complete"
        or document.get("jobs") != FULL_RUN_JOBS
        or document.get("caseTimeoutSeconds") != CASE_TIMEOUT_SECONDS
        or document.get("maxCounterexampleRounds") != MAX_COUNTEREXAMPLE_ROUNDS
        or document.get("verificationMode") != VERIFICATION_MODE
        or document.get("model") != MODEL
        or document.get("reasoningEffort") != REASONING_EFFORT
        or document.get("proofCheckTimeoutSeconds") != TRUSTED_CHECK_TIMEOUT_SECONDS
        or document.get("usageComplete") is not True
        or not isinstance(cases, list)
        or not all(isinstance(case, str) and case for case in cases)
        or len(cases) != 389
        or len(set(cases)) != 389
        or not isinstance(results, list)
        or len(results) != 389
        or not isinstance(configuration, dict)
        or configuration.get("jobs") != FULL_RUN_JOBS
        or configuration.get("caseTimeoutSeconds") != CASE_TIMEOUT_SECONDS
        or configuration.get("maxCounterexampleRounds")
        != MAX_COUNTEREXAMPLE_ROUNDS
        or configuration.get("verificationMode") != VERIFICATION_MODE
        or configuration.get("model") != MODEL
        or configuration.get("reasoningEffort") != REASONING_EFFORT
        or document.get("terminationGraceSeconds")
        != configuration.get("terminationGraceSeconds")
        or document.get("solverBin") != configuration.get("solverBin")
        or document.get("sqlEnvironment") != configuration.get("sqlEnvironment")
        or nested(document, "configuration", "proofAgent", "model") != MODEL
        or nested(document, "configuration", "proofAgent", "reasoningEffort")
        != REASONING_EFFORT
        or nested(document, "configuration", "proofAgent", "totalTimeoutSeconds")
        != CASE_TIMEOUT_SECONDS - 300
        or nested(
            document,
            "configuration",
            "proofAgent",
            "sessionRestartAfterFailedRounds",
        )
        != PROOF_AGENT_SESSION_RESTART_AFTER_FAILED_ROUNDS
        or nested(document, "configuration", "proofAgent", "sessionHomePolicy")
        != PROOF_AGENT_SESSION_HOME_POLICY
        or nested(document, "configuration", "proofAgent", "trustedCheckTimeoutSeconds")
        != TRUSTED_CHECK_TIMEOUT_SECONDS
        or resource_policy
        != {
            "memoryLimitMiB": PROOF_AGENT_MEMORY_LIMIT_MIB,
            "storageLimitMiB": PROOF_AGENT_STORAGE_LIMIT_MIB,
            "cpuLimit": None,
        }
        or document.get("proofAgentMemoryLimitMiB") != PROOF_AGENT_MEMORY_LIMIT_MIB
        or document.get("proofAgentStorageLimitMiB") != PROOF_AGENT_STORAGE_LIMIT_MIB
        or document.get("statementTimeoutSeconds") != STATEMENT_TIMEOUT_SECONDS
        or document.get("proofDockerImage") != image_id
        or document.get("proofDockerImageEffective") != image_id
        or document.get("proofDockerImageRequested")
        != (image.get("reference") if isinstance(image, dict) else None)
        or nested(document, "configuration", "frozenBenchmark", "benchmarkFingerprint")
        != BENCHMARK_FINGERPRINT
        or nested(document, "configuration", "frozenBenchmark", "frozenSummarySha256")
        != FROZEN_SUMMARY_SHA256
        or nested(document, "configuration", "frozenBenchmark", "frozenCaseCount")
        != 389
        or nested(document, "configuration", "frozenBenchmark", "generatedCaseCount")
        != 389
        or nested(
            document,
            "configuration",
            "frozenBenchmark",
            "selectedCaseSetSha256",
        )
        != FROZEN_CASE_SET_SHA256
        or nested(document, "provenance", "benchmarkFingerprint")
        != BENCHMARK_FINGERPRINT
        or nested(document, "provenance", "frozenSummarySha256")
        != FROZEN_SUMMARY_SHA256
        or not valid_sha256(source_digest)
        or nested(document, "provenance", "frameworkSourceTreeManifestSha256")
        != source_digest
        or not isinstance(image, dict)
        or image.get("resolved") is not True
        or not isinstance(image_id, str)
        or not image_id.startswith("sha256:")
        or not valid_sha256(image_id.removeprefix("sha256:"))
        or image.get("effectiveReference") != image_id
        or not isinstance(integrity, dict)
        or integrity.get("verified") is not True
        or document.get("integrityError") is not None
    ):
        raise PublishError(
            "full runner summary violates the accepted frozen 389/32x/4h contract"
        )
    assert isinstance(cases, list)
    assert isinstance(results, list)
    assert isinstance(configuration, dict)
    effective_solver_args = validate_solver_arguments(document, configuration)

    by_case: dict[str, dict[str, Any]] = {}
    for row in results:
        if not isinstance(row, dict) or not isinstance(row.get("caseId"), str):
            raise PublishError("full runner summary contains a malformed result row")
        case_id = row["caseId"]
        if not case_id or case_id in by_case:
            raise PublishError(
                "full runner summary contains an empty or duplicate caseId"
            )
        if (
            row.get("status") not in TERMINAL_STATUSES
            or row.get("usageComplete", "llmUsage" in row) is not True
            or (
                row.get("status") == "completed"
                and not completed_return_code_is_coherent(row)
            )
        ):
            raise PublishError(
                f"{case_id}: nonterminal, incoherent, or incomplete-usage result"
            )
        by_case[case_id] = row
    if set(by_case) != set(cases):
        raise PublishError("full runner cases and result rows do not reconcile")
    observed_counts = Counter(row["status"] for row in results)
    expected_counts = {
        "selected": 389,
        "pending": 0,
        "completed": observed_counts["completed"],
        "timedOut": observed_counts["timed_out"],
        "failed": observed_counts["failed"],
        "cancelled": 0,
    }
    if document.get("counts") != expected_counts:
        raise PublishError("full runner terminal counts do not exactly reconcile")

    source_manifest_path = path / "framework-source-tree-manifest.json"
    source_path, _ = validate_file_binding(
        configuration.get("frameworkSourceTree"),
        path_key="manifestPath",
        digest_key="manifestSha256",
        location="configuration.frameworkSourceTree",
        run_root=path,
        expected_path=source_manifest_path,
    )
    source_manifest = load_json(source_path)
    if (
        source_manifest.get("schemaVersion") != 1
        or source_manifest.get("kind") != "canonical-dirty-source-tree"
    ):
        raise PublishError("full run source-tree manifest has the wrong schema")
    try:
        helper_binding = runner_validators()[
            "validate_framework_source_tree_helper_binding"
        ](source_manifest)
    except Exception as error:
        raise PublishError(
            f"full run source-tree digest helper binding is invalid: {error}"
        ) from error
    if (
        configuration["frameworkSourceTree"].get("sourceTreeDigestHelper")
        != helper_binding
    ):
        raise PublishError(
            "configuration.frameworkSourceTree digest helper binding drifted"
        )

    solver_path, solver_digest = validate_file_binding(
        configuration.get("solverBinary"),
        path_key="path",
        digest_key="sha256",
        location="configuration.solverBinary",
        run_root=path,
    )
    if not os.access(solver_path, os.X_OK):
        raise PublishError("configuration.solverBinary.path is not executable")
    if (
        resolve_recorded_file(
            configuration.get("solverBin"), "configuration.solverBin", path
        )
        != solver_path
    ):
        raise PublishError("configuration.solverBin differs from bound solverBinary")
    runtime_snapshot = validate_rocq_runtime_snapshot(
        configuration.get("rocqRuntimeSnapshot"), path
    )
    proof_switch = resolve_recorded_directory(
        nested(configuration, "proofAgent", "rocqOpamSwitch"),
        "configuration.proofAgent.rocqOpamSwitch",
        path,
    )
    if proof_switch != runtime_snapshot["root"]:
        raise PublishError("proof-agent Rocq switch differs from runtime snapshot")
    rocq_snapshot = validate_rocq_authority_snapshot(
        configuration.get("rocqAuthoritySnapshot"),
        path,
        runtime_snapshot,
        configuration.get("frameworkSourceTree"),
    )
    if (
        configuration.get("rocqAuthoritySnapshotPolicy")
        != TRUSTED_ROCQ_AUTHORITY_SNAPSHOT_POLICY
    ):
        raise PublishError("configuration Rocq authority snapshot policy drifted")
    trusted_stack = validate_trusted_stack(
        configuration.get("trustedStack"),
        path,
        legacy_catalog=legacy_catalog,
    )
    validate_rocq_snapshot_trusted_stack_binding(
        runtime_snapshot, rocq_snapshot, trusted_stack
    )
    trusted_path = trusted_stack["path"]
    trusted_digest = trusted_stack["sha256"]
    input_manifest = validate_input_manifests(
        configuration.get("inputManifest"), path, set(cases)
    )
    frontend_stack = validate_frontend_stack(configuration.get("frontendStack"), path)
    codex_provider = validate_codex_provider(configuration.get("codexProvider"), path)
    launch_environments = validate_runner_launch_environments(
        configuration, codex_provider, frontend_stack
    )
    postgres_profile = validate_postgres_profile(
        configuration.get("postgresServerProfile"), path
    )
    if configuration.get("postgresUrl") != {
        "configured": True,
        "sha256": postgres_profile["urlSha256"],
    }:
        raise PublishError("PostgreSQL URL fingerprint and server profile differ")
    gate = validate_cohort16_gate(
        configuration.get("cohort16Gate"),
        path,
        source_digest,
        document.get("startedAt"),
        input_manifest["rows"],
        input_manifest["semanticRows"],
        solver_digest,
        rocq_snapshot["manifestSha256"],
        trusted_digest,
        frontend_stack["sha256"],
        codex_provider,
        postgres_profile["sha256"],
        configuration,
        legacy_catalog=legacy_catalog,
    )
    expected_integrity = {
        "frameworkSourceTreeManifestSha256": source_digest,
        "solverBinarySha256": solver_digest,
        "rocqRuntimeSnapshotManifestSha256": runtime_snapshot["manifestSha256"],
        "rocqAuthoritySnapshotManifestSha256": rocq_snapshot["manifestSha256"],
        "trustedStackManifestSha256": trusted_digest,
        "frontendStackManifestSha256": frontend_stack["sha256"],
        "codexProviderManifestSha256": codex_provider["sha256"],
        "codexConfigSha256": codex_provider["configSha256"],
        "providerEndpointSha256": codex_provider["endpointSha256"],
        "solverEnvironmentSha256": launch_environments["solverEnvironment"]["sha256"],
        "postgresServerProfileSha256": postgres_profile["sha256"],
        "inputManifestSha256": input_manifest["sha256"],
        "selectedInputManifestSha256": input_manifest["selectedSha256"],
        "semanticAuthoritySha256": input_manifest["semanticSha256"],
        "selectedSemanticAuthoritySha256": input_manifest[
            "selectedSemanticSha256"
        ],
        "cohort16GateSha256": gate["sha256"],
    }
    for key, expected in expected_integrity.items():
        if integrity.get(key) != expected:
            raise PublishError(f"full runner integrity binding drifted: {key}")
    for key, expected in (
        (
            "rocqRuntimeSnapshotManifestSha256",
            runtime_snapshot["manifestSha256"],
        ),
        (
            "rocqAuthoritySnapshotManifestSha256",
            rocq_snapshot["manifestSha256"],
        ),
        ("frontendStackManifestSha256", frontend_stack["sha256"]),
        ("codexProviderManifestSha256", codex_provider["sha256"]),
        ("codexConfigSha256", codex_provider["configSha256"]),
        ("providerEndpointSha256", codex_provider["endpointSha256"]),
        ("postgresServerProfileSha256", postgres_profile["sha256"]),
    ):
        if nested(document, "provenance", key) != expected:
            raise PublishError(f"full runner provenance binding drifted: {key}")
    provenance_runtime_root = resolve_recorded_directory(
        nested(document, "provenance", "rocqRuntimeSnapshotRoot"),
        "provenance.rocqRuntimeSnapshotRoot",
        path,
    )
    if provenance_runtime_root != runtime_snapshot["root"]:
        raise PublishError("full runner provenance Rocq runtime root drifted")
    provenance_snapshot_root = resolve_recorded_directory(
        nested(document, "provenance", "rocqAuthoritySnapshotRoot"),
        "provenance.rocqAuthoritySnapshotRoot",
        path,
    )
    if provenance_snapshot_root != rocq_snapshot["root"]:
        raise PublishError("full runner provenance Rocq snapshot root drifted")
    bindings = {
        "source": {"path": source_path, "sha256": source_digest},
        "solver": {"path": solver_path, "sha256": solver_digest},
        "rocqRuntimeSnapshot": runtime_snapshot,
        "rocqAuthoritySnapshot": rocq_snapshot,
        "trustedStack": {"path": trusted_path, "sha256": trusted_digest},
        "frontendStack": frontend_stack,
        "codexProvider": codex_provider,
        "launchEnvironments": launch_environments,
        "postgresServerProfile": postgres_profile,
        "cohort16Gate": gate,
        "inputManifest": input_manifest,
        "dockerImage": image_id,
        "effectiveSolverArgs": effective_solver_args,
        "sqlEnvironment": configuration["sqlEnvironment"],
        "legacyCatalogArtifacts": legacy_catalog,
    }
    bindings["proofAgentBrokerEvidence"] = validate_case_evidence(
        document, path, bindings, sha256(path / "runner-summary.json")
    )
    return document, bindings


def validate_final_audit(path: Path, source_digest: str) -> dict[str, Any]:
    report = load_json(path)
    checks = report.get("checks")
    for name in (
        "fairness",
        "soundness",
        "sqlSemantics",
        "logicalCorrectness",
        "benchmarkLeakage",
        "trustedBoundary",
    ):
        if not isinstance(checks, dict) or checks.get(name) is not True:
            raise PublishError(f"final audit omits required passed check {name}")
    bound_digest = report.get(
        "sourceTreeManifestSha256",
        report.get("sourceTreeDigest", report.get("revisionId")),
    )
    if (
        report.get("schemaVersion") != 1
        or report.get("finalAudit") is not True
        or report.get("passed") is not True
        or not report.get("independentAgentSessionId")
        or report.get("unresolvedCritical") not in ([], None)
        or report.get("unresolvedHigh") not in ([], None)
        or bound_digest != source_digest
    ):
        raise PublishError(
            "final audit is not independent, passed, finding-free, and bound to the run source digest"
        )
    return {
        "report": "final-audit.json",
        "sha256": sha256(path),
        "revisionId": report.get("revisionId"),
        "sourceTreeManifestSha256": source_digest,
        "independentAgentSessionId": report["independentAgentSessionId"],
        "finalAudit": True,
        "passed": True,
    }


def results_by_case(
    summary: dict[str, Any], source: Path
) -> dict[str, tuple[dict[str, Any], Path]]:
    values: dict[str, tuple[dict[str, Any], Path]] = {}
    for row in summary.get("results", []):
        if not isinstance(row, dict) or not isinstance(row.get("caseId"), str):
            raise PublishError(f"{source}: malformed runner result")
        raw_case = row["caseId"]
        case = canonical_case(raw_case)
        if case in values:
            raise PublishError(f"{source}: duplicate case {case}")
        values[case] = (row, source / "cases" / raw_case)
    return values


def copy_case_logs(
    staging: Path,
    case: str,
    source_dir: Path,
    raw: dict[str, Any],
    usage: dict[str, Any],
    broker_evidence: dict[str, Any] | None,
) -> dict[str, str]:
    destination = staging / "logs" / case
    destination.mkdir(parents=True)
    run_root = source_dir.parents[1]
    copied = ["stdout.log", "stderr.log", "time.txt", "status.json"]
    copied.append("runner-result.json")
    if nested(raw, "reportEvidence", "present") is True:
        copied.append("report.json")
    for filename in copied:
        source = source_dir / filename
        if not source.is_file():
            raise PublishError(f"{case}: source run is missing {source}")
        shutil.copyfile(source, destination / filename)
    for name, filename in (
        ("schema", "schema.sql"),
        ("source", "source.sql"),
        ("target", "target.sql"),
        ("metadata", "metadata.json"),
    ):
        binding = nested(raw, "inputFiles", name)
        input_path = resolve_recorded_file(
            binding.get("path") if isinstance(binding, dict) else None,
            f"{case}.inputFiles.{name}.path",
            run_root,
        )
        shutil.copyfile(input_path, destination / filename)
        if sha256(destination / filename) != binding.get("sha256"):
            raise PublishError(f"{case}: copied {name} input digest drifted")
    if "semanticSidecar" in raw.get("inputFiles", {}):
        binding = raw["inputFiles"]["semanticSidecar"]
        sidecar_path = resolve_recorded_file(
            binding.get("path") if isinstance(binding, dict) else None,
            f"{case}.inputFiles.semanticSidecar.path",
            run_root,
        )
        shutil.copyfile(sidecar_path, destination / "semantic-sidecar.json")
        if sha256(destination / "semantic-sidecar.json") != binding.get("sha256"):
            raise PublishError(f"{case}: copied semantic sidecar digest drifted")
    proof_source = nested(raw, "proofMetrics", "proofSource")
    if isinstance(proof_source, dict) and proof_source.get("present") is True:
        proof_path = resolve_recorded_file(
            proof_source.get("path"), f"{case}.proofMetrics.proofSource.path", run_root
        )
        shutil.copyfile(proof_path, destination / "proof-source.v")
        if sha256(destination / "proof-source.v") != proof_source.get("sha256"):
            raise PublishError(f"{case}: copied proof source digest drifted")
    if broker_evidence is not None:
        for binding in broker_evidence["files"]:
            source = source_dir / binding["sourceRelativePath"]
            target = destination / binding["canonicalRelativePath"]
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, target)
            if (
                sha256(target) != binding["sha256"]
                or target.stat().st_size != binding["bytes"]
            ):
                raise PublishError(f"{case}: copied proof-agent evidence drifted")
        write_json(destination / "proof-agent-evidence-manifest.json", broker_evidence)
    status = load_json(destination / "status.json")
    status_case = status.get("caseId")
    if (
        status.get("schemaVersion") != 1
        or not isinstance(status_case, str)
        or canonical_case(status_case) != case
        or status.get("usageComplete") is not True
    ):
        raise PublishError(f"{case}: malformed or incomplete status.json")
    for key in (
        "status",
        "returnCode",
        "outcome",
        "backendStatus",
        "certification",
        "runnerError",
        "usageError",
    ):
        if status.get(key) != raw.get(key):
            raise PublishError(f"{case}: status.json disagrees with runner on {key}")
    if (destination / "time.txt").read_text(encoding="utf-8") != (
        f"elapsed_ms={raw.get('elapsedMs')}\n"
    ):
        raise PublishError(f"{case}: time.txt disagrees with runner elapsedMs")
    if load_json(destination / "runner-result.json") != raw:
        raise PublishError(f"{case}: copied runner-result.json drifted")
    raw_usage = load_json(source_dir / "usage.json")
    if canonical_usage(raw_usage, f"{case}.source usage.json") != usage:
        raise PublishError(f"{case}: runner result and usage.json differ")
    write_json(destination / "usage.json", usage)
    logs = {
        "stdout": f"logs/{case}/stdout.log",
        "stderr": f"logs/{case}/stderr.log",
        "time": f"logs/{case}/time.txt",
        "status": f"logs/{case}/status.json",
        "usage": f"logs/{case}/usage.json",
        "schemaInput": f"logs/{case}/schema.sql",
        "sourceInput": f"logs/{case}/source.sql",
        "targetInput": f"logs/{case}/target.sql",
        "metadataInput": f"logs/{case}/metadata.json",
    }
    if (destination / "semantic-sidecar.json").is_file():
        logs["semanticSidecarInput"] = f"logs/{case}/semantic-sidecar.json"
    logs["runnerResult"] = f"logs/{case}/runner-result.json"
    if "report.json" in copied:
        logs["report"] = f"logs/{case}/report.json"
        if sha256(destination / "report.json") != nested(
            raw, "reportEvidence", "sha256"
        ):
            raise PublishError(f"{case}: copied report digest drifted")
    if isinstance(proof_source, dict) and proof_source.get("present") is True:
        logs["proofSource"] = f"logs/{case}/proof-source.v"
    if broker_evidence is not None:
        logs["proofAgentEvidenceManifest"] = (
            f"logs/{case}/proof-agent-evidence-manifest.json"
        )
        logs["proofAgentEvidenceManifestSha256"] = sha256(
            destination / "proof-agent-evidence-manifest.json"
        )
    return logs


def write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(value, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )


def result_row(
    raw: dict[str, Any],
    case: str,
    source_kind: str,
    run_id: str,
    logs: dict[str, str],
    usage: dict[str, Any],
) -> dict[str, Any]:
    status = raw.get("status")
    if status not in TERMINAL_STATUSES:
        raise PublishError(f"{case}: nonterminal status {status!r}")
    elapsed = raw.get("elapsedMs")
    if isinstance(elapsed, bool) or not isinstance(elapsed, int) or elapsed < 0:
        raise PublishError(f"{case}: invalid elapsedMs")
    proof_metrics = json.loads(json.dumps(raw.get("proofMetrics")))
    if (
        isinstance(proof_metrics, dict)
        and nested(proof_metrics, "proofSource", "present") is True
    ):
        proof_metrics["proofSource"]["path"] = logs.get("proofSource")
    row = {
        "caseId": case,
        "benchmark": raw.get("benchmark"),
        "status": status,
        "returnCode": raw.get("returnCode"),
        "elapsedMs": elapsed,
        "outcome": raw.get("outcome"),
        "reason": raw.get("reason"),
        "backendStatus": raw.get("backendStatus"),
        "certification": raw.get("certification"),
        "sourceRun": {
            "kind": source_kind,
            "runId": run_id,
        },
        "logs": logs,
        "llmUsage": usage,
        "inputFiles": {
            "schema": {
                "path": logs["schemaInput"],
                "sha256": nested(raw, "inputFiles", "schema", "sha256"),
            },
            "source": {
                "path": logs["sourceInput"],
                "sha256": nested(raw, "inputFiles", "source", "sha256"),
            },
            "target": {
                "path": logs["targetInput"],
                "sha256": nested(raw, "inputFiles", "target", "sha256"),
            },
            "metadata": {
                "path": logs["metadataInput"],
                "sha256": nested(raw, "inputFiles", "metadata", "sha256"),
            },
        },
        "effectiveConfiguration": raw.get("effectiveConfiguration"),
        "proofMetrics": proof_metrics,
        "reportEvidence": {
            "path": logs.get("report"),
            "present": "report" in logs,
            "sha256": nested(raw, "reportEvidence", "sha256"),
        },
    }
    if "semanticSidecarInput" in logs:
        row["inputFiles"]["semanticSidecar"] = {
            "path": logs["semanticSidecarInput"],
            "sha256": nested(raw, "inputFiles", "semanticSidecar", "sha256"),
        }
    if raw.get("recoveredFromTerminalReport") is True:
        row["recoveredFromTerminalReport"] = True
        row["elapsedIncomplete"] = raw.get("elapsedIncomplete")
        row["terminalizedByInvocation"] = raw.get("terminalizedByInvocation")
    for key in ("runnerError", "reportError", "usageError"):
        if key in raw:
            row[key] = raw[key]
    return row


def aggregate_proof_agent_broker_metrics(
    rows: list[dict[str, Any]],
) -> dict[str, int]:
    """Sum the independently validated per-case broker evidence counters."""
    totals = {key: 0 for key in PROOF_AGENT_BROKER_METRIC_KEYS}
    for row in rows:
        case = row.get("caseId")
        metrics = row.get("proofMetrics")
        if not isinstance(metrics, dict):
            raise PublishError(f"{case}: canonical row has no proofMetrics")
        for key in PROOF_AGENT_BROKER_METRIC_KEYS:
            totals[key] += nonnegative_integer(
                metrics.get(key), f"{case}.proofMetrics.{key}"
            )
    if (
        totals["diagnosticAcceptedAuditArtifactCount"]
        != totals["diagnosticAcceptedRequestCount"]
        or totals["diagnosticRejectedSourceAuditArtifactCount"]
        != 4 * totals["diagnosticRejectedSourceAuditCount"]
        or totals["diagnosticPreservedArtifactCount"]
        != totals["diagnosticAcceptedAuditArtifactCount"]
        + totals["diagnosticRejectedSourceAuditArtifactCount"]
    ):
        raise PublishError(
            "canonical diagnostic broker artifact totals do not reconcile"
        )
    return totals


def render_readme(
    run_id: str,
    statuses: Counter[str],
    outcomes: Counter[str],
    usage: dict[str, Any],
    rows: list[dict[str, Any]],
) -> str:
    outcome_lines = ["| Outcome | Cases |", "|---|---:|"]
    outcome_lines.extend(
        f"| `{name}` | {count} |" for name, count in sorted(outcomes.items())
    )
    problem_lines = [
        "| Terminal runner status | Cases | Canonical cases |",
        "|---|---:|---|",
    ]
    for status in ("timed_out", "failed"):
        cases = [row["caseId"] for row in rows if row["status"] == status]
        display = ", ".join(f"`{case}`" for case in cases[:20])
        if len(cases) > 20:
            display += f", … (+{len(cases) - 20})"
        problem_lines.append(f"| `{status}` | {len(cases)} | {display or '—'} |")
    return f"""# Canonical Logos full-pipeline result

This directory publishes the one accepted full Logos run for the frozen 389-case cohort. Run `{run_id}` used 32 concurrent cases, an exact {CASE_TIMEOUT_SECONDS}-second total timeout per case, `outcome-unconditional` verification, and `gpt-5.6-sol` at medium reasoning effort for both LLM stages. Counterexample search preceded FormalSQL lowering, proof-agent repair/resume, deterministic workspace auditing, and trusted Rocq checking. Each reached proof stage has a digest-bound, self-contained copy of its host-broker diagnostics and compile checkpoints under its canonical log directory. No local rerun overlay is permitted.

## Outcomes

{chr(10).join(outcome_lines)}

## Timeouts and failures

{chr(10).join(problem_lines)}

Runner statuses remain distinct from semantic outcomes: an incomplete proof is not an equivalence certificate, a validated counterexample is not a frontend failure, and timeouts are not collapsed into proof failures.

## Token and API-price-equivalent accounting

Authoritative Codex JSON events report {usage['inputTokens']:,} input tokens, including {usage['cachedInputTokens']:,} cached input tokens, and {usage['outputTokens']:,} output tokens ({usage['totalTokens']:,} total). The standard API-price equivalent is **USD {usage['estimatedCostUsd']:.6f}**, computed with the public `gpt-5.6-sol` rates current on {PRICING_AS_OF}: USD {INPUT_RATE:g}/M uncached input, USD {CACHED_INPUT_RATE:g}/M cached input, and USD {OUTPUT_RATE:g}/M output. Source: {PRICING_SOURCE}.

## Audit conclusion

Independent semantic-soundness and lemma-coverage audits passed with zero unresolved critical or high findings. Publication is additionally bound to the final independent proof-agent framework audit and the exact dirty source-tree manifest digest recorded in `manifest.json`.

## Limitations

- Results certify only what the modeled FormalSQL syntax and frozen PostgreSQL environment express; unsupported semantics fail closed.
- Scalar subqueries are limited to the modeled one-column INTEGER/proven-singleton comparison encoding; other scalar-value shapes and types, unmodeled window functions/frames, general interval/session-timezone behavior, and unsupported collations/operator classes receive no invented theorem.
- Bag laws apply at proved reset/abstraction boundaries; exact ordered observations retain order and multiplicity.
- API cost is an equivalent estimate from authoritative token counts and the documented standard rates, not a statement about ChatGPT subscription billing.
"""


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--full-run", required=True, type=Path)
    parser.add_argument("--run-id", required=True)
    parser.add_argument("--final-audit", required=True, type=Path)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument(
        "--source-tree-root",
        type=Path,
        default=LOGOS_ROOT,
        help="Logos source checkout that must match the full-run source digest.",
    )
    args = parser.parse_args()

    if not args.run_id.strip():
        raise PublishError("--run-id must be nonempty")

    full_run = args.full_run.expanduser().resolve()
    output = args.output.expanduser().resolve()
    for name in ("latest", "run", "complete", ".archive", "lowering-current"):
        alias = output / name
        if alias.exists() or alias.is_symlink():
            raise PublishError(f"forbidden canonical lifecycle alias exists: {alias}")
    expected = expected_cases(output)
    audit = load_json(output / "audit.json")
    if audit.get("status") != "passed":
        raise PublishError("audit.json must pass before publication")
    full_summary_path = full_run / "runner-summary.json"
    validated_full_summary_sha256 = sha256(full_summary_path)
    full_summary, bindings = validate_full_summary(full_run)
    if sha256(full_summary_path) != validated_full_summary_sha256:
        raise PublishError("full runner summary changed during publication validation")
    source_digest = nested(
        full_summary, "configuration", "frameworkSourceTree", "manifestSha256"
    )
    try:
        current_source_digest = source_tree_manifest_sha256(
            build_source_tree_manifest(args.source_tree_root.expanduser().resolve())
        )
    except SourceTreeError as error:
        raise PublishError(f"cannot attest the current source tree: {error}") from error
    if current_source_digest != source_digest:
        raise PublishError(
            "current Logos source tree differs from the audited full-run source tree"
        )
    docker_image = nested(full_summary, "configuration", "proofAgent", "dockerImage")
    final_audit_path = args.final_audit.expanduser().resolve()
    final_audit = validate_final_audit(final_audit_path, source_digest)
    selected = results_by_case(full_summary, full_run)
    summary_cases = {canonical_case(case) for case in full_summary["cases"]}
    if set(selected) != expected or summary_cases != expected:
        raise PublishError(
            "full run cases/results do not reconcile with the frozen 389-case cohort"
        )

    staging_parent = output.parent
    staging_parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(
        prefix=".Logos.publish-", dir=staging_parent
    ) as temporary:
        staging = Path(temporary)
        source_full_summary_sha256 = validated_full_summary_sha256
        rows: list[dict[str, Any]] = []
        for case in sorted(expected):
            raw, source_dir = selected[case]
            usage = canonical_usage(raw.get("llmUsage"), f"{case}.llmUsage")
            logs = copy_case_logs(
                staging,
                case,
                source_dir,
                raw,
                usage,
                bindings["proofAgentBrokerEvidence"].get(case),
            )
            rows.append(
                result_row(
                    raw,
                    case,
                    "full",
                    args.run_id,
                    logs,
                    usage,
                )
            )

        statuses = Counter(row["status"] for row in rows)
        outcomes = Counter(
            "None" if row.get("outcome") is None else str(row["outcome"])
            for row in rows
        )
        totals = {
            "model": MODEL,
            "inputTokens": sum(row["llmUsage"]["inputTokens"] for row in rows),
            "cachedInputTokens": sum(
                row["llmUsage"]["cachedInputTokens"] for row in rows
            ),
            "outputTokens": sum(row["llmUsage"]["outputTokens"] for row in rows),
            "totalTokens": sum(row["llmUsage"]["totalTokens"] for row in rows),
            "estimatedCostUsd": sum(
                row["llmUsage"]["estimatedCostUsd"] for row in rows
            ),
        }
        broker_totals = aggregate_proof_agent_broker_metrics(rows)
        results_text = "".join(
            json.dumps(row, ensure_ascii=False) + "\n" for row in rows
        )
        canonical_results_sha256 = sha256_text(results_text)
        runner_copy = staging / "runner-summary.json"
        shutil.copyfile(full_summary_path, runner_copy)
        if sha256(runner_copy) != source_full_summary_sha256:
            raise PublishError("full runner summary changed while being copied")
        source_manifest_copy = staging / "framework-source-tree-manifest.json"
        shutil.copyfile(bindings["source"]["path"], source_manifest_copy)
        if sha256(source_manifest_copy) != source_digest:
            raise PublishError("source-tree manifest changed while being copied")
        evidence_copies = {
            "frozen-input-manifest.json": (
                bindings["inputManifest"]["path"],
                bindings["inputManifest"]["sha256"],
            ),
            "selected-input-manifest.json": (
                bindings["inputManifest"]["selectedPath"],
                bindings["inputManifest"]["selectedSha256"],
            ),
            "semantic-input-authority-manifest.json": (
                bindings["inputManifest"]["semanticPath"],
                bindings["inputManifest"]["semanticSha256"],
            ),
            "selected-semantic-input-authority-manifest.json": (
                bindings["inputManifest"]["selectedSemanticPath"],
                bindings["inputManifest"]["selectedSemanticSha256"],
            ),
            "trusted-stack-manifest.json": (
                bindings["trustedStack"]["path"],
                bindings["trustedStack"]["sha256"],
            ),
            "trusted-rocq-runtime-manifest.json": (
                bindings["rocqRuntimeSnapshot"]["manifestPath"],
                bindings["rocqRuntimeSnapshot"]["manifestSha256"],
            ),
            "trusted-rocq-authority-build.log": (
                bindings["rocqAuthoritySnapshot"]["buildLogPath"],
                bindings["rocqAuthoritySnapshot"]["buildLogSha256"],
            ),
            "frontend-stack-manifest.json": (
                bindings["frontendStack"]["path"],
                bindings["frontendStack"]["sha256"],
            ),
            "codex-provider-manifest.json": (
                bindings["codexProvider"]["path"],
                bindings["codexProvider"]["sha256"],
            ),
            "codex-provider-config.toml": (
                bindings["codexProvider"]["configPath"],
                bindings["codexProvider"]["configSha256"],
            ),
            "postgres-server-profile.json": (
                bindings["postgresServerProfile"]["path"],
                bindings["postgresServerProfile"]["sha256"],
            ),
            "cohort16-gate-summary.json": (
                bindings["cohort16Gate"]["path"],
                bindings["cohort16Gate"]["sha256"],
            ),
            "cohort16-scope.json": (
                bindings["cohort16Gate"]["scopePath"],
                bindings["cohort16Gate"]["scopeSha256"],
            ),
        }
        for destination_name, (source_path, expected_digest) in evidence_copies.items():
            destination_path = staging / destination_name
            shutil.copyfile(source_path, destination_path)
            if sha256(destination_path) != expected_digest:
                raise PublishError(f"{destination_name} changed while being copied")
        copy_rocq_authority_snapshot(bindings["rocqAuthoritySnapshot"], staging)
        shutil.copyfile(final_audit_path, staging / "final-audit.json")
        if sha256(staging / "final-audit.json") != final_audit["sha256"]:
            raise PublishError("final audit changed while being copied")
        continuation_count = nested(full_summary, "provenance", "continuationCount")
        if (
            isinstance(continuation_count, bool)
            or not isinstance(continuation_count, int)
            or continuation_count < 0
        ):
            raise PublishError("full run has invalid continuationCount provenance")
        manifest = {
            "schemaVersion": 1,
            "artifactKind": "canonical-logos-full-pipeline-results",
            "canonical": True,
            "benchmarkFingerprint": BENCHMARK_FINGERPRINT,
            "totalCases": 389,
            "fullRun": {
                "runId": args.run_id,
                "caseSetSha256": FROZEN_CASE_SET_SHA256,
                "jobs": FULL_RUN_JOBS,
                "caseTimeoutSeconds": CASE_TIMEOUT_SECONDS,
                "verificationMode": VERIFICATION_MODE,
                "model": MODEL,
                "reasoningEffort": REASONING_EFFORT,
                "proofAgentTimeoutSeconds": CASE_TIMEOUT_SECONDS - 300,
                "proofAgentSessionRestartAfterFailedRounds": (
                    PROOF_AGENT_SESSION_RESTART_AFTER_FAILED_ROUNDS
                ),
                "proofAgentSessionHomePolicy": PROOF_AGENT_SESSION_HOME_POLICY,
                **effective_proof_agent_diagnostic_configuration(),
                "solverLaunchEnvironmentPolicy": bindings["launchEnvironments"][
                    "solverLaunchEnvironmentPolicy"
                ],
                "solverEnvironment": bindings["launchEnvironments"][
                    "solverEnvironment"
                ],
                "solverEnvironmentSha256": bindings["launchEnvironments"][
                    "solverEnvironment"
                ]["sha256"],
                "frontendLaunchEnvironmentPolicy": bindings["launchEnvironments"][
                    "frontendLaunchEnvironmentPolicy"
                ],
                "commandProviderEnvironmentPolicy": bindings["launchEnvironments"][
                    "commandProviderEnvironmentPolicy"
                ],
                "trustedCheckTimeoutSeconds": TRUSTED_CHECK_TIMEOUT_SECONDS,
                "resourcePolicy": {
                    "memoryLimitMiB": PROOF_AGENT_MEMORY_LIMIT_MIB,
                    "storageLimitMiB": PROOF_AGENT_STORAGE_LIMIT_MIB,
                    "cpuLimit": None,
                },
                "dockerImage": docker_image,
                "status": "complete",
                "invocationCount": continuation_count + 1,
                "runnerSummarySha256": source_full_summary_sha256,
                "canonicalResultsJsonlSha256": canonical_results_sha256,
                "proofAgentBrokerMetrics": broker_totals,
                "frameworkSourceTreeManifest": "framework-source-tree-manifest.json",
                "frameworkSourceTreeManifestSha256": source_digest,
                "inputManifest": "frozen-input-manifest.json",
                "inputManifestSha256": bindings["inputManifest"]["sha256"],
                "selectedInputManifest": "selected-input-manifest.json",
                "selectedInputManifestSha256": bindings["inputManifest"][
                    "selectedSha256"
                ],
                "semanticInputAuthorityManifest": (
                    "semantic-input-authority-manifest.json"
                ),
                "semanticAuthoritySha256": bindings["inputManifest"][
                    "semanticSha256"
                ],
                "selectedSemanticInputAuthorityManifest": (
                    "selected-semantic-input-authority-manifest.json"
                ),
                "selectedSemanticAuthoritySha256": bindings["inputManifest"][
                    "selectedSemanticSha256"
                ],
                "cohort16Gate": "cohort16-gate-summary.json",
                "cohort16GateSha256": bindings["cohort16Gate"]["sha256"],
                "cohort16Scope": "cohort16-scope.json",
                "cohort16ScopeSha256": bindings["cohort16Gate"]["scopeSha256"],
                "solverBinaryPath": nested(
                    full_summary, "configuration", "solverBinary", "path"
                ),
                "solverBinarySha256": bindings["solver"]["sha256"],
                "rocqAuthoritySnapshotPolicy": (
                    TRUSTED_ROCQ_AUTHORITY_SNAPSHOT_POLICY
                ),
                "rocqRuntimeSnapshotPolicy": TRUSTED_ROCQ_RUNTIME_SNAPSHOT_POLICY,
                "rocqRuntimeSnapshotPackaging": (
                    "manifest-only-exact-digest-live-tree-validated-at-publication-v1"
                ),
                "rocqRuntimeSnapshotManifest": (
                    "trusted-rocq-runtime-manifest.json"
                ),
                "rocqRuntimeSnapshotManifestSha256": bindings[
                    "rocqRuntimeSnapshot"
                ]["manifestSha256"],
                "rocqAuthoritySnapshotRoot": "trusted-rocq-authority",
                "rocqAuthoritySnapshotManifest": (
                    "trusted-rocq-authority-manifest.json"
                ),
                "rocqAuthoritySnapshotManifestSha256": bindings[
                    "rocqAuthoritySnapshot"
                ]["manifestSha256"],
                "rocqAuthorityBuildLog": "trusted-rocq-authority-build.log",
                "rocqAuthorityBuildLogSha256": bindings[
                    "rocqAuthoritySnapshot"
                ]["buildLogSha256"],
                "trustedStackManifest": "trusted-stack-manifest.json",
                "trustedStackManifestSha256": bindings["trustedStack"]["sha256"],
                "frontendStackManifest": "frontend-stack-manifest.json",
                "frontendStackManifestSha256": bindings["frontendStack"]["sha256"],
                "codexProviderManifest": "codex-provider-manifest.json",
                "codexProviderManifestSha256": bindings["codexProvider"]["sha256"],
                "codexProviderConfig": "codex-provider-config.toml",
                "codexProviderConfigSha256": bindings["codexProvider"]["configSha256"],
                "providerEndpointSha256": bindings["codexProvider"]["endpointSha256"],
                "postgresServerProfile": "postgres-server-profile.json",
                "postgresServerProfileSha256": bindings["postgresServerProfile"][
                    "sha256"
                ],
                "sourceTreeMatchVerifiedAtPublication": True,
            },
            "localReruns": [],
            "finalAudit": final_audit,
            "modelPricing": {
                "model": MODEL,
                "currency": "USD",
                "tier": "standard",
                "inputUsdPerMillionTokens": INPUT_RATE,
                "cachedInputUsdPerMillionTokens": CACHED_INPUT_RATE,
                "outputUsdPerMillionTokens": OUTPUT_RATE,
                "source": PRICING_SOURCE,
                "asOf": PRICING_AS_OF,
            },
        }
        write_json(staging / "manifest.json", manifest)
        (staging / "results.jsonl").write_text(results_text, encoding="utf-8")
        write_json(
            staging / "summary.json",
            {
                "schemaVersion": 1,
                "status": "complete",
                "runId": args.run_id,
                "sourceFullRunSummarySha256": source_full_summary_sha256,
                "totalCases": 389,
                "statusCounts": dict(statuses),
                "outcomeCounts": dict(outcomes),
                "llmUsage": totals,
                "proofAgentBrokerMetrics": broker_totals,
                "resultsJsonlSha256": canonical_results_sha256,
                "results": rows,
            },
        )
        (staging / "README.md").write_text(
            render_readme(args.run_id, statuses, outcomes, totals, rows),
            encoding="utf-8",
        )

        target_logs = output / "logs"
        if target_logs.exists():
            shutil.rmtree(target_logs)
        os.replace(staging / "logs", target_logs)
        finalize_staged_rocq_authority(
            staging, output, bindings["rocqAuthoritySnapshot"]
        )
        for filename in (
            "manifest.json",
            "final-audit.json",
            "framework-source-tree-manifest.json",
            "frozen-input-manifest.json",
            "selected-input-manifest.json",
            "semantic-input-authority-manifest.json",
            "selected-semantic-input-authority-manifest.json",
            "trusted-stack-manifest.json",
            "trusted-rocq-runtime-manifest.json",
            "trusted-rocq-authority-build.log",
            "frontend-stack-manifest.json",
            "codex-provider-manifest.json",
            "codex-provider-config.toml",
            "postgres-server-profile.json",
            "cohort16-gate-summary.json",
            "cohort16-scope.json",
            "runner-summary.json",
            "results.jsonl",
            "summary.json",
            "README.md",
        ):
            os.replace(staging / filename, output / filename)
    print(f"published 389 canonical cases under {output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
