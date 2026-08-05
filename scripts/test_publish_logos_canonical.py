#!/usr/bin/env python3
"""Focused fail-closed tests for the canonical Logos publisher."""

from __future__ import annotations

import hashlib
import json
import os
import re
import runpy
import shlex
import shutil
import subprocess
import sys
import tempfile
import textwrap
import unittest
from pathlib import Path
from types import SimpleNamespace

from logos_source_tree_digest import (
    build_manifest as build_source_tree_manifest,
    canonical_bytes as source_tree_manifest_bytes,
    manifest_sha256 as source_tree_manifest_sha256,
)


LOGOS_ROOT = Path(__file__).resolve().parents[1]
from logos_env import configured_path, load_logos_env  # noqa: E402

load_logos_env(LOGOS_ROOT)

PUBLISHER = LOGOS_ROOT / "scripts/publish-logos-canonical.py"
RUNNER = LOGOS_ROOT / "benchmarks/scripts/run-logos"
COHORT_AUTHORITY = LOGOS_ROOT / "benchmarks/core/authority/cohort-389.json"
SCOPE = LOGOS_ROOT / "benchmarks/core/authority/proof-gate-16.json"
INPUT_ROOT = LOGOS_ROOT / "benchmarks/core/.generated/sqlsolver"
SOURCE_TREE_DIGEST_HELPER_RECORD = {
    "path": "scripts/logos_source_tree_digest.py",
    "sha256": "a2b651399e0103adac71a11822803979c535ac8bc897479a54c4366bd5e44b81",
    "bytes": 8009,
    "executionPolicy": "exact-bytes-loaded-before-module-execution-v1",
}
INPUT_MANIFEST_ALGORITHM = "logos-frozen-input-manifest-v1"
TRUSTED_STACK_MANIFEST_ALGORITHM = "logos-trusted-proof-stack-manifest-v7"
TRUSTED_DYNAMIC_LINKING_ALGORITHM = "logos-elf-runtime-closure-v2"
TRUSTED_LDD_SHA256 = "ab2b0110ee2b8725a08deec886d57d84a37c31d1225aceb7321faf1b583c46f1"
FRONTEND_STACK_MANIFEST_ALGORITHM = "logos-sql-frontend-stack-manifest-v2"
FRONTEND_LAUNCH_BASH = "/usr/bin/bash"
FRONTEND_LAUNCH_ARGUMENTS = ("--noprofile", "--norc", "-c")
FRONTEND_LAUNCH_COMMAND_BODY = 'source "$0" "$@"'
CODEX_PROVIDER_MANIFEST_ALGORITHM = "logos-codex-provider-manifest-v1"
POSTGRES_PROFILE_MANIFEST_ALGORITHM = "logos-postgres-server-profile-v1"
FROZEN_INPUT_MANIFEST_SHA256 = (
    "d34443e927c3e68a28c6d216334c624e1b50d0b37d60c9c937d21202b9f3162e"
)
SEMANTIC_INPUT_AUTHORITY_ALGORITHM = "logos-semantic-input-authority-v1"
FROZEN_SEMANTIC_INPUT_AUTHORITY_SHA256 = (
    "8ee79987c8f77cb88bc637196931010b7da88e8f4fb3303392527f1e156587a4"
)
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
    "-c model_reasoning_effort=medium --dangerously-bypass-approvals-and-sandbox "
    "--skip-git-repo-check -"
)
CANONICAL_FRONTEND_COMMAND = shlex.join(
    (
        FRONTEND_LAUNCH_BASH,
        *FRONTEND_LAUNCH_ARGUMENTS,
        FRONTEND_LAUNCH_COMMAND_BODY,
        str((LOGOS_ROOT / "scripts/calcite-ir").resolve()),
    )
)
EXPLICITLY_EXCLUDED_ENVIRONMENT_VARIABLES = [
    "BASH_ENV",
    "ENV",
    "SHELLOPTS",
    "BASHOPTS",
    "LD_PRELOAD",
    "LD_LIBRARY_PATH",
    "OCAMLPATH",
    "CAML_LD_LIBRARY_PATH",
    "CDPATH",
]
FRONTEND_LAUNCH_EXCLUDED_VARIABLES = EXPLICITLY_EXCLUDED_ENVIRONMENT_VARIABLES + [
    "JAVA_TOOL_OPTIONS",
    "_JAVA_OPTIONS",
    "JDK_JAVA_OPTIONS",
    "CLASSPATH",
    "MAVEN_OPTS",
    "MAVEN_ARGS",
]
SOLVER_LAUNCH_EXCLUDED_VARIABLES = FRONTEND_LAUNCH_EXCLUDED_VARIABLES + [
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
]
TRUSTED_CHECKER_ENVIRONMENT_POLICY = {
    "schemaVersion": 1,
    "inheritedEnvironmentCleared": True,
    "fixedVariables": [
        "PATH=/Anaconda/bin:/usr/bin:/bin",
        "HOME=/nonexistent",
        "LC_ALL=C",
        "LANG=C",
    ],
    "hostEnvironmentAllowlist": [],
    "explicitContractVariables": [
        "LOGOS_REPO_ROOT",
        "LOGOS_PROOF_WORKDIR",
        "LOGOS_TRUSTED_ROCQ_CACHE_DIR",
        "LOGOS_ROCQ_OPAM_SWITCH",
    ],
    "unlistedEnvironmentPolicy": "excluded_by_env_clear_before_process_start",
    "explicitlyExcludedVariables": EXPLICITLY_EXCLUDED_ENVIRONMENT_VARIABLES,
    "explicitlyExcludedPrefixes": ["BASH_FUNC_"],
}
PROOF_AGENT_LAUNCHER_ENVIRONMENT_POLICY = {
    "schemaVersion": 1,
    "inheritedEnvironmentCleared": True,
    "fixedVariables": [
        "PATH=/usr/bin:/bin",
        "LC_ALL=C",
        "LANG=C",
    ],
    "hostEnvironmentAllowlist": [
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
    ],
    "explicitContractVariables": [
        "LOGOS_REPO_ROOT",
        "LOGOS_PROOF_WORKDIR",
        "LOGOS_PROOF_AGENT_CODEX_HOME",
        "LOGOS_PROOF_AGENT_STAGE",
        "LOGOS_PROOF_DIAGNOSTIC_SOCKET",
        "LOGOS_PROOF_DIAGNOSTIC_NONCE",
        "LOGOS_SOLVER_IMAGE",
        "LOGOS_PROOF_AGENT_COMMAND",
        "LOGOS_PROOF_AGENT_CATALOG_GUIDANCE",
        "LOGOS_PROOF_AGENT_MEMORY_LIMIT",
        "LOGOS_PROOF_AGENT_STORAGE_LIMIT_BYTES",
        "LOGOS_PROOF_AGENT_TIMEOUT",
    ],
    "unlistedEnvironmentPolicy": "excluded_by_env_clear_before_process_start",
    "explicitlyExcludedVariables": EXPLICITLY_EXCLUDED_ENVIRONMENT_VARIABLES,
    "explicitlyExcludedPrefixes": ["BASH_FUNC_"],
}
PROOF_AGENT_ENVIRONMENT_CONFIGURATION = {
    "trustedCheckerEnvironmentPolicy": TRUSTED_CHECKER_ENVIRONMENT_POLICY,
    "proofAgentLauncherEnvironmentPolicy": (PROOF_AGENT_LAUNCHER_ENVIRONMENT_POLICY),
}
CURRENT_PROOF_AGENT_LAUNCHER_ENVIRONMENT_POLICY = {
    **PROOF_AGENT_LAUNCHER_ENVIRONMENT_POLICY,
    "explicitContractVariables": [
        name
        for name in PROOF_AGENT_LAUNCHER_ENVIRONMENT_POLICY["explicitContractVariables"]
        if name != "LOGOS_PROOF_AGENT_CATALOG_GUIDANCE"
    ],
}
CURRENT_PROOF_AGENT_ENVIRONMENT_CONFIGURATION = {
    "trustedCheckerEnvironmentPolicy": TRUSTED_CHECKER_ENVIRONMENT_POLICY,
    "proofAgentLauncherEnvironmentPolicy": (
        CURRENT_PROOF_AGENT_LAUNCHER_ENVIRONMENT_POLICY
    ),
}
PROOF_AGENT_DIAGNOSTIC_CONFIGURATION = {
    "diagnosticTransport": "host_unix_broker",
    "diagnosticCachePolicy": "preflight_built_source_digest_bound_host_only",
    "diagnosticTimeoutPolicy": "positive_request_bounded_only_by_current_invocation_deadline",
    "diagnosticBudgetPolicy": "bounded_by_invocation_deadline",
    "diagnosticCheckerParallelismMax": 1,
    "diagnosticCheckerSchedulingPolicy": "sequential_host_broker_invocation_deadline_bounded",
    "compileCheckpointPolicy": "latest_host_problem_compile_pass_over_immutable_checked_module_cache_digest_deduplicated",
    "scratchPersistencePolicy": "regular_nonsymlink_allowed_extension_round_replacement_drop_other_extensions_with_warning_exact_digest_checked_promotion",
    "writableStorageLimitBytes": 2048 * 1024 * 1024,
    "writableStoragePolicy": "single_kernel_tmpfs_all_agent_writes_with_read_only_root_v1",
    "scratchAllowedExtensions": ["v", "md", "txt"],
    **PROOF_AGENT_ENVIRONMENT_CONFIGURATION,
}
CURRENT_PROOF_AGENT_DIAGNOSTIC_CONFIGURATION = {
    **PROOF_AGENT_DIAGNOSTIC_CONFIGURATION,
    **CURRENT_PROOF_AGENT_ENVIRONMENT_CONFIGURATION,
}
EFFECTIVE_PROOF_AGENT_DIAGNOSTIC_CONFIGURATION = {
    "proofAgentDiagnosticTransport": "host_unix_broker",
    "proofAgentDiagnosticCachePolicy": (
        "preflight_built_source_digest_bound_host_only"
    ),
    "proofAgentDiagnosticTimeoutPolicy": "positive_request_bounded_only_by_current_invocation_deadline",
    "proofAgentDiagnosticBudgetPolicy": "bounded_by_invocation_deadline",
    "proofAgentDiagnosticCheckerParallelismMax": 1,
    "proofAgentDiagnosticCheckerSchedulingPolicy": "sequential_host_broker_invocation_deadline_bounded",
    "proofAgentCompileCheckpointPolicy": "latest_host_problem_compile_pass_over_immutable_checked_module_cache_digest_deduplicated",
    "proofAgentScratchPersistencePolicy": "regular_nonsymlink_allowed_extension_round_replacement_drop_other_extensions_with_warning_exact_digest_checked_promotion",
    "proofAgentWritableStorageLimitBytes": 2048 * 1024 * 1024,
    "proofAgentWritableStoragePolicy": "single_kernel_tmpfs_all_agent_writes_with_read_only_root_v1",
    "proofAgentScratchAllowedExtensions": ["v", "md", "txt"],
    **PROOF_AGENT_ENVIRONMENT_CONFIGURATION,
}
CURRENT_EFFECTIVE_PROOF_AGENT_DIAGNOSTIC_CONFIGURATION = {
    **EFFECTIVE_PROOF_AGENT_DIAGNOSTIC_CONFIGURATION,
    **CURRENT_PROOF_AGENT_ENVIRONMENT_CONFIGURATION,
}
PROOF_AGENT_BROKER_METRICS = {
    "diagnosticRequestCount": 2,
    "diagnosticRequestedTimeoutSecondsReserved": 60,
    "diagnosticAcceptedRequestCount": 1,
    "diagnosticRejectedSourceAuditCount": 1,
    "diagnosticOtherRejectedRequestCount": 0,
    "diagnosticAcceptedAuditArtifactCount": 1,
    "diagnosticRejectedSourceAuditArtifactCount": 4,
    "diagnosticPreservedArtifactCount": 5,
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


def write_canonical_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n",
        encoding="utf-8",
    )


def diagnostic_artifact_binding(case_root: Path, path: Path) -> dict[str, object]:
    return {
        "path": path.relative_to(case_root).as_posix(),
        "sha256": sha256(path),
        "bytes": path.stat().st_size,
    }


def make_diagnostic_cache(case_root: Path) -> tuple[Path, str]:
    formal_root = case_root / "proof-stage/formal-sql"
    formal_root.mkdir(parents=True, exist_ok=True)
    for name, text in (
        ("Schema.v", "Definition fixture_schema := True.\n"),
        ("Queries.v", "Definition fixture_queries := True.\n"),
        ("Witness.v", "Definition fixture_witness := True.\n"),
    ):
        (formal_root / name).write_text(text, encoding="utf-8")
    cache_root = case_root / "proof-stage/proof-agent/trusted-diagnostic-cache"
    cache_root.mkdir(parents=True, exist_ok=True)
    for name in ("Schema.v", "Queries.v", "Witness.v"):
        shutil.copyfile(formal_root / name, cache_root / name)
    (cache_root / "Schema.vo").write_bytes(b"compiled schema fixture\n")
    (cache_root / "Queries.vo").write_bytes(b"compiled queries fixture\n")
    (cache_root / "Witness.vo").write_bytes(b"compiled witness fixture\n")
    module_root = cache_root / "ProofModules"
    module_root.mkdir()
    (module_root / "ORDER").write_text("", encoding="utf-8")
    entries = (
        "Schema.v",
        "Schema.vo",
        "Queries.v",
        "Queries.vo",
        "Witness.v",
        "Witness.vo",
        "ProofModules/ORDER",
    )
    manifest = cache_root / "SHA256SUMS"
    manifest.write_text(
        "".join(f"{sha256(cache_root / name)}  {name}\n" for name in entries),
        encoding="utf-8",
    )
    return manifest, sha256(manifest)


CONTEXT_BINDING_FILES = {
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


def make_proof_context(
    formal_root: Path,
    source_path: Path,
    target_path: Path,
    verification_mode: str,
) -> dict[str, object]:
    shutil.copyfile(source_path, formal_root / "source.sql")
    shutil.copyfile(target_path, formal_root / "target.sql")
    for name, text in (
        ("query-shape.json", "{}\n"),
        ("ordered-signatures.json", "[]\n"),
        ("observation-certificates.json", "{}\n"),
        ("semantic-primer.md", "fixture semantic primer\n"),
        ("search-rocq-declarations.py", "# fixture declaration search\n"),
        ("Goal.v", "Definition fixture_goal : Prop := True.\n"),
    ):
        (formal_root / name).write_text(text, encoding="utf-8")
    manifest: dict[str, object] = {
        "schemaVersion": 8,
        "authority": "fixture navigation context",
        "verificationMode": verification_mode,
        "staticPromptAndPrimerBytes": 300,
    }
    for field, name in CONTEXT_BINDING_FILES.items():
        path = formal_root / name
        manifest[field] = {
            "path": name,
            "bytes": path.stat().st_size,
            "sha256": sha256(path),
        }
    manifest_path = formal_root / "context-manifest.json"
    write_json(manifest_path, manifest)
    context: dict[str, object] = {
        "manifestPath": "proof-stage/formal-sql/context-manifest.json",
        "manifestSha256": sha256(manifest_path),
        "manifestBytes": manifest_path.stat().st_size,
        "problemModuleBytes": (formal_root / "Problem.v").stat().st_size
        if (formal_root / "Problem.v").is_file()
        else 1,
        "goalModuleBytes": manifest["goalModule"]["bytes"],
        "semanticPrimerBytes": manifest["semanticPrimer"]["bytes"],
        "catalogBytes": 10,
        "generatedContextBytes": 400,
    }
    for binding_name, (digest_field, bytes_field) in {
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
        "declarationSearch": (
            "declarationSearchSha256",
            "declarationSearchBytes",
        ),
    }.items():
        binding = manifest[binding_name]
        context[digest_field] = binding["sha256"]
        context[bytes_field] = binding["bytes"]
    return context


def discover_inputs() -> dict[str, dict[str, object]]:
    values: dict[str, dict[str, object]] = {}
    for metadata_path in sorted(INPUT_ROOT.rglob("metadata.json")):
        metadata = json.loads(metadata_path.read_text(encoding="utf-8"))
        relative = metadata_path.parent.relative_to(INPUT_ROOT)
        cohort = relative.parts[0] if len(relative.parts) > 1 else "generated"
        base = metadata.get("flatCaseId") or "__".join(relative.parts)
        case_id = base if base.startswith(f"{cohort}__") else f"{cohort}__{base}"
        case_id = re.sub(r"[^A-Za-z0-9_.-]+", "_", case_id).strip("_")
        directory = metadata_path.parent.resolve()
        values[case_id] = {
            "directory": directory,
            "schema": directory / "schema.sql",
            "source": directory / "sql1.sql",
            "target": directory / "sql2.sql",
        }
    return values


def frozen_input_manifest(inputs: dict[str, dict[str, object]]) -> bytes:
    rows = []
    for case, paths in inputs.items():
        rows.append(
            {
                "caseId": case,
                "schemaSha256": sha256(paths["schema"]),
                "sql1Sha256": sha256(paths["source"]),
                "sql2Sha256": sha256(paths["target"]),
            }
        )
    document = {
        "schemaVersion": 1,
        "algorithm": INPUT_MANIFEST_ALGORITHM,
        "caseCount": len(rows),
        "cases": sorted(rows, key=lambda row: row["caseId"]),
    }
    return (json.dumps(document, sort_keys=True, separators=(",", ":")) + "\n").encode(
        "utf-8"
    )


class PublisherOrdinaryTerminalProblemBindingTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.publisher = runpy.run_path(
            str(PUBLISHER), run_name="publisher_problem_binding_test"
        )
        cls.publish_error = cls.publisher["PublishError"]

    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.source_dir = Path(self.temporary.name) / "case"
        self.live = self.source_dir / "proof-stage/formal-sql/Problem.v"
        self.checked = (
            self.source_dir
            / "proof-stage/proof-agent/rounds/01/checked-workspace/Problem.v"
        )
        self.live.parent.mkdir(parents=True)
        self.checked.parent.mkdir(parents=True)
        self.payload = (
            b"Definition generated_verification_claim : "
            b"Logos.FormalSQL.VerificationConditions.verification_claim_kind := "
            b"Logos.FormalSQL.VerificationConditions.VerificationEquivalence.\n"
            b"Theorem generated_queries_verified : True. Proof. exact I. Qed.\n"
        )
        self.live.write_bytes(self.payload)
        self.checked.write_bytes(self.payload)
        digest = hashlib.sha256(self.payload).hexdigest()
        self.proof = {
            "verificationMode": "outcome_unconditional",
            "proofWorkspace": {"problemPath": "proof-stage/formal-sql/Problem.v"},
            "proofAgent": {
                "round": 1,
                "candidateClaim": "equivalence",
                "authorityClosurePath": (
                    "proof-stage/proof-agent/rounds/01/checked-workspace/"
                    "authority-closure.txt"
                ),
                "candidateProblemSha256": digest,
            },
        }
        self.row = {
            "proofMetrics": {
                "proofSource": {
                    "path": self.publisher["publisher_workspace_display_path"](
                        self.live
                    ),
                    "present": True,
                    "sha256": digest,
                    "bytes": len(self.payload),
                }
            }
        }

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def validate(self) -> None:
        self.publisher["validate_ordinary_terminal_problem_binding"](
            "case",
            self.row,
            self.proof,
            self.source_dir,
            "outcome_unconditional",
        )

    def rebind_payload(self, payload: bytes) -> None:
        self.payload = payload
        self.live.write_bytes(payload)
        self.checked.write_bytes(payload)
        digest = hashlib.sha256(payload).hexdigest()
        self.proof["proofAgent"]["candidateProblemSha256"] = digest
        self.row["proofMetrics"]["proofSource"].update(
            {"sha256": digest, "bytes": len(payload)}
        )

    def bind_conditional(self, source: str) -> str:
        constructor = {
            "derived": "PreconditionDerived",
            "external": "PreconditionExternal",
        }[source]
        definition = (
            "Definition generated_precondition : "
            "Logos.FormalSQL.VerificationConditions.verification_condition := "
            "Logos.FormalSQL.VerificationConditions.ConditionTrue."
        )
        self.rebind_payload(
            (
                "Definition generated_precondition_source : "
                "Logos.FormalSQL.VerificationConditions.precondition_source := "
                "Logos.FormalSQL.VerificationConditions."
                f"{constructor}.\n{definition}\n"
                "Theorem generated_queries_equivalent : True. Proof. exact I. Qed.\n"
            ).encode()
        )
        self.proof["verificationMode"] = "conditional"
        self.proof["proofAgent"].update(
            {"preconditionSource": source, "preconditionDefinition": definition}
        )
        return definition

    def validate_conditional(self, outcome: str) -> None:
        self.publisher["validate_ordinary_terminal_problem_binding"](
            "case", self.row, self.proof, self.source_dir, outcome
        )

    def test_accepts_exact_binding(self) -> None:
        self.validate()

    def test_rejects_live_mutation(self) -> None:
        self.live.write_bytes(self.payload + b"(* drift *)\n")
        with self.assertRaisesRegex(self.publish_error, "binding drifted"):
            self.validate()

    def test_rejects_coherently_rebound_countermodel_selector(self) -> None:
        self.rebind_payload(
            self.payload.replace(
                b"VerificationEquivalence", b"VerificationCountermodel"
            )
        )
        with self.assertRaisesRegex(self.publish_error, "unconditional equivalence"):
            self.validate()

    def test_rejects_unconditional_conditional_fields_and_claim_drift(self) -> None:
        self.proof["proofAgent"]["preconditionSource"] = "derived"
        with self.assertRaisesRegex(self.publish_error, "unconditional equivalence"):
            self.validate()
        self.proof["proofAgent"].pop("preconditionSource")
        self.proof["proofAgent"]["candidateClaim"] = "formal_countermodel"
        with self.assertRaisesRegex(self.publish_error, "claim is not equivalence"):
            self.validate()

    def test_rejects_conditional_external_as_derived_reclassification(self) -> None:
        self.bind_conditional("external")
        with self.assertRaisesRegex(self.publish_error, "provenance drifted"):
            self.validate_conditional("conditional_derived")

    def test_accepts_conditional_derived_and_external_bindings(self) -> None:
        for source in ("derived", "external"):
            self.bind_conditional(source)
            self.validate_conditional(f"conditional_{source}")

    def test_rejects_conditional_definition_claim_and_theorem_drift(self) -> None:
        definition = self.bind_conditional("derived")
        self.proof["proofAgent"]["preconditionDefinition"] = definition + " "
        with self.assertRaisesRegex(self.publish_error, "provenance drifted"):
            self.validate_conditional("conditional_derived")
        self.bind_conditional("derived")
        self.rebind_payload(
            self.payload
            + b"Definition generated_verification_claim : "
            + b"Logos.FormalSQL.VerificationConditions.verification_claim_kind := "
            + b"Logos.FormalSQL.VerificationConditions.VerificationEquivalence.\n"
        )
        with self.assertRaisesRegex(self.publish_error, "provenance drifted"):
            self.validate_conditional("conditional_derived")
        self.bind_conditional("derived")
        self.rebind_payload(
            self.payload.replace(
                b"generated_queries_equivalent", b"generated_queries_verified"
            )
        )
        with self.assertRaisesRegex(self.publish_error, "direct final theorem"):
            self.validate_conditional("conditional_derived")

    def test_rejects_intermediate_symlink(self) -> None:
        checked_parent = self.checked.parent
        external = Path(self.temporary.name) / "external"
        external.mkdir()
        (external / "Problem.v").write_bytes(self.payload)
        shutil.rmtree(checked_parent)
        checked_parent.symlink_to(external, target_is_directory=True)
        with self.assertRaisesRegex(self.publish_error, "symlink or non-directory"):
            self.validate()


class PublisherSessionSequenceTest(unittest.TestCase):
    def test_expected_cases_come_from_repository_authority(self) -> None:
        publisher = runpy.run_path(str(PUBLISHER), run_name="publisher_authority")
        cases = publisher["expected_cases"](Path("/nonexistent/publication"))
        self.assertEqual(len(cases), 389)
        self.assertEqual(
            hashlib.sha256(COHORT_AUTHORITY.read_bytes()).hexdigest(),
            publisher["COHORT_AUTHORITY_SHA256"],
        )

    def test_publisher_rejects_mutable_digest_helper_before_execution(self) -> None:
        with tempfile.TemporaryDirectory(prefix="logos-publisher-helper-pin-") as raw:
            sandbox_root = Path(raw) / "Logos"
            copied_publisher = sandbox_root / "scripts/publish-logos-canonical.py"
            copied_helper = sandbox_root / "scripts/logos_source_tree_digest.py"
            copied_env = sandbox_root / "scripts/logos_env.py"
            copied_publisher.parent.mkdir(parents=True)
            shutil.copy2(PUBLISHER, copied_publisher)
            shutil.copy2(
                LOGOS_ROOT / "scripts/logos_source_tree_digest.py", copied_helper
            )
            shutil.copy2(LOGOS_ROOT / "scripts/logos_env.py", copied_env)
            safe = subprocess.run(
                [sys.executable, str(copied_publisher), "--help"],
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                check=False,
            )
            self.assertEqual(safe.returncode, 0, safe.stderr)

            execution_marker = Path(raw) / "mutable-helper-executed"
            original_helper = copied_helper.read_bytes()
            malicious_prefix = (
                "from pathlib import Path\n"
                "Path("
                + repr(str(execution_marker))
                + ").write_text('unsafe helper executed', encoding='utf-8')\n"
                "raise SystemExit(0)\n"
            ).encode()
            self.assertLess(len(malicious_prefix) + 2, len(original_helper))
            copied_helper.write_bytes(
                malicious_prefix
                + b"#"
                + b"x" * (len(original_helper) - len(malicious_prefix) - 2)
                + b"\n"
            )
            rejected = subprocess.run(
                [sys.executable, str(copied_publisher), "--help"],
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                check=False,
            )
            self.assertNotEqual(rejected.returncode, 0)
            self.assertIn(
                "source-tree digest helper differs from the immutable publisher binding",
                rejected.stderr,
            )
            self.assertFalse(execution_marker.exists())

    def test_publisher_rejects_mutable_environment_helper_before_execution(self) -> None:
        with tempfile.TemporaryDirectory(prefix="logos-publisher-env-pin-") as raw:
            scripts = Path(raw) / "Logos/scripts"
            scripts.mkdir(parents=True)
            copied_publisher = scripts / "publish-logos-canonical.py"
            copied_digest = scripts / "logos_source_tree_digest.py"
            copied_env = scripts / "logos_env.py"
            shutil.copy2(PUBLISHER, copied_publisher)
            shutil.copy2(
                LOGOS_ROOT / "scripts/logos_source_tree_digest.py", copied_digest
            )
            shutil.copy2(LOGOS_ROOT / "scripts/logos_env.py", copied_env)
            marker = Path(raw) / "mutable-environment-helper-executed"
            payload = copied_env.read_bytes()
            prefix = (
                "from pathlib import Path\n"
                f"Path({str(marker)!r}).write_text('unsafe', encoding='utf-8')\n"
            ).encode()
            self.assertLess(len(prefix) + 2, len(payload))
            copied_env.write_bytes(
                prefix + b"#" + b"x" * (len(payload) - len(prefix) - 2) + b"\n"
            )
            rejected = subprocess.run(
                [sys.executable, str(copied_publisher), "--help"],
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                check=False,
            )
            self.assertNotEqual(rejected.returncode, 0)
            self.assertIn(
                "environment helper differs from the immutable publisher binding",
                rejected.stderr,
            )
            self.assertFalse(marker.exists())

    def test_current_semantic_manifest_format_is_bound_and_tamper_rejected(self) -> None:
        publisher = runpy.run_path(
            str(PUBLISHER), run_name="publisher_semantic_manifest_test"
        )
        runner = runpy.run_path(str(RUNNER), run_name="runner_semantic_manifest_test")
        cases = runner["discover_cases"](INPUT_ROOT.resolve())
        legacy = runner["build_input_manifest"](cases, legacy=True)
        semantic = runner["build_semantic_input_authority_manifest"](cases)
        legacy_bytes = runner["canonical_json_bytes"](legacy)
        semantic_bytes = runner["canonical_json_bytes"](semantic)
        legacy_digest = hashlib.sha256(legacy_bytes).hexdigest()
        semantic_digest = hashlib.sha256(semantic_bytes).hexdigest()
        self.assertEqual(len(cases), 389)
        self.assertEqual(semantic_digest, FROZEN_SEMANTIC_INPUT_AUTHORITY_SHA256)
        # SQL materialization is independently dirty in this shared worktree;
        # this focused format test binds its observed legacy digest locally
        # while retaining the real frozen semantic authority digest.
        publisher["validate_input_manifests"].__globals__[
            "FROZEN_INPUT_MANIFEST_SHA256"
        ] = legacy_digest
        with tempfile.TemporaryDirectory(prefix="logos-semantic-manifest-") as raw:
            root = Path(raw)
            paths = {
                "path": root / "input-manifest.json",
                "selectedPath": root / "selected-input-manifest.json",
                "semanticAuthorityPath": root
                / "semantic-input-authority-manifest.json",
                "selectedSemanticAuthorityPath": root
                / "selected-semantic-input-authority-manifest.json",
            }
            paths["path"].write_bytes(legacy_bytes)
            paths["selectedPath"].write_bytes(legacy_bytes)
            paths["semanticAuthorityPath"].write_bytes(semantic_bytes)
            paths["selectedSemanticAuthorityPath"].write_bytes(semantic_bytes)
            record = {
                "path": str(paths["path"]),
                "sha256": legacy_digest,
                "algorithm": INPUT_MANIFEST_ALGORITHM,
                "manifestSchemaVersion": 1,
                "caseCount": 389,
                "selectedPath": str(paths["selectedPath"]),
                "selectedSha256": legacy_digest,
                "selectedCaseCount": 389,
                "semanticAuthorityPath": str(paths["semanticAuthorityPath"]),
                "semanticAuthoritySha256": semantic_digest,
                "semanticAuthorityAlgorithm": SEMANTIC_INPUT_AUTHORITY_ALGORITHM,
                "selectedSemanticAuthorityPath": str(
                    paths["selectedSemanticAuthorityPath"]
                ),
                "selectedSemanticAuthoritySha256": semantic_digest,
                "expectedFrozenSemanticAuthoritySha256": semantic_digest,
                "frozenSemanticAuthorityVerified": True,
                "expectedFrozenSha256": legacy_digest,
                "frozenVerified": True,
            }
            bindings = publisher["validate_input_manifests"](
                record, root, {case.case_id for case in cases}
            )
            self.assertEqual(len(bindings["semanticRows"]), 389)
            paths["semanticAuthorityPath"].write_bytes(semantic_bytes + b"\n")
            with self.assertRaisesRegex(
                publisher["PublishError"], "digest mismatch"
            ):
                publisher["validate_input_manifests"](
                    record, root, {case.case_id for case in cases}
                )

    def test_publisher_projects_wetune_sidecar_and_rejects_digest_drift(self) -> None:
        publisher = runpy.run_path(
            str(PUBLISHER), run_name="publisher_sidecar_projection_test"
        )
        with tempfile.TemporaryDirectory(prefix="logos-publisher-sidecar-") as raw:
            root = Path(raw)
            source_dir = root / "run/cases/wetune-issues__31"
            input_dir = root / "selected/wetune-issues/31"
            source_dir.mkdir(parents=True)
            input_dir.mkdir(parents=True)
            input_files = {}
            digests = {}
            for logical, filename in (
                ("schema", "schema.sql"),
                ("source", "sql1.sql"),
                ("target", "sql2.sql"),
            ):
                path = input_dir / filename
                path.write_text("SELECT 1;\n", encoding="utf-8")
                digests[logical] = sha256(path)
                input_files[logical] = {
                    "path": str(path),
                    "sha256": digests[logical],
                }
            sidecar = root / "semantic-sidecar.json"
            sidecar.write_text(json.dumps({"primaryKeys": []}), encoding="utf-8")
            metadata = input_dir / "metadata.json"
            metadata.write_text(
                json.dumps(
                    {
                        "flatCaseId": "wetune-issues__31",
                        "integrityContract": {
                            "semanticSidecar": str(sidecar),
                        },
                    }
                ),
                encoding="utf-8",
            )
            input_files["metadata"] = {
                "path": str(metadata),
                "sha256": sha256(metadata),
            }
            input_files["semanticSidecar"] = {
                "path": str(sidecar),
                "sha256": sha256(sidecar),
            }
            stack = root / "trusted-stack.json"
            stack.write_text("{}\n", encoding="utf-8")
            row = {
                "inputDir": str(input_dir),
                "inputFiles": input_files,
            }
            bindings = {
                "sqlEnvironment": {
                    "defaultCollation": "C",
                    "characterClassification": "C",
                    "localeProvider": "libc",
                    "serverEncoding": "UTF8",
                },
                "trustedStack": {"path": stack, "sha256": sha256(stack)},
            }
            _, config = publisher["runner_case_authority"](
                "wetune-issues__31", row, source_dir, digests, bindings
            )
            self.assertIn("semanticSidecar", config.input_files["wetune-issues__31"])
            sidecar.write_text(json.dumps({"primaryKeys": [{"forged": True}]}))
            with self.assertRaisesRegex(
                publisher["PublishError"], "semantic sidecar binding drifted"
            ):
                publisher["runner_case_authority"](
                    "wetune-issues__31", row, source_dir, digests, bindings
                )

    def test_completed_unknown_return_code_requires_exact_crash_recovery_shape(self) -> None:
        publisher = runpy.run_path(
            str(PUBLISHER), run_name="publisher_crash_recovery_test"
        )
        coherent = publisher["completed_return_code_is_coherent"]
        recovered = {
            "status": "completed",
            "returnCode": None,
            "recoveredFromTerminalReport": True,
            "elapsedIncomplete": True,
            "terminalizedByInvocation": 2,
            "reportEvidence": {"present": True},
            "runnerError": None,
        }
        self.assertTrue(coherent(recovered))
        for field, value in (
            ("recoveredFromTerminalReport", False),
            ("elapsedIncomplete", False),
            ("terminalizedByInvocation", 0),
            ("reportEvidence", {"present": False}),
            ("runnerError", "framework failure"),
        ):
            with self.subTest(field=field):
                forged = dict(recovered)
                forged[field] = value
                self.assertFalse(coherent(forged))
        ordinary = {"status": "completed", "returnCode": 0}
        self.assertTrue(coherent(ordinary))

    def test_publisher_projects_trusted_stack_for_materialized_script_check(self) -> None:
        publisher = runpy.run_path(
            str(PUBLISHER), run_name="publisher_script_projection_test"
        )
        runner = runpy.run_path(str(RUNNER), run_name="runner_script_projection_test")
        with tempfile.TemporaryDirectory(prefix="logos-publisher-scripts-") as raw:
            run_root = Path(raw)
            case_id = "nonwetune-flat__fixture"
            source_dir = run_root / "cases" / case_id
            input_dir = run_root / "selected" / case_id
            source_dir.mkdir(parents=True)
            input_dir.mkdir(parents=True)
            sql_paths = {}
            for logical, filename in (
                ("schema", "schema.sql"),
                ("source", "sql1.sql"),
                ("target", "sql2.sql"),
            ):
                path = input_dir / filename
                path.write_text(f"-- {logical}\nSELECT 1;\n", encoding="utf-8")
                sql_paths[logical] = path
            metadata_path = input_dir / "metadata.json"
            metadata_path.write_text(
                json.dumps({"flatCaseId": "fixture"}), encoding="utf-8"
            )

            projections = (
                (
                    "crates/logos-solver/scripts/run-rocq-check.sh",
                    "proof-stage/formal-sql/run-rocq-check.sh",
                ),
                (
                    "crates/logos-solver/scripts/run-proof-agent-docker.sh",
                    "proof-stage/proof-agent/trusted-launcher/run-proof-agent-docker.sh",
                ),
                (
                    "crates/logos-solver/scripts/run-trusted-rocq-check.sh",
                    "proof-stage/proof-agent/trusted-launcher/run-trusted-rocq-check.sh",
                ),
            )
            trusted_scripts = []
            for index, (source_name, projection_name) in enumerate(projections):
                projection = source_dir / projection_name
                projection.parent.mkdir(parents=True, exist_ok=True)
                projection.write_text(f"#!/bin/bash\n# trusted {index}\n", encoding="utf-8")
                trusted_scripts.append(
                    {
                        "path": source_name,
                        "sha256": sha256(projection),
                        "bytes": projection.stat().st_size,
                    }
                )
            stack_path = run_root / "trusted-stack-manifest.json"
            write_json(stack_path, {"trustedScripts": trusted_scripts})
            input_files = {
                name: {"path": str(path), "sha256": sha256(path)}
                for name, path in sql_paths.items()
            }
            input_files["metadata"] = {
                "path": str(metadata_path),
                "sha256": sha256(metadata_path),
            }
            row = {
                "caseId": case_id,
                "inputDir": str(input_dir),
                "inputFiles": input_files,
            }
            bindings = {
                "sqlEnvironment": {
                    "defaultCollation": "C",
                    "characterClassification": "C",
                    "localeProvider": "libc",
                    "serverEncoding": "UTF8",
                },
                "trustedStack": {"path": stack_path, "sha256": sha256(stack_path)},
            }
            _, config = publisher["runner_case_authority"](
                case_id,
                row,
                source_dir,
                {name: sha256(path) for name, path in sql_paths.items()},
                bindings,
            )
            proof = {
                "proofWorkspace": {
                    "rocqCheckScriptPath": "proof-stage/formal-sql/run-rocq-check.sh",
                    "dockerAgentScriptPath": (
                        "proof-stage/proof-agent/trusted-launcher/"
                        "run-proof-agent-docker.sh"
                    ),
                }
            }
            runner["validate_materialized_trusted_scripts"](
                source_dir, proof, config
            )
            (source_dir / projections[1][1]).write_text(
                "#!/bin/bash\n# stale embedded launcher\n", encoding="utf-8"
            )
            with self.assertRaisesRegex(
                runner["RunnerError"], "differs from frozen stack"
            ):
                runner["validate_materialized_trusted_scripts"](
                    source_dir, proof, config
                )
            metadata_path.write_text(
                json.dumps(
                    {"flatCaseId": "fixture", "constraints": [{"forged": True}]}
                ),
                encoding="utf-8",
            )
            with self.assertRaisesRegex(
                publisher["PublishError"], "selected metadata binding drifted"
            ):
                publisher["runner_case_authority"](
                    case_id,
                    row,
                    source_dir,
                    {name: sha256(path) for name, path in sql_paths.items()},
                    bindings,
                )

    def test_publisher_delegates_counterexample_tamper_to_runner_policy(self) -> None:
        publisher = runpy.run_path(
            str(PUBLISHER), run_name="publisher_runner_delegation_test"
        )
        validate = publisher["validate_with_runner_report_policy"]
        publish_error = publisher["PublishError"]
        calls: list[str] = []

        def validate_completed_report(report, result, case_dir, case, config):
            del result, case_dir, case
            self.assertEqual(config.trusted_stack["manifestSha256"], "f" * 64)
            self.assertEqual(
                Path(config.trusted_stack["manifestPath"]).name,
                "trusted-stack-manifest.json",
            )
            calls.append(report["counterexample"]["kind"])
            if report["counterexample"] != {
                "kind": "dataDifference",
                "statement": 1,
            }:
                raise ValueError("strict runner counterexample policy rejected tampering")

        validate.__globals__["_RUNNER_VALIDATORS"] = {
            "validate_proof_context_manifest": lambda *args: None,
            "validate_materialized_trusted_scripts": lambda *args: None,
            "validate_completed_report": validate_completed_report,
        }
        with tempfile.TemporaryDirectory(prefix="logos-publisher-delegation-") as raw:
            run_root = Path(raw)
            case_id = "nonwetune-flat__fixture"
            source_dir = run_root / "cases" / case_id
            input_dir = run_root / "selected" / case_id
            source_dir.mkdir(parents=True)
            input_dir.mkdir(parents=True)
            sql = {
                "schema": ("schema.sql", "CREATE TABLE t(x INT);\n"),
                "source": ("sql1.sql", "SELECT x FROM t;\n"),
                "target": ("sql2.sql", "SELECT x FROM t;\n"),
            }
            input_files = {}
            input_digests = {}
            for name, (filename, contents) in sql.items():
                path = input_dir / filename
                path.write_text(contents, encoding="utf-8")
                digest = sha256(path)
                input_files[name] = {"path": str(path), "sha256": digest}
                input_digests[name] = digest
            metadata_path = input_dir / "metadata.json"
            metadata_path.write_text(
                json.dumps({"flatCaseId": "fixture"}), encoding="utf-8"
            )
            input_files["metadata"] = {
                "path": str(metadata_path),
                "sha256": sha256(metadata_path),
            }
            row = {
                "caseId": case_id,
                "inputDir": str(input_dir),
                "inputFiles": input_files,
            }
            bindings = {
                "sqlEnvironment": {
                    "defaultCollation": "C",
                    "characterClassification": "C",
                    "localeProvider": "libc",
                    "serverEncoding": "UTF8",
                },
                "trustedStack": {
                    "path": run_root / "trusted-stack-manifest.json",
                    "sha256": "f" * 64,
                },
            }
            report = {
                "counterexample": {"kind": "dataDifference", "statement": 1},
                "proof": None,
            }
            validate(
                case_id,
                row,
                report,
                source_dir,
                input_digests,
                bindings,
                validate_current_context=False,
            )
            tampered = json.loads(json.dumps(report))
            tampered["counterexample"]["statement"] = 2
            with self.assertRaisesRegex(
                publish_error, "strict runner counterexample policy rejected tampering"
            ):
                validate(
                    case_id,
                    row,
                    tampered,
                    source_dir,
                    input_digests,
                    bindings,
                    validate_current_context=False,
                )
            self.assertEqual(calls, ["dataDifference", "dataDifference"])

    def test_diagnostic_elapsed_warning_has_an_exact_boundary(self) -> None:
        publisher = runpy.run_path(str(PUBLISHER), run_name="publisher_unit_test")
        warning = publisher["diagnostic_elapsed_warning"]
        common = {
            "round_number": 2,
            "sequence": 3,
            "requested_timeout_seconds": 30,
            "effective_timeout_seconds": 30,
        }
        self.assertIsNone(warning(**common, elapsed_ms=36_000))
        self.assertEqual(
            warning(**common, elapsed_ms=36_001),
            {
                "code": "diagnostic_elapsed_exceeded_timeout_plus_kill_margin",
                "round": 2,
                "sequence": 3,
                "requestedTimeoutSeconds": 30,
                "effectiveTimeoutSeconds": 30,
                "elapsedMs": 36_001,
                "timeoutPlusKillMarginMs": 36_000,
                "overrunMs": 1,
            },
        )

    def test_diagnostic_elapsed_warning_schema_is_type_strict(self) -> None:
        publisher = runpy.run_path(str(PUBLISHER), run_name="publisher_unit_test")
        validate = publisher["validate_diagnostic_elapsed_warnings"]
        publish_error = publisher["PublishError"]
        warning = publisher["diagnostic_elapsed_warning"](
            round_number=1,
            sequence=1,
            requested_timeout_seconds=30,
            effective_timeout_seconds=30,
            elapsed_ms=36_001,
        )
        self.assertEqual(validate([warning], "fixture"), [warning])
        forged = dict(warning)
        forged["round"] = True
        with self.assertRaisesRegex(publish_error, "fixture\[0\]\.round"):
            validate([forged], "fixture")
        forged = dict(warning)
        forged["elapsedMs"] = float(forged["elapsedMs"])
        with self.assertRaisesRegex(publish_error, "fixture\[0\]\.elapsedMs"):
            validate([forged], "fixture")

    def test_backward_diagnostic_wall_clock_is_warning_only_and_type_strict(
        self,
    ) -> None:
        publisher = runpy.run_path(str(PUBLISHER), run_name="publisher_unit_test")
        warning = publisher["diagnostic_clock_warning"](
            round_number=2,
            sequence=3,
            prior_estimated_end_unix_ms=10_500,
            started_at_unix_ms=9_900,
        )
        self.assertEqual(
            warning,
            {
                "code": "diagnostic_wall_clock_regressed_or_overlapped",
                "round": 2,
                "sequence": 3,
                "startedAtUnixMs": 9_900,
                "priorEstimatedEndUnixMs": 10_500,
                "apparentRegressionMs": 600,
            },
        )
        validate = publisher["validate_diagnostic_clock_warnings"]
        self.assertEqual(validate([warning], "completed-proof fixture"), [warning])
        forged = dict(warning)
        forged["apparentRegressionMs"] = 599
        with self.assertRaisesRegex(
            publisher["PublishError"], "incoherent clock telemetry"
        ):
            validate([forged], "completed-proof fixture")
        self.assertIsNone(
            publisher["diagnostic_clock_warning"](
                round_number=2,
                sequence=4,
                prior_estimated_end_unix_ms=10_500,
                started_at_unix_ms=10_500,
            )
        )

    def test_cohort_gate_binds_selected_semantics_metadata_and_sidecar(self) -> None:
        publisher = runpy.run_path(str(PUBLISHER), run_name="publisher_gate_unit_test")
        validate = publisher["validate_cohort16_gate_case_input_authority"]
        digest_authority = publisher["cohort16_selected_authority_digests"]
        publish_error = publisher["PublishError"]
        with tempfile.TemporaryDirectory(prefix="logos-gate-semantic-") as raw:
            root = Path(raw)
            paths = {
                "schema": root / "schema.sql",
                "source": root / "sql1.sql",
                "target": root / "sql2.sql",
                "metadata": root / "metadata.json",
                "semanticSidecar": root / "semantic-sidecar.json",
            }
            paths["schema"].write_text("CREATE TABLE t (x int);\n", encoding="utf-8")
            paths["source"].write_text("SELECT x FROM t;\n", encoding="utf-8")
            paths["target"].write_text("SELECT x FROM t;\n", encoding="utf-8")
            write_json(paths["metadata"], {"flatCaseId": "fixture-flat"})
            write_json(paths["semanticSidecar"], {"tables": []})
            input_files = {
                name: {"path": str(path), "sha256": sha256(path)}
                for name, path in paths.items()
            }
            input_row = {
                "caseId": "fixture-case",
                "schemaSha256": input_files["schema"]["sha256"],
                "sql1Sha256": input_files["source"]["sha256"],
                "sql2Sha256": input_files["target"]["sha256"],
            }
            semantic_row = {
                "caseId": "fixture-case",
                "flatCaseId": "fixture-flat",
                "metadataSha256": input_files["metadata"]["sha256"],
                "semanticSidecarPath": str(paths["semanticSidecar"]),
                "semanticSidecarSha256": input_files["semanticSidecar"]["sha256"],
            }
            input_digest, semantic_digest = digest_authority(
                ["fixture-case"],
                {"fixture-case": input_row},
                {"fixture-case": semantic_row},
            )
            changed_semantic = dict(semantic_row)
            changed_semantic["metadataSha256"] = "a" * 64
            self.assertEqual(
                input_digest,
                digest_authority(
                    ["fixture-case"],
                    {"fixture-case": input_row},
                    {"fixture-case": changed_semantic},
                )[0],
            )
            self.assertNotEqual(
                semantic_digest,
                digest_authority(
                    ["fixture-case"],
                    {"fixture-case": input_row},
                    {"fixture-case": changed_semantic},
                )[1],
            )
            digests, _, metadata_path = validate(
                "fixture-case", input_files, input_row, semantic_row, root
            )
            self.assertEqual(digests["metadata"], semantic_row["metadataSha256"])
            self.assertEqual(metadata_path, paths["metadata"].resolve())

            write_json(paths["metadata"], {"flatCaseId": "tampered-flat"})
            input_files["metadata"]["sha256"] = sha256(paths["metadata"])
            with self.assertRaisesRegex(publish_error, "metadata semantic authority"):
                validate("fixture-case", input_files, input_row, semantic_row, root)
            write_json(paths["metadata"], {"flatCaseId": "fixture-flat"})
            input_files["metadata"]["sha256"] = sha256(paths["metadata"])

            write_json(paths["semanticSidecar"], {"tables": [{"name": "t"}]})
            input_files["semanticSidecar"]["sha256"] = sha256(
                paths["semanticSidecar"]
            )
            with self.assertRaisesRegex(publish_error, "sidecar authority drifted"):
                validate("fixture-case", input_files, input_row, semantic_row, root)

    def test_publisher_delegates_recovered_cohort_gate_certificate_to_runner(
        self,
    ) -> None:
        publisher = runpy.run_path(
            str(PUBLISHER), run_name="publisher_gate_delegation_test"
        )
        calls = []

        def validate_gate_report(report_path, case, config, expected_metrics):
            calls.append((report_path, case, config, expected_metrics))
            if expected_metrics.get("deterministicTailRecoveryAccepted") is not True:
                raise RuntimeError("recovery evidence was not delegated")

        publisher["validate_cohort16_gate_report_with_runner"].__globals__[
            "_RUNNER_VALIDATORS"
        ] = {"validate_gate_report": validate_gate_report}
        with tempfile.TemporaryDirectory(prefix="logos-gate-delegation-") as raw:
            root = Path(raw)
            report_path = root / "report.json"
            report_path.write_text("{}\n", encoding="utf-8")
            input_paths = {}
            input_files = {}
            for name, contents in (
                ("schema", "CREATE TABLE t (x int);\n"),
                ("source", "SELECT x FROM t;\n"),
                ("target", "SELECT x FROM t;\n"),
            ):
                path = root / f"{name}.sql"
                path.write_text(contents, encoding="utf-8")
                input_paths[name] = path.resolve()
                input_files[name] = {"path": str(path), "sha256": sha256(path)}
            metadata_path = root / "metadata.json"
            write_json(metadata_path, {"flatCaseId": "fixture-flat"})
            input_files["metadata"] = {
                "path": str(metadata_path),
                "sha256": sha256(metadata_path),
            }
            metrics = {"deterministicTailRecoveryAccepted": True}
            publisher["validate_cohort16_gate_report_with_runner"](
                "fixture__case",
                report_path,
                {"proofMetrics": metrics},
                metadata_path,
                {"flatCaseId": "fixture-flat"},
                input_paths,
                input_files,
                {
                    "proofAgent": {
                        "dockerImage": {"imageId": "sha256:" + "a" * 64}
                    },
                    "trustedStack": {
                        "manifestPath": str(root / "trusted-stack.json"),
                        "manifestSha256": "b" * 64,
                    },
                    "sqlEnvironment": {
                        "defaultCollation": "C",
                        "characterClassification": "C",
                        "localeProvider": "libc",
                        "serverEncoding": "UTF8",
                    },
                },
            )
        self.assertEqual(len(calls), 1)
        _, delegated_case, delegated_config, delegated_metrics = calls[0]
        self.assertEqual(delegated_case.flat_case_id, "fixture-flat")
        self.assertEqual(delegated_config.input_files["fixture__case"], input_files)
        self.assertIs(delegated_metrics, metrics)

    def test_publisher_validates_cross_binds_and_copies_rocq_snapshot(self) -> None:
        publisher = runpy.run_path(
            str(PUBLISHER), run_name="publisher_rocq_snapshot_test"
        )
        runner = runpy.run_path(str(RUNNER), run_name="runner_rocq_snapshot_fixture")
        with tempfile.TemporaryDirectory(prefix="logos-publisher-rocq-") as raw:
            run_root = Path(raw) / "run"
            snapshot_root = run_root / "runtime/trusted-rocq-authority"
            theory_root = snapshot_root / "theories/FormalSQL"
            theory_root.mkdir(parents=True)
            source = theory_root / "Fixture.v"
            object_path = theory_root / "Fixture.vo"
            source.write_text("Definition fixture : True := I.\n", encoding="utf-8")
            object_path.write_bytes(b"fixture-vo-authority\n")
            pair = {
                "sourcePath": "theories/FormalSQL/Fixture.v",
                "sourceSha256": sha256(source),
                "sourceBytes": source.stat().st_size,
                "objectPath": "theories/FormalSQL/Fixture.vo",
                "objectSha256": sha256(object_path),
                "objectBytes": object_path.stat().st_size,
            }
            runtime_root = run_root / "runtime/trusted-rocq-switch"
            runtime_root.mkdir()
            runtime_manifest_path = run_root / "trusted-rocq-runtime-manifest.json"
            runtime_manifest_path.write_text("{}\n", encoding="utf-8")
            runtime_snapshot = {
                "root": runtime_root.resolve(),
                "manifestPath": runtime_manifest_path.resolve(),
                "manifestSha256": sha256(runtime_manifest_path),
                "schemaVersion": 1,
                "algorithm": "logos-trusted-rocq-runtime-snapshot-v1",
                "policy": "run-private-immutable-rocq-runtime-bwrap-closure-v1",
                "directoryCount": 1,
                "fileCount": 1,
                "totalBytes": 1,
                "document": {"fixture": True},
            }
            framework_manifest_path = run_root / "framework-source-tree-manifest.json"
            framework_manifest_path.write_text("{}\n", encoding="utf-8")
            framework_source_tree = {
                "manifestPath": runner["workspace_display_path"](
                    framework_manifest_path
                ),
                "manifestSha256": sha256(framework_manifest_path),
            }
            build_log_path = run_root / "trusted-rocq-authority-build.log"
            build_log_path.write_text("private source build fixture\n", encoding="utf-8")
            build_log_path.chmod(0o444)
            document = {
                "schemaVersion": 2,
                "algorithm": "logos-trusted-rocq-authority-snapshot-v2",
                "policy": "run-private-forced-source-build-closure-v2",
                "frameworkSourceManifestPath": framework_source_tree["manifestPath"],
                "frameworkSourceManifestSha256": framework_source_tree[
                    "manifestSha256"
                ],
                "runtimeSnapshotManifestPath": runner["workspace_display_path"](
                    runtime_manifest_path
                ),
                "runtimeSnapshotManifestSha256": runtime_snapshot[
                    "manifestSha256"
                ],
                "runtimeSnapshotPolicy": runtime_snapshot["policy"],
                "buildLog": {
                    "path": runner["workspace_display_path"](build_log_path),
                    "sha256": sha256(build_log_path),
                    "bytes": build_log_path.stat().st_size,
                },
                "sourceObjectPairCount": 1,
                "fileCount": 2,
                "totalBytes": source.stat().st_size + object_path.stat().st_size,
                "sourceObjects": [pair],
            }
            manifest_path = run_root / "trusted-rocq-authority-manifest.json"
            manifest_path.write_bytes(runner["canonical_json_bytes"](document))
            for path in (source, object_path):
                path.chmod(0o444)
                os.utime(path, ns=(1_000_000_000, 1_000_000_000))
            for directory in (theory_root, theory_root.parent, snapshot_root):
                directory.chmod(0o555)
            manifest_path.chmod(0o444)
            record = {
                "root": str(snapshot_root),
                "manifestPath": str(manifest_path),
                "manifestSha256": sha256(manifest_path),
                "schemaVersion": 2,
                "algorithm": "logos-trusted-rocq-authority-snapshot-v2",
                "policy": "run-private-forced-source-build-closure-v2",
                "sourceObjectPairCount": 1,
                "fileCount": 2,
                "totalBytes": source.stat().st_size + object_path.stat().st_size,
            }
            def read_manifest(path: Path) -> tuple[dict[str, object], str]:
                return json.loads(path.read_text(encoding="utf-8")), sha256(path)

            def verify_tree(root: Path, value: dict[str, object]) -> None:
                for binding in value["sourceObjects"]:
                    for path_key, digest_key, bytes_key in (
                        ("sourcePath", "sourceSha256", "sourceBytes"),
                        ("objectPath", "objectSha256", "objectBytes"),
                    ):
                        path = root / binding[path_key]
                        if (
                            not path.is_file()
                            or path.is_symlink()
                            or path.stat().st_size != binding[bytes_key]
                            or sha256(path) != binding[digest_key]
                        ):
                            raise RuntimeError(f"snapshot file is invalid: {path}")

            def validate_external(
                value: dict[str, object],
                runtime: dict[str, object],
                framework: dict[str, object],
            ) -> None:
                if (
                    value["runtimeSnapshotManifestSha256"]
                    != runtime["manifestSha256"]
                    or value["runtimeSnapshotManifestPath"]
                    != runtime["manifestPath"]
                    or value["frameworkSourceManifestSha256"]
                    != framework["manifestSha256"]
                    or value["frameworkSourceManifestPath"]
                    != framework["manifestPath"]
                ):
                    raise RuntimeError("external provenance binding drifted")

            publisher["runner_validators"].__globals__["_RUNNER_VALIDATORS"] = {
                "read_rocq_authority_snapshot_manifest": read_manifest,
                "verify_rocq_authority_snapshot_tree": verify_tree,
                "validate_rocq_authority_external_bindings": validate_external,
                "workspace_display_path": runner["workspace_display_path"],
                "make_tree_writable_for_cleanup": runner[
                    "make_tree_writable_for_cleanup"
                ],
            }
            snapshot = publisher["validate_rocq_authority_snapshot"](
                record, run_root, runtime_snapshot, framework_source_tree
            )
            trusted_stack = {
                "sourceObjects": [pair],
                "rocqRuntimeSnapshot": {
                    key: value
                    for key, value in runtime_snapshot.items()
                    if key not in {"document", "root", "manifestPath"}
                }
                | {
                    "root": runner["workspace_display_path"](runtime_root),
                    "manifestPath": runner["workspace_display_path"](
                        runtime_manifest_path
                    ),
                },
                "rocqAuthoritySnapshot": {
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
                | {
                    "root": runner["workspace_display_path"](snapshot_root),
                    "manifestPath": runner["workspace_display_path"](manifest_path),
                },
            }
            publisher["validate_rocq_snapshot_trusted_stack_binding"](
                runtime_snapshot, snapshot, trusted_stack
            )
            with self.assertRaisesRegex(
                publisher["PublishError"], "differs from the immutable snapshot"
            ):
                changed_stack = dict(trusted_stack)
                changed_stack["sourceObjects"] = []
                publisher["validate_rocq_snapshot_trusted_stack_binding"](
                    runtime_snapshot, snapshot, changed_stack
                )
            staging = Path(raw) / "staging"
            staging.mkdir()
            publisher["copy_rocq_authority_snapshot"](snapshot, staging)
            canonical = Path(raw) / "canonical"
            canonical.mkdir()
            publisher["finalize_staged_rocq_authority"](
                staging, canonical, snapshot
            )
            self.assertEqual(
                sha256(canonical / "trusted-rocq-authority-manifest.json"),
                record["manifestSha256"],
            )
            self.assertTrue(
                (canonical / "trusted-rocq-authority/theories/FormalSQL/Fixture.vo")
                .is_file()
            )
            replacement = Path(raw) / "replacement"
            replacement.mkdir()
            publisher["copy_rocq_authority_snapshot"](snapshot, replacement)
            publisher["finalize_staged_rocq_authority"](
                replacement, canonical, snapshot
            )
            self.assertFalse(
                any(path.name.startswith(".trusted-rocq-authority.previous-") for path in canonical.iterdir())
            )

            source.chmod(0o644)
            source.write_text("Definition tampered : True := I.\n", encoding="utf-8")
            source.chmod(0o444)
            with self.assertRaisesRegex(
                publisher["PublishError"], "failed runner validation"
            ):
                publisher["validate_rocq_authority_snapshot"](
                    record, run_root, runtime_snapshot, framework_source_tree
                )

    def test_cohort_gate_rejects_rocq_snapshot_drift_on_every_surface(self) -> None:
        publisher = runpy.run_path(
            str(PUBLISHER), run_name="publisher_gate_rocq_binding_test"
        )
        validate = publisher["validate_cohort16_rocq_snapshot_bindings"]
        digest = "a" * 64
        runtime_digest = "c" * 64
        policy = "run-private-forced-source-build-closure-v2"
        runtime = {
            "root": "Logos/fixture/runtime/trusted-rocq-switch",
            "manifestPath": "Logos/fixture/trusted-rocq-runtime-manifest.json",
            "manifestSha256": runtime_digest,
            "schemaVersion": 1,
            "algorithm": "logos-trusted-rocq-runtime-snapshot-v1",
            "policy": "run-private-immutable-rocq-runtime-bwrap-closure-v1",
            "directoryCount": 3,
            "fileCount": 7,
            "totalBytes": 101,
        }
        record = {
            "rocqAuthoritySnapshotManifestSha256": digest,
            "rocqRuntimeSnapshotManifestSha256": runtime_digest,
        }
        configuration = {
            "rocqRuntimeSnapshot": runtime,
            "trustedStack": {"rocqRuntimeSnapshot": runtime},
            "proofAgent": {"rocqOpamSwitch": runtime["root"]},
            "rocqAuthoritySnapshotPolicy": policy,
            "rocqAuthoritySnapshot": {
                "policy": policy,
                "manifestSha256": digest,
            },
        }
        integrity = {
            "rocqAuthoritySnapshotManifestSha256": digest,
            "rocqRuntimeSnapshotManifestSha256": runtime_digest,
        }
        rows = [
            {
                "effectiveConfiguration": {
                    "rocqRuntimeSnapshotPolicy": runtime["policy"],
                    "rocqRuntimeSnapshotManifestSha256": runtime_digest,
                    "rocqAuthoritySnapshotPolicy": policy,
                    "rocqAuthoritySnapshotManifestSha256": digest,
                }
            }
        ]
        validate(record, configuration, integrity, rows, digest, runtime)
        mutations = []
        bad_record = json.loads(json.dumps(record))
        bad_record["rocqAuthoritySnapshotManifestSha256"] = "b" * 64
        mutations.append((bad_record, configuration, integrity, rows))
        bad_configuration = json.loads(json.dumps(configuration))
        bad_configuration["rocqAuthoritySnapshot"]["manifestSha256"] = "b" * 64
        mutations.append((record, bad_configuration, integrity, rows))
        bad_integrity = json.loads(json.dumps(integrity))
        bad_integrity["rocqAuthoritySnapshotManifestSha256"] = "b" * 64
        mutations.append((record, configuration, bad_integrity, rows))
        bad_rows = json.loads(json.dumps(rows))
        bad_rows[0]["effectiveConfiguration"][
            "rocqAuthoritySnapshotManifestSha256"
        ] = "b" * 64
        mutations.append((record, configuration, integrity, bad_rows))
        for values in mutations:
            with self.subTest(surface=values):
                with self.assertRaisesRegex(
                    publisher["PublishError"], "Rocq authority snapshot drifted"
                ):
                    validate(*values, digest, runtime)

        bad_runtime_configuration = json.loads(json.dumps(configuration))
        bad_runtime_configuration["proofAgent"]["rocqOpamSwitch"] = (
            "Logos/fixture/runtime/untrusted-switch"
        )
        with self.assertRaisesRegex(
            publisher["PublishError"], "Rocq authority snapshot drifted"
        ):
            validate(
                record,
                bad_runtime_configuration,
                integrity,
                rows,
                digest,
                runtime,
            )

    def test_final_theorem_detection_ignores_nested_rocq_comments(self) -> None:
        publisher = runpy.run_path(str(PUBLISHER), run_name="publisher_unit_test")
        declares = publisher["problem_declares_final_theorem"]
        for mode, theorem, goal in (
            (
                "outcome_unconditional",
                "generated_queries_verified",
                "generated_verification_goal",
            ),
            (
                "conditional",
                "generated_queries_equivalent",
                "generated_equivalence_goal",
            ),
        ):
            with self.subTest(mode=mode):
                placeholder = textwrap.dedent(
                    f"""\
                    (* LOGOS_PROOF_HOLE: add
                       (* a nested planning note *)
                       Theorem {theorem} : {goal}.
                    *)
                    """
                )
                self.assertFalse(declares(placeholder, mode))
                self.assertTrue(
                    declares(
                        placeholder
                        + f"Theorem {theorem} : {goal}.\nProof. exact I. Qed.",
                        mode,
                    )
                )

    def test_final_theorem_detection_requires_a_direct_theorem_sentence(self) -> None:
        publisher = runpy.run_path(str(PUBLISHER), run_name="publisher_unit_test")
        declares = publisher["problem_declares_final_theorem"]
        for indirect in (
            'Definition reminder := "Theorem generated_queries_verified".',
            'Definition reminder := "note. Theorem generated_queries_verified".',
            "Lemma generated_queries_verified : generated_verification_goal.",
            "Fail Theorem generated_queries_verified : generated_verification_goal.",
        ):
            with self.subTest(indirect=indirect):
                self.assertFalse(declares(indirect, "outcome-unconditional"))
        self.assertTrue(
            declares(
                "Theorem (* direct declaration *) generated_queries_verified : "
                "generated_verification_goal.",
                "outcome-unconditional",
            )
        )

    def test_countermodel_claim_requires_the_fully_qualified_trusted_type(self) -> None:
        publisher = runpy.run_path(str(PUBLISHER), run_name="publisher_unit_test")
        declares = publisher["problem_declares_formal_countermodel_claim"]
        self.assertTrue(
            declares(
                "Definition generated_verification_claim : "
                "Logos.FormalSQL.VerificationConditions.verification_claim_kind :=\n"
                "  Logos.FormalSQL.VerificationConditions.VerificationCountermodel."
            )
        )
        self.assertFalse(
            declares(
                "Definition generated_verification_claim : verification_claim_kind :=\n"
                "  Logos.FormalSQL.VerificationConditions.VerificationCountermodel."
            )
        )

    def test_rocq_comment_stripping_preserves_strings_and_line_count(self) -> None:
        publisher = runpy.run_path(str(PUBLISHER), run_name="publisher_unit_test")
        strip_comments = publisher["strip_rocq_comments"]
        text = textwrap.dedent(
            """\
            Definition label := "(* literal *) and a doubled "" quote".
            (* outer
               (* nested *)
            *)
            Definition kept := True.
            """
        )
        stripped = strip_comments(text)
        self.assertIn('"(* literal *) and a doubled "" quote"', stripped)
        self.assertEqual(len(stripped.splitlines()), len(text.splitlines()))
        self.assertNotIn("outer", stripped)
        self.assertIn("Definition kept := True.", stripped)

    def test_runner_and_publisher_final_theorem_detectors_match(self) -> None:
        runner = runpy.run_path(str(RUNNER), run_name="runner_rocq_lexing_contract")
        publisher = runpy.run_path(
            str(PUBLISHER), run_name="publisher_rocq_lexing_contract"
        )
        corpus = (
            "",
            "(* Theorem generated_queries_equivalent : True. *)",
            "(* outer (* nested Theorem generated_queries_equivalent *) *)",
            'Definition note := "Theorem generated_queries_equivalent".',
            'Definition note := "sentence. Theorem generated_queries_equivalent".',
            "Lemma generated_queries_equivalent : True.",
            "Theorem generated_queries_equivalent : True.",
            "Theorem (* bridge *) generated_queries_equivalent : True.",
            "Theorem generated_queries_verified : True.",
            "Theorem (* bridge *) generated_queries_verified : True.",
            'Definition label := "sentence. still a string".\n'
            "Theorem generated_queries_equivalent : True.",
        )
        runner_declares = runner["problem_declares_final_theorem"]
        publisher_declares = publisher["problem_declares_final_theorem"]
        for mode in ("outcome-unconditional", "conditional"):
            for text in corpus:
                with self.subTest(mode=mode, text=text):
                    self.assertEqual(
                        runner_declares(text, mode),
                        publisher_declares(text, mode),
                    )

    def test_runner_and_publisher_compile_authority_contracts_match(self) -> None:
        runner = runpy.run_path(
            str(RUNNER), run_name="runner_compile_authority_contract"
        )
        publisher = runpy.run_path(
            str(PUBLISHER), run_name="publisher_compile_authority_contract"
        )
        candidate = "a" * 64
        other = "b" * 64
        exact_problem_pass = {
            "compilePassed": True,
            "problemCompilePassed": True,
            "mode": "problem",
            "candidatePath": "Problem.v",
            "compileCheckpointAdvanced": True,
            "candidateSha256": candidate,
        }
        module_pass = {
            **exact_problem_pass,
            "problemCompilePassed": False,
            "mode": "module",
            "candidatePath": "ProofModules/Core.v",
            "compileCheckpointAdvanced": False,
        }
        failed_problem = {**exact_problem_pass, "compilePassed": False}
        cases = (
            (candidate, [], True),
            (other, [exact_problem_pass], True),
            (other, [], False),
            (other, [module_pass], False),
            (other, [failed_problem], False),
        )
        runner_authorized = runner["candidate_problem_has_compile_authority"]
        publisher_authorized = publisher["candidate_problem_has_compile_authority"]
        for active, invocations, expected in cases:
            with self.subTest(active=active, invocations=invocations):
                self.assertIs(
                    runner_authorized(candidate, active, invocations), expected
                )
                self.assertEqual(
                    runner_authorized(candidate, active, invocations),
                    publisher_authorized(candidate, active, invocations),
                )

    def test_bounded_sessions_restart_exactly_once_and_are_not_reused(self) -> None:
        publisher = runpy.run_path(str(PUBLISHER), run_name="publisher_unit_test")
        validate = publisher["validate_proof_agent_session_sequence"]
        publish_error = publisher["PublishError"]
        rounds = [
            {
                "workspaceGeneration": 1,
                "sessionGeneration": 1,
                "sessionRestarted": False,
                "checkpointTransition": (
                    "newWorkspaceInitial" if index == 0 else "continued"
                ),
                "sessionId": "session-a",
                "success": False,
            }
            for index in range(16)
        ] + [
            {
                "workspaceGeneration": 1,
                "sessionGeneration": 2,
                "sessionRestarted": True,
                "sessionRestartReason": "failedRoundLimit",
                "checkpointTransition": "restoredExisting",
                "sessionId": "session-b",
                "success": False,
            }
        ]
        validate(rounds, [], "fixture")

        rounds[-1]["sessionId"] = "session-a"
        with self.assertRaisesRegex(publish_error, "reused after restart"):
            validate(rounds, [], "fixture")

    def test_fixed_witness_transition_allows_an_early_fresh_session(self) -> None:
        publisher = runpy.run_path(str(PUBLISHER), run_name="publisher_fixed_restart")
        validate = publisher["validate_proof_agent_session_sequence"]
        publish_error = publisher["PublishError"]
        transitions = [{"afterRound": 1, "toWorkspaceGeneration": 2}]
        rounds = [
            {
                "workspaceGeneration": 1,
                "sessionGeneration": 1,
                "sessionRestarted": False,
                "checkpointTransition": "newWorkspaceInitial",
                "sessionId": "session-a",
                "success": False,
            },
            {
                "workspaceGeneration": 2,
                "sessionGeneration": 2,
                "sessionRestarted": True,
                "sessionRestartReason": "fixedWitnessReplacement",
                "checkpointTransition": "newWorkspaceInitial",
                "sessionId": "session-b",
                "success": False,
            },
        ]
        validate(rounds, transitions, "fixture")
        del rounds[1]["sessionRestartReason"]
        with self.assertRaisesRegex(publish_error, "session transition drifted"):
            validate(rounds, transitions, "fixture")

    def test_workspace_transition_binds_canonical_handoff_and_contexts(self) -> None:
        publisher = runpy.run_path(str(PUBLISHER), run_name="publisher_transition")
        validate = publisher["validate_proof_workspace_transitions"]
        canonical_digest = publisher["canonical_json_sha256"]
        publish_error = publisher["PublishError"]
        handoff = {
            "guidance": "use Ω",
            "decision": "counterexample_candidate",
            "reason": "witness café",
        }
        self.assertEqual(
            canonical_digest(handoff),
            "80d6572a83f08a4be4f10e94c84305ed370b81ff692b45fe019d15e41a1b94a0",
        )
        rounds = [
            {
                "workspaceGeneration": 1,
                "contextManifestSha256": "a" * 64,
                "counterexampleHandoff": handoff,
            },
            {
                "workspaceGeneration": 2,
                "contextManifestSha256": "b" * 64,
            },
        ]
        transition = {
            "afterRound": 1,
            "fromWorkspaceGeneration": 1,
            "toWorkspaceGeneration": 2,
            "reason": "fixedWitnessReplacement",
            "triggeringHandoffSha256": canonical_digest(handoff),
            "fromContextManifestSha256": "a" * 64,
            "toContextManifestSha256": "b" * 64,
            "fromTrustedDiagnosticCache": {
                "workspaceGeneration": 1,
                "manifestPath": "proof-stage/proof-agent/workspace-generations/0001/trusted-diagnostic-cache/SHA256SUMS",
                "manifestSha256": "d" * 64,
            },
            "newTrustedEnvironmentPreflight": {
                "timeoutSeconds": 420,
                "elapsedMs": 1,
                "exitCode": 0,
                "timedOut": False,
            },
            "newInitialProblemCompileCheckpoint": {
                "workspaceGeneration": 2,
                "path": "proof-stage/proof-agent/workspace-generations/0002/initial-problem-checkpoint/Problem.v",
                "sha256": "c" * 64,
                "round": 0,
                "sequence": 0,
            },
        }
        proof = {"proofWorkspaceTransitions": [transition]}
        config = {
            "context": {
                "manifestPath": "proof-stage/formal-sql/context-manifest.json",
                "manifestSha256": "b" * 64,
            }
        }
        transitions, generations = validate("fixture", proof, rounds, config)
        self.assertEqual(transitions, [transition])
        self.assertIs(generations[2], transition)
        transition["triggeringHandoffSha256"] = "0" * 64
        with self.assertRaisesRegex(publish_error, "handoff binding drifted"):
            validate("fixture", proof, rounds, config)

    def test_versioned_checkpoint_and_preflight_elapsed_drift_is_warning_only(self) -> None:
        publisher = runpy.run_path(str(PUBLISHER), run_name="publisher_generation_evidence")
        validate_checkpoint = publisher["validate_initial_checkpoint_evidence"]
        validate_preflight = publisher["validate_trusted_preflight_evidence"]
        validate_warnings = publisher["validate_trusted_elapsed_warnings"]
        make_warning = publisher["trusted_elapsed_warning"]
        with tempfile.TemporaryDirectory(prefix="logos-generation-evidence-") as raw:
            case = Path(raw) / "case"
            evidence_root = case / "proof-stage/proof-agent"
            generation_root = evidence_root / "workspace-generations/0001"
            checkpoint_root = generation_root / "initial-problem-checkpoint"
            checkpoint_root.mkdir(parents=True)
            (checkpoint_root / "Problem.v").write_text(
                "Definition checkpoint : True := I.\n", encoding="utf-8"
            )
            (checkpoint_root / "stdout.txt").write_bytes(b"\xffstdout")
            (checkpoint_root / "stderr.txt").write_bytes(b"\xfestderr")
            problem_digest = sha256(checkpoint_root / "Problem.v")
            write_json(
                checkpoint_root / "invocation.json",
                {
                    "sequence": 0,
                    "mode": "problem",
                    "candidatePath": "Problem.v",
                    "purpose": "assembly",
                    "candidateSha256": problem_digest,
                    "compilePassed": True,
                    "problemCompilePassed": True,
                    "compileCheckpointAdvanced": True,
                    "stdoutSha256": sha256(checkpoint_root / "stdout.txt"),
                    "stderrSha256": sha256(checkpoint_root / "stderr.txt"),
                    "requestedTimeoutSeconds": 420,
                    "effectiveTimeoutSeconds": 420,
                    "startedAtUnixMs": 1,
                    "elapsedMs": 500_000,
                    "exitCode": 0,
                    "timedOut": False,
                },
            )
            binding = {
                "workspaceGeneration": 1,
                "path": checkpoint_root.joinpath("Problem.v")
                .relative_to(case)
                .as_posix(),
                "sha256": problem_digest,
                "round": 0,
                "sequence": 0,
            }
            _, _, _, checkpoint_warning = validate_checkpoint(
                "fixture", evidence_root, 1, binding
            )
            self.assertEqual(
                checkpoint_warning["phase"], "initial_problem_compile"
            )

            preflight_root = generation_root / "trusted-environment-preflight"
            preflight_root.mkdir()
            (preflight_root / "stdout.txt").write_bytes(b"\xffpreflight")
            (preflight_root / "stderr.txt").write_bytes(b"")
            preflight = {
                "timeoutSeconds": 420,
                "elapsedMs": 500_000,
                "exitCode": 0,
                "timedOut": False,
            }
            write_json(preflight_root / "invocation.json", preflight)
            _, _, preflight_warning = validate_preflight(
                "fixture", evidence_root, 1, preflight
            )
            self.assertEqual(
                preflight_warning["phase"], "trusted_environment_preflight"
            )
            final_warning = make_warning(
                phase="final_trusted_check",
                timeout_seconds=420,
                elapsed_ms=500_000,
                round_number=2,
            )
            self.assertEqual(
                validate_warnings(
                    [preflight_warning, checkpoint_warning, final_warning],
                    "fixture trusted warnings",
                )[-1]["phase"],
                "final_trusted_check",
            )

    def test_trusted_cache_accepts_manifest_bound_proof_modules(self) -> None:
        publisher = runpy.run_path(str(PUBLISHER), run_name="publisher_module_cache")
        validate = publisher["validate_trusted_diagnostic_cache"]
        publish_error = publisher["PublishError"]
        with tempfile.TemporaryDirectory(prefix="logos-module-cache-") as raw:
            case = Path(raw) / "case"
            manifest, _ = make_diagnostic_cache(case)
            formal_module_root = case / "proof-stage/formal-sql/ProofModules"
            formal_module_root.mkdir()
            module_source = formal_module_root / "CheckedFacts.v"
            module_source.write_text(
                "Lemma checked_fact : True. Proof. exact I. Qed.\n", encoding="utf-8"
            )
            cache_root = manifest.parent
            cache_module_root = cache_root / "ProofModules"
            (cache_module_root / "ORDER").write_text("CheckedFacts.v\n")
            shutil.copyfile(module_source, cache_module_root / "CheckedFacts.v")
            (cache_module_root / "CheckedFacts.vo").write_bytes(b"compiled facts\n")
            entries = (
                "Schema.v",
                "Schema.vo",
                "Queries.v",
                "Queries.vo",
                "Witness.v",
                "Witness.vo",
                "ProofModules/ORDER",
                "ProofModules/CheckedFacts.v",
                "ProofModules/CheckedFacts.vo",
            )
            manifest.write_text(
                "".join(f"{sha256(cache_root / name)}  {name}\n" for name in entries),
                encoding="utf-8",
            )
            config = {
                "diagnosticCacheManifestPath": (
                    "proof-stage/proof-agent/trusted-diagnostic-cache/SHA256SUMS"
                ),
                "diagnosticCacheManifestSha256": sha256(manifest),
            }
            _, _, observed = validate("fixture", case, config)
            self.assertEqual(observed, entries)
            archive_root = (
                case
                / "proof-stage/proof-agent/workspace-generations/0001/trusted-diagnostic-cache"
            )
            shutil.copytree(cache_root, archive_root)
            historical_root = case / "proof-stage/proof-agent/rounds/01/checked-workspace"
            (historical_root / "ProofModules").mkdir(parents=True)
            for name in ("Schema.v", "Queries.v", "Witness.v"):
                shutil.copyfile(case / "proof-stage/formal-sql" / name, historical_root / name)
            shutil.copyfile(
                module_source, historical_root / "ProofModules/CheckedFacts.v"
            )
            archive_binding = {
                "workspaceGeneration": 1,
                "manifestPath": (
                    "proof-stage/proof-agent/workspace-generations/0001/"
                    "trusted-diagnostic-cache/SHA256SUMS"
                ),
                "manifestSha256": sha256(archive_root / "SHA256SUMS"),
            }
            _, _, archived_entries = validate(
                "fixture",
                case,
                config,
                cache_binding=archive_binding,
                authoritative_root=historical_root,
            )
            self.assertEqual(archived_entries, entries)
            (archive_root / "ProofModules/CheckedFacts.vo").write_bytes(b"tampered")
            with self.assertRaisesRegex(publish_error, "manifest is noncanonical"):
                validate(
                    "fixture",
                    case,
                    config,
                    cache_binding=archive_binding,
                    authoritative_root=historical_root,
                )
            (cache_module_root / "ORDER").write_text("bad-name.v\n")
            with self.assertRaisesRegex(publish_error, "invalid entry"):
                validate("fixture", case, config)

    def test_round_context_snapshot_is_manifest_bound(self) -> None:
        publisher = runpy.run_path(str(PUBLISHER), run_name="publisher_context_snapshot")
        validate = publisher["validate_context_snapshot"]
        validate_report = publisher["validate_final_context_report"]
        publish_error = publisher["PublishError"]
        with tempfile.TemporaryDirectory(prefix="logos-context-snapshot-") as raw:
            root = Path(raw)
            formal = root / "formal"
            formal.mkdir()
            for name in ("Schema.v", "Queries.v", "Witness.v"):
                (formal / name).write_text(f"Definition {name[:-2]} := True.\n")
            source = root / "source.sql"
            target = root / "target.sql"
            source.write_text("SELECT 1;\n")
            target.write_text("SELECT 1;\n")
            context = make_proof_context(
                formal, source, target, "outcome_unconditional"
            )
            selected = validate(
                "fixture",
                formal,
                context["manifestSha256"],
                "outcome_unconditional",
                "round one",
            )
            self.assertIn((formal / "Witness.v").resolve(), selected)
            self.assertIn(
                (formal / "context-manifest.json").resolve(),
                validate_report(
                    "fixture",
                    formal,
                    context,
                    "outcome_unconditional",
                    300,
                ),
            )
            (formal / "Witness.v").write_text("Definition tampered := False.\n")
            with self.assertRaisesRegex(publish_error, "witnessModule drifted"):
                validate(
                    "fixture",
                    formal,
                    context["manifestSha256"],
                    "outcome_unconditional",
                    "round one",
                )

    def test_module_identity_and_late_publication_are_accepted_fail_closed(self) -> None:
        publisher = runpy.run_path(str(PUBLISHER), run_name="publisher_late_module")
        validate_identity = publisher["validate_diagnostic_identity"]
        expected_compile = publisher["expected_diagnostic_compile_passed"]
        publish_error = publisher["PublishError"]
        with tempfile.TemporaryDirectory(prefix="logos-late-module-") as raw:
            module = Path(raw) / "CheckedFacts.v"
            module.write_text(
                "Lemma checked_fact : True. Proof. exact I. Qed.\n", encoding="utf-8"
            )
            trusted_module = Path(raw) / "trusted-CheckedFacts.v"
            shutil.copyfile(module, trusted_module)
            digest = sha256(module)
            validate_identity(
                "module",
                "ProofModules/CheckedFacts.v",
                "static-obligation",
                digest,
                "fixture",
            )
            passed, late = expected_compile(
                mode="module",
                exit_code=137,
                timed_out=True,
                error=None,
                reported_compile_passed=True,
                durable_module_path=module,
                trusted_cache_module_path=trusted_module,
                candidate_sha256=digest,
            )
            self.assertTrue(passed)
            self.assertTrue(late)
            module.write_text("Lemma tampered : False.\n", encoding="utf-8")
            passed, late = expected_compile(
                mode="module",
                exit_code=137,
                timed_out=True,
                error=None,
                reported_compile_passed=True,
                durable_module_path=module,
                trusted_cache_module_path=trusted_module,
                candidate_sha256=digest,
            )
            self.assertFalse(passed)
            self.assertFalse(late)
            with self.assertRaisesRegex(publish_error, "UppercaseRocqIdentifier"):
                validate_identity(
                    "module",
                    "ProofModules/lowercase.v",
                    "static-obligation",
                    digest,
                    "fixture",
                )


class CanonicalPublisherTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.temporary = tempfile.TemporaryDirectory(prefix="logos-publisher-test-")
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.root = Path(cls.temporary.name)
        cls.full_run = cls.root / "full-run"
        cls.output = cls.root / "FinalExperiment/Logos"
        cls.source_root = cls.root / "source-tree"
        cls.full_run.mkdir()
        cls.output.mkdir(parents=True)
        cls.source_root.mkdir()

        cohort = json.loads(COHORT_AUTHORITY.read_text(encoding="utf-8"))
        cls.raw_cases = cohort["cases"]
        if (len(cls.raw_cases), len(set(cls.raw_cases))) != (389, 389):
            raise AssertionError("benchmark authority is not 389 unique cases")
        cls.inputs = discover_inputs()
        if set(cls.inputs) != set(cls.raw_cases):
            raise AssertionError("generated inputs do not match the frozen cohort")
        write_json(cls.output / "audit.json", {"schemaVersion": 1, "status": "passed"})

        subprocess.run(
            ["git", "-C", str(cls.source_root), "init", "--quiet"], check=True
        )
        subprocess.run(
            [
                "git",
                "-C",
                str(cls.source_root),
                "config",
                "user.name",
                "Publisher Fixture",
            ],
            check=True,
        )
        subprocess.run(
            [
                "git",
                "-C",
                str(cls.source_root),
                "config",
                "user.email",
                "publisher@example.invalid",
            ],
            check=True,
        )
        cls.source_file = cls.source_root / "source.py"
        cls.source_file.write_text("value = 1\n", encoding="utf-8")
        bound_source_paths = (
            "scripts/logos_source_tree_digest.py",
            "scripts/logos_env.py",
            "benchmarks/scripts/run-logos",
        )
        for relative in bound_source_paths:
            destination = cls.source_root / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(LOGOS_ROOT / relative, destination)
        subprocess.run(
            [
                "git",
                "-C",
                str(cls.source_root),
                "add",
                "source.py",
                *bound_source_paths,
            ],
            check=True,
        )
        subprocess.run(
            [
                "git",
                "-C",
                str(cls.source_root),
                "commit",
                "--quiet",
                "-m",
                "fixture",
            ],
            check=True,
        )
        source_document = build_source_tree_manifest(cls.source_root)
        cls.source_manifest = cls.full_run / "framework-source-tree-manifest.json"
        cls.source_manifest.write_bytes(source_tree_manifest_bytes(source_document))
        cls.source_digest = source_tree_manifest_sha256(source_document)

        cls.solver_binary = cls.root / "logos-solver"
        cls.solver_binary.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
        cls.solver_binary.chmod(0o755)
        cls.solver_digest = sha256(cls.solver_binary)
        cls.trusted_manifest = cls.full_run / "trusted-stack-manifest.json"
        trusted_executable = {
            "path": str(cls.solver_binary),
            "sha256": cls.solver_digest,
            "bytes": cls.solver_binary.stat().st_size,
        }
        cls.trusted_executable = trusted_executable
        trusted_executable_names = (
            "rocq",
            "rocqchk",
            "rocqworker",
            "rocqnative",
            "bwrap",
        )
        trusted_executables = {
            name: dict(trusted_executable) for name in trusted_executable_names
        }
        trusted_executables["bwrap"] = {
            **trusted_executable,
            "path": "/Anaconda/bin/bwrap",
            "selectionPolicy": "first-executable-in-trusted-checker-path-v1",
            "searchPath": "/Anaconda/bin:/usr/bin:/bin",
            "selectedPath": "/Anaconda/bin/bwrap",
            "selectedPathIsSymlink": False,
        }
        cls.trusted_executables = trusted_executables
        trusted_host_tool_names = (
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
        dynamic_files = [
            {
                "mountPath": "/lib/libc.so.6",
                "sourcePath": "/fixture/libc.so.6",
                "sha256": "3" * 64,
                "bytes": 1,
            },
            {
                "mountPath": "/lib64/ld-linux-x86-64.so.2",
                "sourcePath": "/fixture/ld-linux-x86-64.so.2",
                "sha256": "4" * 64,
                "bytes": 1,
            },
        ]
        host_tool_records = []
        for name in trusted_host_tool_names:
            selected_path = f"/usr/bin/{name}"
            tool = {
                "name": name,
                "selectedPath": selected_path,
                "resolvedPath": selected_path,
                "selectedPathIsSymlink": False,
                "format": "script" if name == "ldd" else "elf",
                "sha256": cls.solver_digest,
                "bytes": cls.solver_binary.stat().st_size,
            }
            if name == "ldd":
                tool["sha256"] = TRUSTED_LDD_SHA256
                tool["scriptInterpreter"] = {
                    "path": "/bin/bash",
                    "resolvedPath": "/usr/bin/bash",
                    "hostTool": "bash",
                    "sha256": cls.solver_digest,
                }
            host_tool_records.append(tool)
        inspection_environment = {
            "policy": "clear-then-fixed-allowlist-v1",
            "parentEnvironmentInherited": False,
            "workingDirectory": "/",
            "allowedVariableCount": 3,
            "allowedVariables": [
                {"name": "LANG", "value": "C"},
                {"name": "LC_ALL", "value": "C"},
                {"name": "PATH", "value": "/usr/bin:/bin"},
            ],
        }
        ldd_runtime_loaders = {
            "algorithm": "logos-ldd-literal-rtldlist-closure-v1",
            "declaration": "RTLDLIST",
            "selectionPolicy": "ordered-first-present-compatible-loader-v1",
            "candidateCount": 3,
            "presentCandidateCount": 2,
            "absentCandidateCount": 1,
            "candidates": [
                {
                    "ordinal": 1,
                    "selectedPath": "/lib/ld-linux.so.2",
                    "state": "present",
                    "selectedPathIsSymlink": True,
                    "selectedPathSymlinkTarget": "/lib32/ld-linux.so.2",
                    "resolvedPath": "/usr/lib32/ld-linux.so.2",
                    "resolvedMode": "0755",
                    "sha256": (
                        "8bfac642322e3e03bbf5cb7f8ffed50e"
                        "e8a8119f0ce7d9da9dd54cb961436abf"
                    ),
                    "bytes": 1,
                    "executableCheckPassed": True,
                    "elfCheck": {"passed": True, "magicHex": "7f454c46"},
                },
                {
                    "ordinal": 2,
                    "selectedPath": "/lib64/ld-linux-x86-64.so.2",
                    "state": "present",
                    "selectedPathIsSymlink": True,
                    "selectedPathSymlinkTarget": (
                        "/lib/x86_64-linux-gnu/ld-linux-x86-64.so.2"
                    ),
                    "resolvedPath": ("/usr/lib/x86_64-linux-gnu/ld-linux-x86-64.so.2"),
                    "resolvedMode": "0755",
                    "sha256": (
                        "db61dfe5ac2fb5522cc111df698146d1"
                        "87b13cbfb73684f190f58217b8dbeec4"
                    ),
                    "bytes": 1,
                    "executableCheckPassed": True,
                    "elfCheck": {"passed": True, "magicHex": "7f454c46"},
                },
                {
                    "ordinal": 3,
                    "selectedPath": "/libx32/ld-linux-x32.so.2",
                    "state": "absent",
                },
            ],
        }

        def system_file(path: str, digest_character: str) -> dict[str, object]:
            return {
                "selectedPath": path,
                "state": "present",
                "selectedPathIsSymlink": False,
                "selectedPathSymlinkTarget": None,
                "resolvedPath": path,
                "resolvedMode": "0644",
                "sha256": digest_character * 64,
                "bytes": 1,
            }

        system_resolver_configuration = {
            "algorithm": "logos-system-dynamic-loader-config-closure-v1",
            "selectionPolicy": "fixed-system-dynamic-loader-paths-v1",
            "pathCount": 2,
            "presentPathCount": 1,
            "absentPathCount": 1,
            "paths": [
                system_file("/etc/ld.so.cache", "7"),
                {"selectedPath": "/etc/ld.so.preload", "state": "absent"},
            ],
        }
        system_identity_configuration = {
            "algorithm": "logos-system-identity-config-closure-v1",
            "selectionPolicy": "fixed-system-identity-paths-v1",
            "pathCount": 2,
            "presentPathCount": 2,
            "absentPathCount": 0,
            "paths": [
                {
                    "path": "/etc/nsswitch.conf",
                    "present": True,
                    "resolvedPath": "/etc/nsswitch.conf",
                    "sha256": "8" * 64,
                    "bytes": 1,
                },
                {
                    "path": "/etc/passwd",
                    "present": True,
                    "resolvedPath": "/etc/passwd",
                    "sha256": "9" * 64,
                    "bytes": 1,
                },
            ],
        }
        trusted_document = {
            "schemaVersion": 4,
            "algorithm": TRUSTED_STACK_MANIFEST_ALGORITHM,
            "rocqOpamSwitch": "fixture",
            "executables": trusted_executables,
            "dynamicLinking": {
                "algorithm": TRUSTED_DYNAMIC_LINKING_ALGORITHM,
                "consumerCount": len(trusted_executable_names),
                "consumers": [
                    {
                        "name": name,
                        "executableSha256": cls.solver_digest,
                        "interpreterMountPath": "/lib64/ld-linux-x86-64.so.2",
                        "dependencyMountPaths": [
                            "/lib/libc.so.6",
                            "/lib64/ld-linux-x86-64.so.2",
                        ],
                    }
                    for name in trusted_executable_names
                ],
                "fileCount": len(dynamic_files),
                "files": dynamic_files,
            },
            "trustedHostTools": {
                "selectionPolicy": "first-executable-in-sanitized-path-v1",
                "searchPath": "/fixture/_opam/bin:/usr/bin:/bin",
                "toolCount": len(trusted_host_tool_names),
                "tools": host_tool_records,
                "inspectionEnvironment": inspection_environment,
                "lddRuntimeLoaders": ldd_runtime_loaders,
                "systemResolverConfiguration": system_resolver_configuration,
                "systemIdentityConfiguration": system_identity_configuration,
                "dynamicLinking": {
                    "algorithm": TRUSTED_DYNAMIC_LINKING_ALGORITHM,
                    "consumerCount": len(trusted_host_tool_names) - 1,
                    "consumers": [
                        {
                            "name": name,
                            "executableSha256": cls.solver_digest,
                            "interpreterMountPath": "/lib64/ld-linux-x86-64.so.2",
                            "dependencyMountPaths": [
                                "/lib/libc.so.6",
                                "/lib64/ld-linux-x86-64.so.2",
                            ],
                        }
                        for name in trusted_host_tool_names
                        if name != "ldd"
                    ],
                    "fileCount": len(dynamic_files),
                    "files": dynamic_files,
                },
            },
            "trustedScripts": [{"path": "fixture.sh", "sha256": "d" * 64, "bytes": 1}],
            "sourceObjects": [
                {
                    "sourcePath": "Fixture.v",
                    "sourceSha256": "e" * 64,
                    "sourceBytes": 1,
                    "objectPath": "Fixture.vo",
                    "objectSha256": "f" * 64,
                    "objectBytes": 1,
                }
            ],
            "rocqStdlib": {
                "root": "fixture",
                "objectCount": 1,
                "objects": [{"path": "Init.vo", "sha256": "1" * 64, "bytes": 1}],
            },
            "rocqRuntime": {
                "root": "fixture",
                "componentCount": 1,
                "components": [{"path": "plugin.cmxs", "sha256": "2" * 64, "bytes": 1}],
                "configurationSelection": "nonempty-findlib-meta-conf-v1",
                "configurationCount": 2,
                "configuration": [
                    {"path": "findlib.conf", "sha256": "5" * 64, "bytes": 1},
                    {
                        "path": "rocq-runtime/META",
                        "sha256": "6" * 64,
                        "bytes": 1,
                    },
                ],
            },
        }
        cls.trusted_manifest.write_bytes(
            (
                json.dumps(trusted_document, sort_keys=True, separators=(",", ":"))
                + "\n"
            ).encode("utf-8")
        )
        cls.trusted_digest = sha256(cls.trusted_manifest)

        fixture_file = {
            "path": "fixture",
            "kind": "file",
            "sha256": "3" * 64,
            "bytes": 1,
            "executable": False,
        }
        command_component = {
            key: value for key, value in fixture_file.items() if key != "kind"
        }
        frontend_launch_environment = {
            "schemaVersion": 1,
            "inheritedEnvironmentCleared": True,
            "fixedVariables": [
                "PATH=/usr/bin:/bin",
                "HOME=/nonexistent",
                "TMPDIR=/tmp",
                "LC_ALL=C",
                "LANG=C",
                "TZ=UTC",
            ],
            "hostEnvironmentAllowlist": [],
            "explicitContractVariables": [
                "JAVA_HOME",
                "MAVEN_VERSION",
                "LOGOS_CALCITE_RUNTIME_CLASSPATH_FILE",
            ],
            "unlistedEnvironmentPolicy": ("excluded_by_env_clear_before_process_start"),
            "explicitlyExcludedVariables": FRONTEND_LAUNCH_EXCLUDED_VARIABLES,
            "explicitlyExcludedPrefixes": ["BASH_FUNC_"],
        }
        frontend_tool_paths = (
            ("bash", "/usr/bin/bash"),
            ("sh", "/bin/sh"),
            ("dirname", "/usr/bin/dirname"),
            ("readlink", "/usr/bin/readlink"),
            ("uname", "/usr/bin/uname"),
            ("mkdir", "/usr/bin/mkdir"),
            ("curl", "/usr/bin/curl"),
            ("tar", "/usr/bin/tar"),
        )
        frontend_tool_records = [
            {
                "name": name,
                "selectedPath": path,
                "resolvedPath": "/usr/bin/dash" if name == "sh" else path,
                "selectedPathIsSymlink": name == "sh",
                "selectedPathSymlinkTarget": "dash" if name == "sh" else None,
                "format": "elf",
                "sha256": cls.solver_digest,
                "bytes": cls.solver_binary.stat().st_size,
            }
            for name, path in frontend_tool_paths
        ]
        frontend_launch_tools = {
            "algorithm": "logos-sql-frontend-launch-tools-v1",
            "selectionPolicy": "fixed-absolute-paths-v1",
            "shellExecutable": "/usr/bin/bash",
            "shellArguments": ["--noprofile", "--norc", "-c"],
            "commandBody": FRONTEND_LAUNCH_COMMAND_BODY,
            "scriptArgument": "scripts/calcite-ir",
            "toolCount": len(frontend_tool_paths),
            "frozenDirectJavaToolNames": ["bash", "dirname", "readlink"],
            "frontendPreparationToolNames": [name for name, _ in frontend_tool_paths],
            "tools": frontend_tool_records,
            "dynamicLinking": {
                "algorithm": TRUSTED_DYNAMIC_LINKING_ALGORITHM,
                "consumerCount": len(frontend_tool_paths),
                "consumers": [
                    {
                        "name": name,
                        "executableSha256": cls.solver_digest,
                        "interpreterMountPath": "/lib64/ld-linux-x86-64.so.2",
                        "dependencyMountPaths": [
                            "/lib/libc.so.6",
                            "/lib64/ld-linux-x86-64.so.2",
                        ],
                    }
                    for name, _ in frontend_tool_paths
                ],
                "fileCount": len(dynamic_files),
                "files": dynamic_files,
            },
        }
        cls.frontend_manifest = cls.full_run / "frontend-stack-manifest.json"
        frontend_document = {
            "schemaVersion": 2,
            "algorithm": FRONTEND_STACK_MANIFEST_ALGORITHM,
            "canonicalCommand": CANONICAL_FRONTEND_COMMAND,
            "effectiveCommand": CANONICAL_FRONTEND_COMMAND,
            "executionMode": "direct-java-bound-classpath-v1",
            "sourceSqlTransport": "exact-input-bytes-v1",
            "normalizationLayer": "none",
            "launchEnvironmentAlgorithm": ("logos-sql-frontend-launch-environment-v1"),
            "launchEnvironment": frontend_launch_environment,
            "launchTools": frontend_launch_tools,
            "commandComponents": [command_component],
            "java": {
                "javaHome": "fixture-java",
                "jdkRoot": "fixture-jdk",
                "javaInvocationPath": "fixture-java/bin/java",
                "javaExecutable": trusted_executable,
                "version": "openjdk version 17.0.18",
                "files": [fixture_file],
            },
            "maven": {
                "root": "fixture-maven",
                "executable": trusted_executable,
                "version": "Apache Maven 3.9.11",
                "files": [fixture_file],
                "settings": {
                    "path": "/nonexistent/.m2/settings.xml",
                    "present": False,
                    "sha256": None,
                    "bytes": None,
                },
            },
            "calcite": {
                "classesRoot": "fixture-classes",
                "classCount": 1,
                "classes": [fixture_file],
                "classpathPath": "fixture-classpath.txt",
                "runtimeClasspathEnvironmentVariable": "LOGOS_CALCITE_RUNTIME_CLASSPATH_FILE",
                "classpathSha256": "4" * 64,
                "classpath": ["fixture.jar"],
                "dependencyCount": 1,
                "dependencies": [
                    {
                        "classpathIndex": 0,
                        "path": "fixture.jar",
                        "sha256": "5" * 64,
                        "bytes": 1,
                    }
                ],
            },
        }
        write_canonical_json(cls.frontend_manifest, frontend_document)
        cls.frontend_digest = sha256(cls.frontend_manifest)
        cls.frontend_record = {
            "manifestPath": str(cls.frontend_manifest),
            "manifestSha256": cls.frontend_digest,
            "manifestSchemaVersion": 2,
            "algorithm": FRONTEND_STACK_MANIFEST_ALGORITHM,
            "canonicalCommand": CANONICAL_FRONTEND_COMMAND,
            "effectiveCommand": CANONICAL_FRONTEND_COMMAND,
            "executionMode": "direct-java-bound-classpath-v1",
            "sourceSqlTransport": "exact-input-bytes-v1",
            "normalizationLayer": "none",
            "launchEnvironmentAlgorithm": ("logos-sql-frontend-launch-environment-v1"),
            "launchEnvironmentPolicy": ("excluded_by_env_clear_before_process_start"),
            "launchEnvironmentVariableCount": 9,
            "launchToolCount": 8,
            "launchToolDynamicLinkingAlgorithm": (TRUSTED_DYNAMIC_LINKING_ALGORITHM),
            "launchToolDynamicRuntimeFileCount": len(dynamic_files),
            "javaVersion": "openjdk version 17.0.18",
            "mavenVersion": "Apache Maven 3.9.11",
            "calciteClassCount": 1,
            "dependencyCount": 1,
        }

        cls.codex_config = cls.full_run / "codex-provider-config.toml"
        cls.codex_config.write_text(
            'model = "gpt-5.6-sol"\n'
            'model_reasoning_effort = "medium"\n'
            'model_provider = "fixture"\n'
            'preferred_auth_method = "apikey"\n\n'
            '[model_providers."fixture"]\n'
            'name = "Fixture"\n'
            'base_url = "http://127.0.0.1:2455/backend-api/codex"\n'
            'wire_api = "responses"\n'
            "supports_websockets = false\n"
            "requires_openai_auth = true\n",
            encoding="utf-8",
        )
        cls.codex_config_digest = sha256(cls.codex_config)
        endpoint = {
            "providerId": "fixture",
            "name": "Fixture",
            "baseUrl": "http://127.0.0.1:2455/backend-api/codex",
            "baseUrlSha256": hashlib.sha256(
                b"http://127.0.0.1:2455/backend-api/codex"
            ).hexdigest(),
            "scheme": "http",
            "host": "127.0.0.1",
            "port": 2455,
            "path": "/backend-api/codex",
            "wireApi": "responses",
            "supportsWebsockets": False,
            "requiresOpenaiAuth": True,
        }
        cls.endpoint_digest = hashlib.sha256(
            json.dumps(endpoint, sort_keys=True, separators=(",", ":")).encode()
        ).hexdigest()
        codex_executable = {
            "path": "/fixture/codex.js",
            "sha256": cls.solver_digest,
            "bytes": cls.solver_binary.stat().st_size,
        }
        codex_lexical_wrapper = {
            "path": "/fixture/bin/codex",
            "kind": "symlink",
            "symlinkTarget": "../codex.js",
            "resolvedPath": "/fixture/codex.js",
            "sha256": cls.solver_digest,
            "bytes": cls.solver_binary.stat().st_size,
        }
        node_executable = {
            "path": "/fixture/node/bin/node",
            "sha256": cls.solver_digest,
            "bytes": cls.solver_binary.stat().st_size,
        }
        node_lexical_executable = {
            "path": "/fixture/node/bin/node",
            "kind": "file",
            "symlinkTarget": None,
            "resolvedPath": "/fixture/node/bin/node",
            "sha256": cls.solver_digest,
            "bytes": cls.solver_binary.stat().st_size,
        }
        env_tool = {
            "name": "env",
            "selectedPath": "/usr/bin/env",
            "resolvedPath": "/usr/bin/env",
            "selectedPathIsSymlink": False,
            "selectedPathSymlinkTarget": None,
            "format": "elf",
            "sha256": cls.solver_digest,
            "bytes": cls.solver_binary.stat().st_size,
        }
        node_tool = {
            "name": "node",
            "selectedPath": "/fixture/node/bin/node",
            "resolvedPath": "/fixture/node/bin/node",
            "selectedPathIsSymlink": False,
            "selectedPathSymlinkTarget": None,
            "format": "elf",
            "sha256": cls.solver_digest,
            "bytes": cls.solver_binary.stat().st_size,
        }
        solver_path = {
            "algorithm": "logos-codex-solver-path-v1",
            "value": "/fixture/bin:/fixture/node/bin:/usr/bin:/bin",
            "directoryCount": 4,
            "directories": [
                {
                    "ordinal": 1,
                    "role": "codexLexicalWrapper",
                    "path": "/fixture/bin",
                    "boundExecutableSha256": cls.solver_digest,
                },
                {
                    "ordinal": 2,
                    "role": "nodeLexicalExecutable",
                    "path": "/fixture/node/bin",
                    "boundExecutableSha256": cls.solver_digest,
                },
                {
                    "ordinal": 3,
                    "role": "systemTools",
                    "path": "/usr/bin",
                    "boundExecutableSha256": None,
                },
                {
                    "ordinal": 4,
                    "role": "systemTools",
                    "path": "/bin",
                    "boundExecutableSha256": None,
                },
            ],
        }
        command_shell = {
            "shellExecutable": "/usr/bin/bash",
            "shellArguments": ["--noprofile", "--norc", "-c"],
        }
        command_environment_policy = {
            "schemaVersion": 1,
            "inheritedEnvironmentCleared": True,
            "fixedVariables": [
                "HOME=/nonexistent",
                "TMPDIR=/tmp",
                "LC_ALL=C",
                "LANG=C",
                "TZ=UTC",
            ],
            "hostEnvironmentAllowlist": [
                "PATH",
                "CODEX_HOME",
                "LOGOS_SOLVER_CODEX_HOME",
                "LOGOS_SOLVER_CODEX_CONFIG",
            ],
            "explicitContractVariables": ["LOGOS_PROPOSAL_JSON"],
            "unlistedEnvironmentPolicy": ("excluded_by_env_clear_before_process_start"),
            "explicitlyExcludedVariables": SOLVER_LAUNCH_EXCLUDED_VARIABLES,
            "explicitlyExcludedPrefixes": ["BASH_FUNC_"],
        }
        cls.codex_manifest = cls.full_run / "codex-provider-manifest.json"
        codex_document = {
            "schemaVersion": 1,
            "algorithm": CODEX_PROVIDER_MANIFEST_ALGORITHM,
            "config": {
                "path": "codex-provider-config.toml",
                "sha256": cls.codex_config_digest,
                "bytes": cls.codex_config.stat().st_size,
                "kind": "sanitized-minimal-nonsecret-codex-config",
            },
            "model": "gpt-5.6-sol",
            "reasoningEffort": "medium",
            "endpoint": endpoint,
            "hostCodexCli": {
                "invocationPath": "/fixture/bin/codex",
                "lexicalWrapper": codex_lexical_wrapper,
                "executable": codex_executable,
                "version": "codex-cli 0.145.0-fixture",
                "node": {
                    "invocationPath": "/fixture/node/bin/node",
                    "lexicalExecutable": node_lexical_executable,
                    "executable": node_executable,
                    "version": "v22.0.0-fixture",
                },
                "interpreterChain": {
                    "shebang": "#!/usr/bin/env node",
                    "envExecutable": env_tool,
                    "nodeExecutable": node_tool,
                    "dynamicLinking": {
                        "algorithm": TRUSTED_DYNAMIC_LINKING_ALGORITHM,
                        "consumerCount": 2,
                        "consumers": [
                            {
                                "name": name,
                                "executableSha256": cls.solver_digest,
                                "interpreterMountPath": ("/lib64/ld-linux-x86-64.so.2"),
                                "dependencyMountPaths": [
                                    "/lib/libc.so.6",
                                    "/lib64/ld-linux-x86-64.so.2",
                                ],
                            }
                            for name in ("env", "node")
                        ],
                        "fileCount": len(dynamic_files),
                        "files": dynamic_files,
                    },
                },
                "packageRoot": "fixture-codex-package",
                "packageFiles": [fixture_file],
                "solverPath": solver_path,
            },
            "commandShell": command_shell,
            "commandEnvironmentPolicy": command_environment_policy,
            "commands": {
                "counterexample": DEFAULT_COUNTEREXAMPLE_COMMAND,
                "proofAgent": DEFAULT_PROOF_AGENT_COMMAND,
                "proofAgentResume": DEFAULT_PROOF_AGENT_RESUME_COMMAND,
            },
        }
        write_canonical_json(cls.codex_manifest, codex_document)
        cls.codex_digest = sha256(cls.codex_manifest)
        cls.codex_record = {
            "manifestPath": str(cls.codex_manifest),
            "manifestSha256": cls.codex_digest,
            "algorithm": CODEX_PROVIDER_MANIFEST_ALGORITHM,
            "configPath": str(cls.codex_config),
            "configSha256": cls.codex_config_digest,
            "configBytes": cls.codex_config.stat().st_size,
            "model": "gpt-5.6-sol",
            "reasoningEffort": "medium",
            "endpoint": endpoint,
            "endpointSha256": cls.endpoint_digest,
            "hostCodexVersion": "codex-cli 0.145.0-fixture",
            "hostCodexInvocationPath": "/fixture/bin/codex",
            "hostCodexLexicalWrapper": codex_lexical_wrapper,
            "hostCodexNodeInvocationPath": "/fixture/node/bin/node",
            "solverPath": solver_path,
            "commandShell": command_shell,
            "commandEnvironmentPolicy": command_environment_policy,
            "commands": codex_document["commands"],
        }

        cls.postgres_manifest = cls.full_run / "postgres-server-profile.json"
        postgres_profile = {
            "serverVersion": "17.4",
            "serverVersionNum": "170004",
            "databaseCollation": "C",
            "databaseCharacterClassification": "C",
            "localeProvider": "libc",
            "serverEncoding": "UTF8",
            "timeZone": "UTC",
            "maxConnections": "96",
        }
        postgres_url_digest = "a" * 64
        postgres_document = {
            "schemaVersion": 1,
            "algorithm": POSTGRES_PROFILE_MANIFEST_ALGORITHM,
            "configured": True,
            "urlSha256": postgres_url_digest,
            "psql": {
                "executable": trusted_executable,
                "version": "psql (PostgreSQL) 17.4",
            },
            "profile": postgres_profile,
        }
        write_canonical_json(cls.postgres_manifest, postgres_document)
        cls.postgres_digest = sha256(cls.postgres_manifest)
        cls.postgres_record = {
            "manifestPath": str(cls.postgres_manifest),
            "manifestSha256": cls.postgres_digest,
            "algorithm": POSTGRES_PROFILE_MANIFEST_ALGORITHM,
            "configured": True,
            "urlSha256": postgres_url_digest,
            "profile": postgres_profile,
            "psql": postgres_document["psql"],
        }

        manifest_bytes = frozen_input_manifest(cls.inputs)
        if hashlib.sha256(manifest_bytes).hexdigest() != FROZEN_INPUT_MANIFEST_SHA256:
            raise AssertionError("frozen generated inputs have drifted")
        cls.input_manifest = cls.full_run / "frozen-input-manifest.json"
        cls.selected_input_manifest = cls.full_run / "selected-input-manifest.json"
        cls.input_manifest.write_bytes(manifest_bytes)
        cls.selected_input_manifest.write_bytes(manifest_bytes)
        image_id = "sha256:" + "b" * 64
        sql_environment = {
            "timeZone": "UTC",
            "defaultCollation": "C",
            "characterClassification": "C",
            "localeProvider": "libc",
            "serverEncoding": "UTF8",
        }
        postgres_url = {"configured": True, "sha256": "a" * 64}
        solver_launch_environment_policy = {
            "schemaVersion": 1,
            "inheritedEnvironmentCleared": True,
            "fixedVariables": [
                f"PATH={solver_path['value']}",
                "HOME=/nonexistent",
                "TMPDIR=/tmp",
                "LC_ALL=C",
                "LANG=C",
                "TZ=UTC",
            ],
            "hostEnvironmentAllowlist": [],
            "explicitContractVariables": [
                "CODEX_HOME",
                "LOGOS_SOLVER_CODEX_HOME",
                "LOGOS_SOLVER_CODEX_CONFIG",
                "JAVA_HOME",
                "MAVEN_VERSION",
                "LOGOS_CALCITE_RUNTIME_CLASSPATH_FILE",
            ],
            "unlistedEnvironmentPolicy": ("excluded_by_env_clear_before_process_start"),
            "explicitlyExcludedVariables": SOLVER_LAUNCH_EXCLUDED_VARIABLES,
            "explicitlyExcludedPrefixes": ["BASH_FUNC_"],
            "codexInvocationPath": "/fixture/bin/codex",
            "nodeInvocationPath": "/fixture/node/bin/node",
            "codexSolverPathAlgorithm": "logos-codex-solver-path-v1",
        }
        solver_variable_names = sorted(
            {
                "PATH",
                "HOME",
                "TMPDIR",
                "LC_ALL",
                "LANG",
                "TZ",
                "CODEX_HOME",
                "LOGOS_SOLVER_CODEX_HOME",
                "LOGOS_SOLVER_CODEX_CONFIG",
                "JAVA_HOME",
                "MAVEN_VERSION",
                "LOGOS_CALCITE_RUNTIME_CLASSPATH_FILE",
            }
        )
        symbolic_home = "<isolated-codex-runtime-home>"
        normalized_solver_environment = {
            "PATH": solver_path["value"],
            "HOME": "/nonexistent",
            "TMPDIR": "/tmp",
            "LC_ALL": "C",
            "LANG": "C",
            "TZ": "UTC",
            "CODEX_HOME": symbolic_home,
            "LOGOS_SOLVER_CODEX_HOME": symbolic_home,
            "LOGOS_SOLVER_CODEX_CONFIG": f"{symbolic_home}/config.toml",
            "JAVA_HOME": str(
                configured_path(
                    LOGOS_ROOT,
                    "LOGOS_JAVA_HOME"
                    if os.environ.get("LOGOS_JAVA_HOME")
                    else "JAVA_HOME",
                    required=True,
                )
            ),
            "MAVEN_VERSION": "3.9.11",
            "LOGOS_CALCITE_RUNTIME_CLASSPATH_FILE": str(
                (
                    LOGOS_ROOT
                    / "frontend/calcite-wrapper/target/logos-runtime-classpath.txt"
                ).resolve()
            ),
        }
        solver_environment = {
            "algorithm": "logos-solver-launch-environment-v1",
            "variableCount": len(solver_variable_names),
            "variableNames": solver_variable_names,
            "normalization": "isolated-codex-runtime-home-symbolic-v1",
            "sha256": hashlib.sha256(
                (
                    json.dumps(
                        normalized_solver_environment,
                        sort_keys=True,
                        separators=(",", ":"),
                    )
                    + "\n"
                ).encode()
            ).hexdigest(),
        }

        scope = json.loads(SCOPE.read_text(encoding="utf-8"))
        gate_cases = scope["ablationCases"] + scope["extensionCases"]
        manifest_document = json.loads(manifest_bytes)
        manifest_by_case = {row["caseId"]: row for row in manifest_document["cases"]}
        gate_input_document = {
            "schemaVersion": 1,
            "algorithm": INPUT_MANIFEST_ALGORITHM,
            "caseCount": 16,
            "cases": [manifest_by_case[case] for case in sorted(gate_cases)],
        }
        cls.gate_input_digest = hashlib.sha256(
            (
                json.dumps(gate_input_document, sort_keys=True, separators=(",", ":"))
                + "\n"
            ).encode("utf-8")
        ).hexdigest()
        gate_rows = []
        for case in gate_cases:
            paths = cls.inputs[case]
            input_files = {
                "schema": {
                    "path": str(paths["schema"]),
                    "sha256": sha256(paths["schema"]),
                },
                "source": {
                    "path": str(paths["source"]),
                    "sha256": sha256(paths["source"]),
                },
                "target": {
                    "path": str(paths["target"]),
                    "sha256": sha256(paths["target"]),
                },
            }
            gate_report = cls.root / "gate-cases" / case / "report.json"
            _, gate_cache_digest = make_diagnostic_cache(gate_report.parent)
            write_json(
                gate_report,
                {
                    "outcome": "outcome_unconditional",
                    "rounds": [],
                    "proof": {
                        "sqlEnvironment": {
                            key: value
                            for key, value in sql_environment.items()
                            if key != "timeZone"
                        },
                        "verificationMode": "outcome_unconditional",
                        "backendStatus": "proof_complete",
                        "certification": "OUTCOME-UNCONDITIONAL",
                        "proofAgentConfiguration": {
                            "enabled": True,
                            "catalogGuidance": True,
                            "command": DEFAULT_PROOF_AGENT_COMMAND,
                            "resumeCommand": DEFAULT_PROOF_AGENT_RESUME_COMMAND,
                            "memoryLimitMib": 6144,
                            "sessionRestartAfterFailedRounds": 16,
                            "sessionHomePolicy": "isolated_per_generation",
                            **PROOF_AGENT_DIAGNOSTIC_CONFIGURATION,
                            "diagnosticCacheManifestPath": (
                                "proof-stage/proof-agent/trusted-diagnostic-cache/"
                                "SHA256SUMS"
                            ),
                            "diagnosticCacheManifestSha256": gate_cache_digest,
                            "timeoutSeconds": 14100,
                            "trustedCheckTimeoutSeconds": 420,
                            "dockerImage": image_id,
                            "context": {
                                "sourceSqlSha256": input_files["source"]["sha256"],
                                "targetSqlSha256": input_files["target"]["sha256"],
                            },
                        },
                        "proofAgent": {
                            "proofCheckExitCode": 0,
                            "proofCheckTimedOut": False,
                            "audit": {"passed": True, "findings": []},
                        },
                    },
                },
            )
            gate_rows.append(
                {
                    "caseId": case,
                    "status": "completed",
                    "returnCode": 0,
                    "outcome": "outcome_unconditional",
                    "backendStatus": "proof_complete",
                    "certification": "OUTCOME-UNCONDITIONAL",
                    "usageComplete": True,
                    "effectiveConfiguration": {
                        "verificationMode": "outcome-unconditional",
                        "model": "gpt-5.6-sol",
                        "reasoningEffort": "medium",
                        "catalogGuidanceEnabled": True,
                        "trustedCheckTimeoutSeconds": 420,
                        "dockerImage": image_id,
                        "caseTimeoutSeconds": 14400,
                        "terminationGraceSeconds": 10.0,
                        "proofAgentTotalTimeoutSeconds": 14100,
                        "proofAgentSessionRestartAfterFailedRounds": 16,
                        "proofAgentSessionHomePolicy": "isolated_per_generation",
                        **EFFECTIVE_PROOF_AGENT_DIAGNOSTIC_CONFIGURATION,
                        "solverLaunchEnvironmentPolicy": (
                            solver_launch_environment_policy
                        ),
                        "solverEnvironment": solver_environment,
                        "frontendLaunchEnvironmentPolicy": (
                            frontend_launch_environment
                        ),
                        "commandProviderEnvironmentPolicy": (
                            command_environment_policy
                        ),
                        "resourcePolicy": {
                            "memoryLimitMiB": 6144,
                            "storageLimitMiB": 2048,
                            "cpuLimit": None,
                        },
                        "solverArgs": [],
                        "effectiveSolverArgs": ["--force-llm-assessment"],
                        "postgresUrl": postgres_url,
                        "sqlEnvironment": sql_environment,
                        "frameworkSourceTreeManifestSha256": cls.source_digest,
                        "inputManifestSha256": FROZEN_INPUT_MANIFEST_SHA256,
                        "selectedInputManifestSha256": cls.gate_input_digest,
                        "solverBinarySha256": cls.solver_digest,
                        "trustedStackManifestSha256": cls.trusted_digest,
                        "frontendStackManifestSha256": cls.frontend_digest,
                        "codexProviderManifestSha256": cls.codex_digest,
                        "codexConfigSha256": cls.codex_config_digest,
                        "providerEndpointSha256": cls.endpoint_digest,
                        "postgresServerProfileSha256": cls.postgres_digest,
                        "cohort16GateSha256": None,
                    },
                    "inputFiles": input_files,
                    "reportEvidence": {
                        "path": str(gate_report),
                        "present": True,
                        "sha256": sha256(gate_report),
                    },
                }
            )
        cls.gate_summary = cls.full_run / "cohort16-gate-summary.json"
        write_json(
            cls.gate_summary,
            {
                "schemaVersion": 1,
                "status": "complete",
                "startedAt": "2026-07-23T00:00:00Z",
                "updatedAt": "2026-07-23T01:00:00Z",
                "verificationMode": "outcome-unconditional",
                "proofAgentCatalogGuidanceEnabled": True,
                "model": "gpt-5.6-sol",
                "reasoningEffort": "medium",
                "caseTimeoutSeconds": 14400,
                "usageComplete": True,
                "configuration": {
                    "verificationMode": "outcome-unconditional",
                    "model": "gpt-5.6-sol",
                    "reasoningEffort": "medium",
                    "caseTimeoutSeconds": 14400,
                    "terminationGraceSeconds": 10.0,
                    "solverArgs": [],
                    "effectiveSolverArgs": ["--force-llm-assessment"],
                    "postgresUrl": postgres_url,
                    "sqlEnvironment": sql_environment,
                    "solverLaunchEnvironmentPolicy": (solver_launch_environment_policy),
                    "solverEnvironment": solver_environment,
                    "frontendLaunchEnvironmentPolicy": frontend_launch_environment,
                    "commandProviderEnvironmentPolicy": command_environment_policy,
                    "frameworkSourceTree": {
                        "manifestSha256": cls.source_digest,
                        "sourceTreeDigestHelper": copy.deepcopy(
                            SOURCE_TREE_DIGEST_HELPER_RECORD
                        ),
                    },
                    "solverBinary": {"sha256": cls.solver_digest},
                    "trustedStack": {"manifestSha256": cls.trusted_digest},
                    "frontendStack": {"manifestSha256": cls.frontend_digest},
                    "codexProvider": {
                        "manifestSha256": cls.codex_digest,
                        "configSha256": cls.codex_config_digest,
                        "endpointSha256": cls.endpoint_digest,
                    },
                    "postgresServerProfile": {
                        "manifestSha256": cls.postgres_digest,
                    },
                    "inputManifest": {
                        "selectedSha256": cls.gate_input_digest,
                    },
                    "proofAgent": {
                        "catalogGuidanceEnabled": True,
                        "model": "gpt-5.6-sol",
                        "reasoningEffort": "medium",
                        "sessionRestartAfterFailedRounds": 16,
                        "sessionHomePolicy": "isolated_per_generation",
                        **PROOF_AGENT_DIAGNOSTIC_CONFIGURATION,
                        "totalTimeoutSeconds": 14100,
                        "trustedCheckTimeoutSeconds": 420,
                        "resourcePolicy": {
                            "memoryLimitMiB": 6144,
                            "storageLimitMiB": 2048,
                            "cpuLimit": None,
                        },
                        "dockerImage": {"imageId": image_id},
                    },
                },
                "cases": gate_cases,
                "counts": {
                    "selected": 16,
                    "pending": 0,
                    "completed": 16,
                    "timedOut": 0,
                    "failed": 0,
                    "cancelled": 0,
                },
                "results": gate_rows,
                "integrityVerification": {
                    "verified": True,
                    "frameworkSourceTreeManifestSha256": cls.source_digest,
                    "solverBinarySha256": cls.solver_digest,
                    "trustedStackManifestSha256": cls.trusted_digest,
                    "frontendStackManifestSha256": cls.frontend_digest,
                    "codexProviderManifestSha256": cls.codex_digest,
                    "codexConfigSha256": cls.codex_config_digest,
                    "providerEndpointSha256": cls.endpoint_digest,
                    "solverEnvironmentSha256": solver_environment["sha256"],
                    "postgresServerProfileSha256": cls.postgres_digest,
                    "inputManifestSha256": FROZEN_INPUT_MANIFEST_SHA256,
                    "selectedInputManifestSha256": cls.gate_input_digest,
                    "cohort16GateSha256": None,
                },
            },
        )
        cls.gate_digest = sha256(cls.gate_summary)
        cls.scope_digest = sha256(SCOPE)
        cls.gate_case_set_digest = hashlib.sha256(
            ("\n".join(sorted(gate_cases)) + "\n").encode("utf-8")
        ).hexdigest()

        cls.final_audit = cls.root / "final-audit.json"
        write_json(
            cls.final_audit,
            {
                "schemaVersion": 1,
                "revisionId": cls.source_digest,
                "sourceTreeManifestSha256": cls.source_digest,
                "finalAudit": True,
                "passed": True,
                "independentAgentSessionId": "independent-fixture-agent",
                "unresolvedCritical": [],
                "unresolvedHigh": [],
                "checks": {
                    "fairness": True,
                    "soundness": True,
                    "sqlSemantics": True,
                    "logicalCorrectness": True,
                    "benchmarkLeakage": True,
                    "trustedBoundary": True,
                },
            },
        )

        cls.usage = {
            "model": "gpt-5.6-sol",
            "inputTokens": 11,
            "cachedInputTokens": 7,
            "outputTokens": 3,
            "totalTokens": 14,
            "estimatedCostUsd": ((11 - 7) * 5 + 7 * 0.5 + 3 * 30) / 1_000_000,
        }
        effective_configuration = {
            "verificationMode": "outcome-unconditional",
            "model": "gpt-5.6-sol",
            "reasoningEffort": "medium",
            "catalogGuidanceEnabled": True,
            "trustedCheckTimeoutSeconds": 420,
            "dockerImage": image_id,
            "caseTimeoutSeconds": 14400,
            "maxCounterexampleRounds": 3,
            "statementTimeoutSeconds": 600,
            "terminationGraceSeconds": 10.0,
            "proofAgentTotalTimeoutSeconds": 14100,
            "proofAgentSessionRestartAfterFailedRounds": 16,
            "proofAgentSessionHomePolicy": "isolated_per_generation",
            **EFFECTIVE_PROOF_AGENT_DIAGNOSTIC_CONFIGURATION,
            "solverLaunchEnvironmentPolicy": solver_launch_environment_policy,
            "solverEnvironment": solver_environment,
            "frontendLaunchEnvironmentPolicy": frontend_launch_environment,
            "commandProviderEnvironmentPolicy": command_environment_policy,
            "resourcePolicy": {
                "memoryLimitMiB": 6144,
                "storageLimitMiB": 2048,
                "cpuLimit": None,
            },
            "solverArgs": [],
            "effectiveSolverArgs": ["--force-llm-assessment"],
            "postgresUrl": postgres_url,
            "sqlEnvironment": sql_environment,
            "frameworkSourceTreeManifestSha256": cls.source_digest,
            "inputManifestSha256": FROZEN_INPUT_MANIFEST_SHA256,
            "selectedInputManifestSha256": FROZEN_INPUT_MANIFEST_SHA256,
            "solverBinarySha256": cls.solver_digest,
            "trustedStackManifestSha256": cls.trusted_digest,
            "frontendStackManifestSha256": cls.frontend_digest,
            "codexProviderManifestSha256": cls.codex_digest,
            "codexConfigSha256": cls.codex_config_digest,
            "providerEndpointSha256": cls.endpoint_digest,
            "postgresServerProfileSha256": cls.postgres_digest,
            "cohort16GateSha256": cls.gate_digest,
        }

        results = []
        cls.first_report = None
        for raw_case in cls.raw_cases:
            case_dir = cls.full_run / "cases" / raw_case
            case_dir.mkdir(parents=True)
            _, diagnostic_cache_digest = make_diagnostic_cache(case_dir)
            for name in ("stdout.log", "stderr.log"):
                (case_dir / name).write_text("", encoding="utf-8")
            (case_dir / "time.txt").write_text("elapsed_ms=1\n", encoding="utf-8")
            proof_source = case_dir / "proof-stage/formal-sql/Problem.v"
            proof_source.parent.mkdir(parents=True, exist_ok=True)
            proof_source.write_text(
                "Theorem generated_queries_verified : True. Proof. exact I. Qed.\n",
                encoding="utf-8",
            )
            initial_candidate_sha256 = sha256(proof_source)
            initial_root = (
                case_dir
                / "proof-stage/proof-agent/workspace-generations/0001/initial-problem-checkpoint"
            )
            initial_root.mkdir(parents=True)
            shutil.copyfile(proof_source, initial_root / "Problem.v")
            (initial_root / "stdout.txt").write_text("initial compile passed\n")
            (initial_root / "stderr.txt").write_text("")
            write_json(
                initial_root / "invocation.json",
                {
                    "sequence": 0,
                    "mode": "problem",
                    "candidatePath": "Problem.v",
                    "purpose": "assembly",
                    "candidateSha256": initial_candidate_sha256,
                    "compilePassed": True,
                    "problemCompilePassed": True,
                    "compileCheckpointAdvanced": True,
                    "stdoutSha256": sha256(initial_root / "stdout.txt"),
                    "stderrSha256": sha256(initial_root / "stderr.txt"),
                    "requestedTimeoutSeconds": 420,
                    "effectiveTimeoutSeconds": 420,
                    "startedAtUnixMs": 0,
                    "elapsedMs": 3,
                    "exitCode": 0,
                    "timedOut": False,
                    "error": None,
                },
            )
            preflight = {
                "timeoutSeconds": 420,
                "elapsedMs": 1,
                "exitCode": 0,
                "timedOut": False,
            }
            preflight_root = (
                case_dir
                / "proof-stage/proof-agent/workspace-generations/0001/trusted-environment-preflight"
            )
            preflight_root.mkdir(parents=True)
            (preflight_root / "stdout.txt").write_text("preflight passed\n")
            (preflight_root / "stderr.txt").write_text("")
            write_json(preflight_root / "invocation.json", preflight)
            proof_source.write_text(
                "(* agent checkpoint *)\n"
                "Theorem generated_queries_verified : True. Proof. exact I. Qed.\n",
                encoding="utf-8",
            )
            candidate_sha256 = sha256(proof_source)
            round_root = case_dir / "proof-stage/proof-agent/rounds/01"
            checked_root = round_root / "checked-workspace"
            checked_root.mkdir(parents=True)
            shutil.copyfile(proof_source, checked_root / "Problem.v")
            authority_closure = checked_root / "authority-closure.json"
            write_json(authority_closure, {"schemaVersion": 1, "files": []})
            diagnostic_root = round_root / "interactive-diagnostics/01"
            diagnostic_workspace = diagnostic_root / "checked-workspace"
            diagnostic_workspace.mkdir(parents=True)
            shutil.copyfile(proof_source, diagnostic_workspace / "Problem.v")
            (diagnostic_root / "stdout.txt").write_text("compile passed\n")
            (diagnostic_root / "stderr.txt").write_text("")
            paths = cls.inputs[raw_case]
            input_files = {
                "schema": {
                    "path": str(paths["schema"]),
                    "sha256": sha256(paths["schema"]),
                },
                "source": {
                    "path": str(paths["source"]),
                    "sha256": sha256(paths["source"]),
                },
                "target": {
                    "path": str(paths["target"]),
                    "sha256": sha256(paths["target"]),
                },
            }
            context = make_proof_context(
                proof_source.parent,
                paths["source"],
                paths["target"],
                "outcome_unconditional",
            )
            for name in (*CONTEXT_BINDING_FILES.values(), "context-manifest.json"):
                shutil.copyfile(proof_source.parent / name, checked_root / name)
            for name in ("Schema.v", "Queries.v", "Witness.v", "Goal.v"):
                shutil.copyfile(proof_source.parent / name, diagnostic_workspace / name)
            diagnostic = {
                "sequence": 1,
                "mode": "problem",
                "candidateSha256": candidate_sha256,
                "candidatePath": "Problem.v",
                "purpose": "assembly",
                "compilePassed": True,
                "problemCompilePassed": True,
                "compileCheckpointAdvanced": True,
                "stdoutSha256": sha256(diagnostic_root / "stdout.txt"),
                "stderrSha256": sha256(diagnostic_root / "stderr.txt"),
                "requestedTimeoutSeconds": 30,
                "effectiveTimeoutSeconds": 30,
                "startedAtUnixMs": 1,
                "elapsedMs": 40_000,
                "exitCode": 0,
                "timedOut": False,
            }
            write_json(
                diagnostic_root / "request.json",
                {
                    "schemaVersion": 2,
                    "nonce": "9" * 64,
                    "mode": "problem",
                    "candidatePath": "Problem.v",
                    "purpose": "assembly",
                    "candidateSha256": candidate_sha256,
                    "candidateBytes": (diagnostic_workspace / "Problem.v").stat().st_size,
                    "requestedTimeoutSeconds": 30,
                },
            )
            write_json(diagnostic_root / "invocation.json", diagnostic)
            write_json(round_root / "interactive-diagnostics.json", [diagnostic])
            accepted_audit_path = diagnostic_root / "audit.json"
            write_json(
                accepted_audit_path,
                {
                    "passed": True,
                    "scannedFiles": [
                        "proof-stage/proof-agent/rounds/01/"
                        "interactive-diagnostics/01/checked-workspace/Problem.v"
                    ],
                    "findings": [],
                },
            )
            accepted_source_audit = {
                "requestOrdinal": 1,
                "sequence": 1,
                "mode": "problem",
                "candidatePath": "Problem.v",
                "purpose": "assembly",
                "candidateSha256": candidate_sha256,
                "requestedTimeoutSeconds": 30,
                "candidate": diagnostic_artifact_binding(
                    case_dir, diagnostic_workspace / "Problem.v"
                ),
                "audit": diagnostic_artifact_binding(case_dir, accepted_audit_path),
            }
            rejected_root = round_root / "rejected-diagnostic-source-audits/02"
            rejected_root.mkdir(parents=True)
            rejected_problem_path = rejected_root / "Problem.v"
            rejected_problem_path.write_text(
                "Load forbidden_fixture.\n", encoding="utf-8"
            )
            rejected_candidate_sha256 = sha256(rejected_problem_path)
            rejected_request_path = rejected_root / "request.json"
            write_json(
                rejected_request_path,
                {
                    "schemaVersion": 2,
                    "nonce": "9" * 64,
                    "mode": "scratch",
                    "candidatePath": "scratch/rejected.v",
                    "purpose": "static-obligation",
                    "candidateSha256": rejected_candidate_sha256,
                    "candidateBytes": rejected_problem_path.stat().st_size,
                    "requestedTimeoutSeconds": 30,
                },
            )
            rejected_audit_path = rejected_root / "audit.json"
            write_json(
                rejected_audit_path,
                {
                    "passed": False,
                    "scannedFiles": [
                        "proof-stage/proof-agent/rounds/01/"
                        "interactive-diagnostics/02/checked-workspace/Problem.v"
                    ],
                    "findings": [
                        {
                            "path": (
                                "proof-stage/proof-agent/rounds/01/"
                                "interactive-diagnostics/02/"
                                "checked-workspace/Problem.v"
                            ),
                            "line": 1,
                            "token": "Load",
                            "excerpt": "Load forbidden_fixture.",
                        }
                    ],
                },
            )
            rejected_feedback_path = rejected_root / "feedback.txt"
            rejected_feedback_path.write_text(
                "interactive problem compile #2 for "
                f"{rejected_candidate_sha256} was rejected by the host deterministic "
                "source audit; the checker was not executed: Load at line 1",
                encoding="utf-8",
            )
            rejected_source_audit = {
                "requestOrdinal": 2,
                "mode": "scratch",
                "candidatePath": "scratch/rejected.v",
                "purpose": "static-obligation",
                "candidateSha256": rejected_candidate_sha256,
                "requestedTimeoutSeconds": 30,
                "problem": diagnostic_artifact_binding(case_dir, rejected_problem_path),
                "request": diagnostic_artifact_binding(case_dir, rejected_request_path),
                "audit": diagnostic_artifact_binding(case_dir, rejected_audit_path),
                "feedback": diagnostic_artifact_binding(
                    case_dir, rejected_feedback_path
                ),
            }
            report = {
                "outcome": "outcome_unconditional",
                "reason": "fixture proof accepted",
                "rounds": [],
                "counterexample": None,
                "proof": {
                    "sqlEnvironment": {
                        key: value
                        for key, value in sql_environment.items()
                        if key != "timeZone"
                    },
                    "verificationMode": "outcome_unconditional",
                    "backendStatus": "proof_complete",
                    "certification": "OUTCOME-UNCONDITIONAL",
                    "proofAgentConfiguration": {
                        "enabled": True,
                        "catalogGuidance": True,
                        "command": DEFAULT_PROOF_AGENT_COMMAND,
                        "resumeCommand": DEFAULT_PROOF_AGENT_RESUME_COMMAND,
                        "memoryLimitMib": 6144,
                        "sessionRestartAfterFailedRounds": 16,
                        "sessionHomePolicy": "isolated_per_generation",
                        **PROOF_AGENT_DIAGNOSTIC_CONFIGURATION,
                        "diagnosticCacheManifestPath": (
                            "proof-stage/proof-agent/trusted-diagnostic-cache/"
                            "SHA256SUMS"
                        ),
                        "diagnosticCacheManifestSha256": diagnostic_cache_digest,
                        "timeoutSeconds": 14100,
                        "trustedCheckTimeoutSeconds": 420,
                        "trustedEnvironmentPreflight": preflight,
                        "dockerImage": image_id,
                        "staticPromptAndPrimerBytes": 300,
                        "context": context,
                    },
                    "proofAgent": {
                        "proofCheckExitCode": 0,
                        "proofCheckElapsedMs": 2,
                        "proofCheckTimedOut": False,
                        "audit": {"passed": True, "findings": []},
                    },
                    "proofAgentRounds": [
                        {
                            "round": 1,
                            "workspaceGeneration": 1,
                            "sessionGeneration": 1,
                            "sessionRestarted": False,
                            "checkpointTransition": "newWorkspaceInitial",
                            "sessionId": "019f8c94-8ab5-7762-8e73-ee0f4f3af9de",
                            "contextManifestSha256": context["manifestSha256"],
                            "success": True,
                            "catalogGuidance": True,
                            "authorityClosurePath": (
                                "proof-stage/proof-agent/rounds/01/"
                                "checked-workspace/authority-closure.json"
                            ),
                            "authorityClosureSha256": sha256(authority_closure),
                            "authorityClosureBytes": authority_closure.stat().st_size,
                            "candidateProblemSha256": candidate_sha256,
                            "candidateProblemCompilePassed": True,
                            "candidateHasFinalTheorem": True,
                            "activeProblemCompileCheckpointSha256": initial_candidate_sha256,
                            "updatedProblemCompileCheckpointSha256": candidate_sha256,
                            "compileCheckpointRestored": False,
                            "diagnosticCheckerTelemetryPath": (
                                "proof-stage/proof-agent/rounds/01/"
                                "interactive-diagnostics.json"
                            ),
                            "diagnosticCheckerInvocations": [diagnostic],
                            "diagnosticRequestsSeen": 2,
                            "diagnosticRequestedTimeoutSecondsReserved": 60,
                            "diagnosticAcceptedCount": 1,
                            "diagnosticRejectedSourceAuditCount": 1,
                            "diagnosticOtherRejectedRequestCount": 0,
                            "diagnosticAcceptedSourceAudits": [accepted_source_audit],
                            "diagnosticRejectedSourceAudits": [rejected_source_audit],
                            "proofCheckExitCode": 0,
                            "proofCheckElapsedMs": 2,
                            "proofCheckTimeoutSeconds": 420,
                            "proofCheckTimedOut": False,
                        }
                    ],
                },
                "elapsedMs": 1,
                "llmUsage": cls.usage,
            }
            report_path = case_dir / "report.json"
            write_json(report_path, report)
            if cls.first_report is None:
                cls.first_report = report_path
            row = {
                "caseId": raw_case,
                "benchmark": "fixture",
                "inputDir": str(paths["directory"]),
                "caseDir": str(case_dir),
                "reportPath": str(report_path),
                "stdoutPath": str(case_dir / "stdout.log"),
                "stderrPath": str(case_dir / "stderr.log"),
                "status": "completed",
                "returnCode": 0,
                "elapsedMs": 1,
                "outcome": "outcome_unconditional",
                "reason": "fixture proof accepted",
                "backendStatus": "proof_complete",
                "certification": "OUTCOME-UNCONDITIONAL",
                "usageComplete": True,
                "llmUsage": cls.usage,
                "inputFiles": input_files,
                "effectiveConfiguration": effective_configuration,
                "reportEvidence": {
                    "path": str(report_path),
                    "present": True,
                    "sha256": sha256(report_path),
                },
                "proofMetrics": {
                    "proofRoundCount": 1,
                    "preflightInvocationCount": 1,
                    "preflightElapsedMs": 1,
                    "preflightGenerations": [
                        {"workspaceGeneration": 1, "elapsedMs": 1}
                    ],
                    "diagnosticInvocationCount": 1,
                    "diagnosticElapsedMs": 40_000,
                    "diagnosticElapsedWarnings": [
                        {
                            "code": (
                                "diagnostic_elapsed_exceeded_timeout_plus_"
                                "kill_margin"
                            ),
                            "round": 1,
                            "sequence": 1,
                            "requestedTimeoutSeconds": 30,
                            "effectiveTimeoutSeconds": 30,
                            "elapsedMs": 40_000,
                            "timeoutPlusKillMarginMs": 36_000,
                            "overrunMs": 4_000,
                        }
                    ],
                    "requestedTimeoutSeconds": [30],
                    "effectiveTimeoutSeconds": [30],
                    "initialProblemCompileElapsedMs": 3,
                    "initialProblemCompileTimeoutSeconds": 420,
                    "initialProblemCompileInvocationCount": 1,
                    "initialProblemCompileGenerations": [
                        {
                            "workspaceGeneration": 1,
                            "path": (
                                "proof-stage/proof-agent/workspace-generations/"
                                "0001/initial-problem-checkpoint/Problem.v"
                            ),
                            "sha256": initial_candidate_sha256,
                            "elapsedMs": 3,
                        }
                    ],
                    "finalProofCheckInvocationCount": 1,
                    "finalProofCheckElapsedTotalMs": 2,
                    "checkerInvocationCount": 4,
                    "checkerElapsedMs": 40_006,
                    "finalProofCheckElapsedMs": 2,
                    **PROOF_AGENT_BROKER_METRICS,
                    "proofSource": {
                        "path": str(proof_source),
                        "present": True,
                        "sha256": sha256(proof_source),
                        "bytes": proof_source.stat().st_size,
                    },
                    "staticPromptAndPrimerBytes": 300,
                    "queryShapeBytes": context["queryShapeBytes"],
                    "catalogBytes": 10,
                    "generatedContextBytes": 400,
                    "contextManifestBytes": context["manifestBytes"],
                },
            }
            write_json(case_dir / "runner-result.json", row)
            write_json(
                case_dir / "status.json",
                {
                    "schemaVersion": 1,
                    "caseId": raw_case,
                    "status": "completed",
                    "returnCode": 0,
                    "outcome": "outcome_unconditional",
                    "backendStatus": "proof_complete",
                    "certification": "OUTCOME-UNCONDITIONAL",
                    "runnerError": None,
                    "usageError": None,
                    "usageComplete": True,
                },
            )
            write_json(case_dir / "usage.json", cls.usage)
            results.append(row)

        configuration = {
            "inputRoot": str(INPUT_ROOT),
            "solverBin": str(cls.solver_binary),
            "jobs": 32,
            "caseTimeoutSeconds": 14400,
            "maxCounterexampleRounds": 3,
            "terminationGraceSeconds": 10.0,
            "verificationMode": "outcome-unconditional",
            "model": "gpt-5.6-sol",
            "reasoningEffort": "medium",
            "solverArgs": [],
            "effectiveSolverArgs": ["--force-llm-assessment"],
            "counterexampleAssessmentPolicy": "force-fresh",
            "postgresUrl": postgres_url,
            "sqlEnvironment": sql_environment,
            "solverLaunchEnvironmentPolicy": solver_launch_environment_policy,
            "solverEnvironment": solver_environment,
            "frontendLaunchEnvironmentPolicy": frontend_launch_environment,
            "commandProviderEnvironmentPolicy": command_environment_policy,
            "frameworkSourceTree": {
                "manifestPath": str(cls.source_manifest),
                "manifestSha256": cls.source_digest,
                "sourceTreeDigestHelper": copy.deepcopy(
                    SOURCE_TREE_DIGEST_HELPER_RECORD
                ),
            },
            "frozenBenchmark": {
                "benchmarkFingerprint": (
                    "0c25cb9d500bce29545ede21d42df355f"
                    "d23efbef32d1725db11ad026b6be91f"
                ),
                "cohortAuthoritySha256": (
                    "b8fd9d4136b247782df4dae4671ef613"
                    "23f587261f1aef11f7d4f53c9a1809f2"
                ),
                "frozenCaseCount": 389,
                "generatedCaseCount": 389,
                "selectedCaseSetSha256": (
                    "c02bc80056ccd6adccecbd1b3c2cd9bf"
                    "98032d6906580ffb755dc93d05a330a8"
                ),
            },
            "inputManifest": {
                "path": str(cls.input_manifest),
                "sha256": FROZEN_INPUT_MANIFEST_SHA256,
                "algorithm": INPUT_MANIFEST_ALGORITHM,
                "caseCount": 389,
                "selectedPath": str(cls.selected_input_manifest),
                "selectedSha256": FROZEN_INPUT_MANIFEST_SHA256,
                "selectedCaseCount": 389,
                "expectedFrozenSha256": FROZEN_INPUT_MANIFEST_SHA256,
                "frozenVerified": True,
            },
            "solverBinary": {
                "path": str(cls.solver_binary),
                "sha256": cls.solver_digest,
            },
            "trustedStack": {
                "manifestPath": str(cls.trusted_manifest),
                "manifestSha256": cls.trusted_digest,
                "manifestSchemaVersion": 4,
                "algorithm": TRUSTED_STACK_MANIFEST_ALGORITHM,
                "dynamicLinkingAlgorithm": TRUSTED_DYNAMIC_LINKING_ALGORITHM,
                "sourceObjectPairCount": 1,
                "rocqStdlibObjectCount": 1,
                "rocqRuntimeComponentCount": 1,
                "rocqRuntimeConfigurationCount": 2,
                "trustedExecutableCount": 5,
                "dynamicRuntimeFileCount": 2,
                "trustedHostToolCount": 26,
                "trustedHostDynamicRuntimeFileCount": 2,
                "trustedInspectionEnvironmentPolicy": ("clear-then-fixed-allowlist-v1"),
                "trustedInspectionEnvironmentVariableCount": 3,
                "lddRuntimeLoaderCandidateCount": 3,
                "lddRuntimeLoaderClosureAlgorithm": (
                    "logos-ldd-literal-rtldlist-closure-v1"
                ),
                "lddRuntimeLoaderPresentCandidateCount": 2,
                "lddRuntimeLoaderAbsentCandidateCount": 1,
                "systemResolverConfigurationPathCount": 2,
                "systemResolverConfigurationAlgorithm": (
                    "logos-system-dynamic-loader-config-closure-v1"
                ),
                "systemResolverConfigurationPresentPathCount": 1,
                "systemResolverConfigurationAbsentPathCount": 1,
                "systemIdentityConfigurationPathCount": 2,
                "systemIdentityConfigurationAlgorithm": (
                    "logos-system-identity-config-closure-v1"
                ),
                "systemIdentityConfigurationPresentPathCount": 2,
                "systemIdentityConfigurationAbsentPathCount": 0,
                "rocqExecutable": cls.trusted_executables["rocq"],
                "rocqCheckExecutable": cls.trusted_executables["rocqchk"],
                "rocqWorkerExecutable": cls.trusted_executables["rocqworker"],
                "rocqNativeExecutable": cls.trusted_executables["rocqnative"],
                "bwrapExecutable": cls.trusted_executables["bwrap"],
                "trustedCheckerEnvironmentPolicy": (TRUSTED_CHECKER_ENVIRONMENT_POLICY),
                "proofAgentLauncherEnvironmentPolicy": (
                    PROOF_AGENT_LAUNCHER_ENVIRONMENT_POLICY
                ),
            },
            "frontendStack": cls.frontend_record,
            "codexProvider": cls.codex_record,
            "postgresServerProfile": cls.postgres_record,
            "cohort16Gate": {
                "path": str(cls.gate_summary),
                "sha256": cls.gate_digest,
                "scopePath": str(SCOPE),
                "scopeSha256": cls.scope_digest,
                "caseSetSha256": cls.gate_case_set_digest,
                "frameworkSourceTreeManifestSha256": cls.source_digest,
                "selectedInputManifestSha256": cls.gate_input_digest,
                "solverBinarySha256": cls.solver_digest,
                "trustedStackManifestSha256": cls.trusted_digest,
                "frontendStackManifestSha256": cls.frontend_digest,
                "codexProviderManifestSha256": cls.codex_digest,
                "codexConfigSha256": cls.codex_config_digest,
                "providerEndpointSha256": cls.endpoint_digest,
                "postgresServerProfileSha256": cls.postgres_digest,
                "catalogGuidanceEnabled": True,
                "verificationMode": "outcome-unconditional",
            },
            "proofAgent": {
                "catalogGuidanceEnabled": True,
                "model": "gpt-5.6-sol",
                "reasoningEffort": "medium",
                "sessionRestartAfterFailedRounds": 16,
                "sessionHomePolicy": "isolated_per_generation",
                **PROOF_AGENT_DIAGNOSTIC_CONFIGURATION,
                "totalTimeoutSeconds": 14100,
                "trustedCheckTimeoutSeconds": 420,
                "resourcePolicy": {
                    "memoryLimitMiB": 6144,
                    "storageLimitMiB": 2048,
                    "cpuLimit": None,
                },
                "dockerImage": {
                    "reference": "logos-solver:latest",
                    "resolved": True,
                    "imageId": image_id,
                    "effectiveReference": image_id,
                },
            },
        }
        cls.summary_path = cls.full_run / "runner-summary.json"
        write_json(
            cls.summary_path,
            {
                "schemaVersion": 1,
                "status": "complete",
                "startedAt": "2026-07-23T02:00:00Z",
                "updatedAt": "2026-07-23T03:00:00Z",
                "jobs": 32,
                "caseTimeoutSeconds": 14400,
                "maxCounterexampleRounds": 3,
                "terminationGraceSeconds": 10.0,
                "solverBin": str(cls.solver_binary),
                "verificationMode": "outcome-unconditional",
                "model": "gpt-5.6-sol",
                "reasoningEffort": "medium",
                "proofAgentCatalogGuidanceEnabled": True,
                "proofAgentMemoryLimitMiB": 6144,
                "proofAgentStorageLimitMiB": 2048,
                "statementTimeoutSeconds": 600,
                "proofCheckTimeoutSeconds": 420,
                "proofDockerImage": image_id,
                "proofDockerImageRequested": "logos-solver:latest",
                "proofDockerImageEffective": image_id,
                "solverArgs": [],
                "effectiveSolverArgs": ["--force-llm-assessment"],
                "counterexampleAssessmentPolicy": "force-fresh",
                "sqlEnvironment": sql_environment,
                "configuration": configuration,
                "counts": {
                    "selected": 389,
                    "pending": 0,
                    "completed": 389,
                    "timedOut": 0,
                    "failed": 0,
                    "cancelled": 0,
                },
                "usageComplete": True,
                "integrityVerification": {
                    "verified": True,
                    "frameworkSourceTreeManifestSha256": cls.source_digest,
                    "solverBinarySha256": cls.solver_digest,
                    "trustedStackManifestSha256": cls.trusted_digest,
                    "frontendStackManifestSha256": cls.frontend_digest,
                    "codexProviderManifestSha256": cls.codex_digest,
                    "codexConfigSha256": cls.codex_config_digest,
                    "providerEndpointSha256": cls.endpoint_digest,
                    "solverEnvironmentSha256": solver_environment["sha256"],
                    "postgresServerProfileSha256": cls.postgres_digest,
                    "inputManifestSha256": FROZEN_INPUT_MANIFEST_SHA256,
                    "selectedInputManifestSha256": FROZEN_INPUT_MANIFEST_SHA256,
                    "cohort16GateSha256": cls.gate_digest,
                },
                "provenance": {
                    "benchmarkFingerprint": (
                        "0c25cb9d500bce29545ede21d42df355f"
                        "d23efbef32d1725db11ad026b6be91f"
                    ),
                    "cohortAuthoritySha256": (
                        "b8fd9d4136b247782df4dae4671ef613"
                        "23f587261f1aef11f7d4f53c9a1809f2"
                    ),
                    "frameworkSourceTreeManifestSha256": cls.source_digest,
                    "frontendStackManifestSha256": cls.frontend_digest,
                    "codexProviderManifestSha256": cls.codex_digest,
                    "codexConfigSha256": cls.codex_config_digest,
                    "providerEndpointSha256": cls.endpoint_digest,
                    "postgresServerProfileSha256": cls.postgres_digest,
                    "continuationCount": 0,
                },
                "cases": cls.raw_cases,
                "results": results,
            },
        )
        cls.original_summary = cls.summary_path.read_bytes()
        cls.original_gate = cls.gate_summary.read_bytes()
        cls.original_report = cls.first_report.read_bytes()
        cls.original_trusted_manifest = cls.trusted_manifest.read_bytes()
        cls.original_frontend_manifest = cls.frontend_manifest.read_bytes()
        cls.original_codex_manifest = cls.codex_manifest.read_bytes()
        cls.original_codex_config = cls.codex_config.read_bytes()
        cls.original_postgres_manifest = cls.postgres_manifest.read_bytes()
        cls.first_runner_result = (
            cls.full_run / "cases" / cls.raw_cases[0] / "runner-result.json"
        )
        cls.original_first_runner_result = cls.first_runner_result.read_bytes()
        cls.first_initial_problem = (
            cls.full_run
            / "cases"
            / cls.raw_cases[0]
            / "proof-stage/proof-agent/workspace-generations/0001/initial-problem-checkpoint/Problem.v"
        )
        cls.original_first_initial_problem = cls.first_initial_problem.read_bytes()
        cls.original_source = cls.source_file.read_bytes()
        cls.command = [
            sys.executable,
            str(PUBLISHER),
            "--full-run",
            str(cls.full_run),
            "--run-id",
            "publisher-preflight",
            "--final-audit",
            str(cls.final_audit),
            "--output",
            str(cls.output),
            "--source-tree-root",
            str(cls.source_root),
        ]
        completed = cls.run_publisher()
        if completed.returncode != 0:
            raise AssertionError(completed.stderr)
        cls.accepted_manifest = (cls.output / "manifest.json").read_bytes()

    @classmethod
    def run_publisher(cls) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            cls.command,
            cwd=LOGOS_ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )

    def setUp(self) -> None:
        self.summary_path.write_bytes(self.original_summary)
        self.gate_summary.write_bytes(self.original_gate)
        self.first_report.write_bytes(self.original_report)
        self.trusted_manifest.write_bytes(self.original_trusted_manifest)
        self.frontend_manifest.write_bytes(self.original_frontend_manifest)
        self.codex_manifest.write_bytes(self.original_codex_manifest)
        self.codex_config.write_bytes(self.original_codex_config)
        self.postgres_manifest.write_bytes(self.original_postgres_manifest)
        self.first_runner_result.write_bytes(self.original_first_runner_result)
        self.first_initial_problem.write_bytes(self.original_first_initial_problem)
        self.source_file.write_bytes(self.original_source)
        for name in ("latest", "run", "complete", ".archive", "lowering-current"):
            alias = self.output / name
            if alias.is_dir() and not alias.is_symlink():
                shutil.rmtree(alias)
            elif alias.exists() or alias.is_symlink():
                alias.unlink()

    def assert_rejected(self, expected_message: str) -> None:
        completed = self.run_publisher()
        self.assertNotEqual(completed.returncode, 0)
        self.assertIn(expected_message, completed.stderr)
        self.assertEqual(
            (self.output / "manifest.json").read_bytes(), self.accepted_manifest
        )

    def assert_first_report_rejected(
        self, report: dict[str, object], expected_message: str
    ) -> None:
        write_json(self.first_report, report)
        summary = json.loads(self.original_summary)
        summary["results"][0]["reportEvidence"]["sha256"] = sha256(self.first_report)
        write_json(self.first_runner_result, summary["results"][0])
        write_json(self.summary_path, summary)
        self.assert_rejected(expected_message)

    def rewrite_fixture_as_current_artifacts(self) -> dict[Path, bytes]:
        """Remove every legacy catalog field while preserving all other evidence."""
        originals: dict[Path, bytes] = {}

        def rewrite(path: Path, document: dict[str, object]) -> None:
            originals.setdefault(path, path.read_bytes())
            write_json(path, document)

        def current_policy() -> dict[str, object]:
            return json.loads(
                json.dumps(CURRENT_PROOF_AGENT_LAUNCHER_ENVIRONMENT_POLICY)
            )

        def strip_proof_agent_configuration(configuration: dict[str, object]) -> None:
            configuration.pop("catalogGuidance", None)
            configuration["proofAgentLauncherEnvironmentPolicy"] = current_policy()
            context = configuration.get("context")
            if isinstance(context, dict):
                context.pop("catalogBytes", None)

        def strip_effective_configuration(configuration: dict[str, object]) -> None:
            configuration.pop("catalogGuidanceEnabled", None)
            configuration["proofAgentLauncherEnvironmentPolicy"] = current_policy()

        def strip_report(report: dict[str, object]) -> None:
            proof = report.get("proof")
            if not isinstance(proof, dict):
                return
            configuration = proof.get("proofAgentConfiguration")
            if isinstance(configuration, dict):
                strip_proof_agent_configuration(configuration)
            rounds = proof.get("proofAgentRounds")
            if isinstance(rounds, list):
                for round_record in rounds:
                    if isinstance(round_record, dict):
                        round_record.pop("catalogGuidance", None)

        gate = json.loads(self.original_gate)
        gate.pop("proofAgentCatalogGuidanceEnabled", None)
        gate_proof_agent = gate["configuration"]["proofAgent"]
        gate_proof_agent.pop("catalogGuidanceEnabled", None)
        gate_proof_agent["proofAgentLauncherEnvironmentPolicy"] = current_policy()
        for row in gate["results"]:
            strip_effective_configuration(row["effectiveConfiguration"])
            report_path = Path(row["reportEvidence"]["path"])
            report = json.loads(report_path.read_text(encoding="utf-8"))
            strip_report(report)
            rewrite(report_path, report)
            row["reportEvidence"]["sha256"] = sha256(report_path)
        rewrite(self.gate_summary, gate)
        gate_digest = sha256(self.gate_summary)

        summary = json.loads(self.original_summary)
        summary.pop("proofAgentCatalogGuidanceEnabled", None)
        proof_agent = summary["configuration"]["proofAgent"]
        proof_agent.pop("catalogGuidanceEnabled", None)
        proof_agent["proofAgentLauncherEnvironmentPolicy"] = current_policy()
        summary["configuration"]["trustedStack"][
            "proofAgentLauncherEnvironmentPolicy"
        ] = current_policy()
        cohort16_gate = summary["configuration"]["cohort16Gate"]
        cohort16_gate.pop("catalogGuidanceEnabled", None)
        cohort16_gate["sha256"] = gate_digest
        summary["integrityVerification"]["cohort16GateSha256"] = gate_digest
        for row in summary["results"]:
            strip_effective_configuration(row["effectiveConfiguration"])
            row["effectiveConfiguration"]["cohort16GateSha256"] = gate_digest
            row["proofMetrics"].pop("catalogBytes", None)
            report_path = Path(row["reportEvidence"]["path"])
            report = json.loads(report_path.read_text(encoding="utf-8"))
            strip_report(report)
            rewrite(report_path, report)
            row["reportEvidence"]["sha256"] = sha256(report_path)
            rewrite(
                self.full_run / "cases" / row["caseId"] / "runner-result.json",
                row,
            )
        rewrite(self.summary_path, summary)
        return originals

    def assert_trusted_manifest_rejected(
        self, mutate: object, expected_message: str
    ) -> None:
        document = json.loads(self.original_trusted_manifest)
        assert callable(mutate)
        mutate(document)
        write_canonical_json(self.trusted_manifest, document)
        summary = json.loads(self.original_summary)
        summary["configuration"]["trustedStack"]["manifestSha256"] = sha256(
            self.trusted_manifest
        )
        write_json(self.summary_path, summary)
        self.assert_rejected(expected_message)

    def assert_frontend_manifest_rejected(
        self, mutate: object, expected_message: str
    ) -> None:
        document = json.loads(self.original_frontend_manifest)
        assert callable(mutate)
        mutate(document)
        write_canonical_json(self.frontend_manifest, document)
        summary = json.loads(self.original_summary)
        summary["configuration"]["frontendStack"]["manifestSha256"] = sha256(
            self.frontend_manifest
        )
        write_json(self.summary_path, summary)
        self.assert_rejected(expected_message)

    def assert_codex_manifest_rejected(
        self, mutate: object, expected_message: str
    ) -> None:
        document = json.loads(self.original_codex_manifest)
        assert callable(mutate)
        mutate(document)
        write_canonical_json(self.codex_manifest, document)
        summary = json.loads(self.original_summary)
        summary["configuration"]["codexProvider"]["manifestSha256"] = sha256(
            self.codex_manifest
        )
        write_json(self.summary_path, summary)
        self.assert_rejected(expected_message)

    def test_result_row_preserves_failed_terminal_status(self) -> None:
        publisher = runpy.run_path(str(PUBLISHER), run_name="publisher_unit_test")
        result_row = publisher["result_row"]
        publish_error = publisher["PublishError"]
        logs = {
            "schemaInput": "logs/case/schema.sql",
            "sourceInput": "logs/case/source.sql",
            "targetInput": "logs/case/target.sql",
        }
        raw = {
            "benchmark": "fixture",
            "status": "failed",
            "returnCode": 1,
            "elapsedMs": 17,
            "outcome": None,
            "backendStatus": None,
            "certification": None,
            "proofMetrics": {},
            "inputFiles": {
                name: {"sha256": character * 64}
                for name, character in (
                    ("schema", "1"),
                    ("source", "2"),
                    ("target", "3"),
                )
            },
        }
        row = result_row(raw, "case", "full", "run-id", logs, self.usage)
        self.assertEqual(row["status"], "failed")
        self.assertEqual(row["returnCode"], 1)
        self.assertIsNone(row["outcome"])

        raw["status"] = "cancelled"
        with self.assertRaisesRegex(publish_error, "nonterminal status"):
            result_row(raw, "case", "full", "run-id", logs, self.usage)

    def test_materializes_and_binds_all_389_rows(self) -> None:
        rows = [
            json.loads(line)
            for line in (self.output / "results.jsonl")
            .read_text(encoding="utf-8")
            .splitlines()
        ]
        self.assertEqual((len(rows), len({row["caseId"] for row in rows})), (389, 389))
        manifest = json.loads(self.accepted_manifest)
        published_runner = json.loads(
            (self.output / "runner-summary.json").read_text(encoding="utf-8")
        )
        self.assertTrue(published_runner["proofAgentCatalogGuidanceEnabled"])
        self.assertTrue(
            published_runner["configuration"]["proofAgent"]["catalogGuidanceEnabled"]
        )
        for (
            key,
            value,
        ) in CURRENT_EFFECTIVE_PROOF_AGENT_DIAGNOSTIC_CONFIGURATION.items():
            self.assertEqual(manifest["fullRun"][key], value)
        for key, value in PROOF_AGENT_ENVIRONMENT_CONFIGURATION.items():
            self.assertEqual(
                published_runner["configuration"]["proofAgent"][key], value
            )
        for key in (
            "solverLaunchEnvironmentPolicy",
            "solverEnvironment",
            "frontendLaunchEnvironmentPolicy",
            "commandProviderEnvironmentPolicy",
        ):
            self.assertEqual(
                manifest["fullRun"][key],
                published_runner["configuration"][key],
            )
        self.assertEqual(
            manifest["fullRun"]["solverEnvironmentSha256"],
            published_runner["configuration"]["solverEnvironment"]["sha256"],
        )
        self.assertNotIn("catalogGuidanceEnabled", manifest["fullRun"])
        self.assertNotIn(
            "catalog guidance",
            (self.output / "README.md").read_text(encoding="utf-8").lower(),
        )
        source_summary_digest = sha256(self.summary_path)
        self.assertEqual(
            manifest["fullRun"]["runnerSummarySha256"], source_summary_digest
        )
        canonical_summary = json.loads(
            (self.output / "summary.json").read_text(encoding="utf-8")
        )
        self.assertEqual(
            canonical_summary["sourceFullRunSummarySha256"], source_summary_digest
        )
        self.assertEqual(len(canonical_summary["results"]), 389)
        self.assertEqual(
            sha256(self.output / "results.jsonl"),
            canonical_summary["resultsJsonlSha256"],
        )
        expected_broker_totals = {
            key: value * 389 for key, value in PROOF_AGENT_BROKER_METRICS.items()
        }
        self.assertEqual(
            canonical_summary["proofAgentBrokerMetrics"], expected_broker_totals
        )
        self.assertEqual(
            manifest["fullRun"]["proofAgentBrokerMetrics"],
            expected_broker_totals,
        )
        self.assertEqual(
            {tuple(sorted(row["sourceRun"].items())) for row in rows},
            {(("kind", "full"), ("runId", "publisher-preflight"))},
        )
        self.assertEqual(
            sha256(self.output / "frozen-input-manifest.json"),
            FROZEN_INPUT_MANIFEST_SHA256,
        )
        self.assertEqual(
            sha256(self.output / "trusted-stack-manifest.json"),
            manifest["fullRun"]["trustedStackManifestSha256"],
        )
        for name, key in (
            ("frontend-stack-manifest.json", "frontendStackManifestSha256"),
            ("codex-provider-manifest.json", "codexProviderManifestSha256"),
            ("codex-provider-config.toml", "codexProviderConfigSha256"),
            ("postgres-server-profile.json", "postgresServerProfileSha256"),
        ):
            self.assertEqual(sha256(self.output / name), manifest["fullRun"][key])
        self.assertNotIn("auth.json", {path.name for path in self.output.rglob("*")})
        first = rows[0]
        for key, value in PROOF_AGENT_ENVIRONMENT_CONFIGURATION.items():
            self.assertEqual(first["effectiveConfiguration"][key], value)
        for key in ("schema", "source", "target"):
            binding = first["inputFiles"][key]
            self.assertEqual(sha256(self.output / binding["path"]), binding["sha256"])
        self.assertEqual(
            sha256(self.output / first["proofMetrics"]["proofSource"]["path"]),
            first["proofMetrics"]["proofSource"]["sha256"],
        )
        evidence_path = self.output / first["logs"]["proofAgentEvidenceManifest"]
        self.assertEqual(
            sha256(evidence_path),
            first["logs"]["proofAgentEvidenceManifestSha256"],
        )
        evidence = json.loads(evidence_path.read_text(encoding="utf-8"))
        self.assertEqual(evidence["schemaVersion"], 3)
        self.assertEqual(
            evidence["diagnosticElapsedWarnings"],
            first["proofMetrics"]["diagnosticElapsedWarnings"],
        )
        self.assertEqual(evidence["diagnosticTransport"], "host_unix_broker")
        self.assertEqual(
            evidence["diagnosticCachePolicy"],
            "preflight_built_source_digest_bound_host_only",
        )
        self.assertEqual(evidence["sourceFullRunSummarySha256"], source_summary_digest)
        self.assertEqual(
            evidence["compileCheckpointPolicy"],
            "latest_host_problem_compile_pass_digest_deduplicated",
        )
        for key, value in PROOF_AGENT_BROKER_METRICS.items():
            self.assertEqual(first["proofMetrics"][key], value)
            self.assertEqual(evidence[key], value)
        self.assertEqual(first["proofMetrics"]["diagnosticInvocationCount"], 1)
        self.assertEqual(first["proofMetrics"]["checkerInvocationCount"], 4)
        self.assertEqual(
            first["proofMetrics"]["diagnosticElapsedWarnings"],
            [
                {
                    "code": "diagnostic_elapsed_exceeded_timeout_plus_kill_margin",
                    "round": 1,
                    "sequence": 1,
                    "requestedTimeoutSeconds": 30,
                    "effectiveTimeoutSeconds": 30,
                    "elapsedMs": 40_000,
                    "timeoutPlusKillMarginMs": 36_000,
                    "overrunMs": 4_000,
                }
            ],
        )
        self.assertEqual(len(evidence["diagnosticAcceptedSourceAudits"]), 1)
        self.assertEqual(len(evidence["diagnosticRejectedSourceAudits"]), 1)
        self.assertEqual(evidence["fileCount"], len(evidence["files"]))
        for binding in evidence["files"]:
            copied = evidence_path.parent / binding["canonicalRelativePath"]
            self.assertEqual(sha256(copied), binding["sha256"])
            self.assertEqual(copied.stat().st_size, binding["bytes"])
            self.assertNotEqual(copied.suffix, ".vo")
        accepted = evidence["diagnosticAcceptedSourceAudits"][0]
        rejected = evidence["diagnosticRejectedSourceAudits"][0]
        self.assertEqual(accepted["sequence"], 1)
        self.assertEqual(accepted["requestOrdinal"], 1)
        self.assertEqual(rejected["requestOrdinal"], 2)
        for binding in (
            accepted["audit"],
            *(rejected[name] for name in ("problem", "request", "audit", "feedback")),
        ):
            copied = evidence_path.parent / binding["canonicalRelativePath"]
            self.assertEqual(sha256(copied), binding["sha256"])
            self.assertEqual(copied.stat().st_size, binding["bytes"])
        self.assertEqual(
            [entry["name"] for entry in evidence["diagnosticCacheEntries"]],
            [
                "Schema.v",
                "Schema.vo",
                "Queries.v",
                "Queries.vo",
                "Witness.v",
                "Witness.vo",
            ],
        )

    def test_current_artifacts_without_catalog_fields_are_accepted(self) -> None:
        originals = self.rewrite_fixture_as_current_artifacts()
        try:
            publisher = runpy.run_path(
                str(PUBLISHER), run_name="current_artifact_publisher"
            )
            _summary, bindings = publisher["validate_full_summary"](self.full_run)
            self.assertFalse(bindings["legacyCatalogArtifacts"])
        finally:
            for path, content in originals.items():
                path.write_bytes(content)

    def test_rejects_mixed_legacy_catalog_metadata(self) -> None:
        summary = json.loads(self.original_summary)
        del summary["proofAgentCatalogGuidanceEnabled"]
        write_json(self.summary_path, summary)
        self.assert_rejected("legacy catalog metadata is incomplete")

    def test_real_runner_record_projections_are_accepted_by_publisher(self) -> None:
        runner = runpy.run_path(str(RUNNER), run_name="publisher_runner_contract")
        publisher = runpy.run_path(str(PUBLISHER), run_name="runner_contract_publisher")
        trusted_document = json.loads(self.original_trusted_manifest)
        frontend_document = json.loads(self.original_frontend_manifest)
        codex_document = json.loads(self.original_codex_manifest)
        with tempfile.TemporaryDirectory(prefix="logos-runner-record-") as temporary:
            run_root = Path(temporary)
            trusted_record = runner["trusted_stack_record"]
            trusted_record.__globals__["build_trusted_stack_manifest"] = (
                lambda _switch: trusted_document
            )
            emitted_trusted = trusted_record(
                run_root,
                Path("/fixture/opam-switch"),
                resume=False,
            )
            frontend_record = runner["frontend_stack_record"]
            frontend_record.__globals__["build_frontend_stack_manifest"] = (
                lambda: frontend_document
            )
            emitted_frontend = frontend_record(run_root, resume=False)
            codex_record = runner["codex_provider_record"]
            codex_record.__globals__["sanitized_codex_config"] = lambda: (
                self.original_codex_config,
                codex_document["endpoint"],
                Path("/fixture/codex-home"),
            )
            codex_record.__globals__["build_codex_provider_manifest"] = (
                lambda _config_path, _endpoint: codex_document
            )
            emitted_codex, _source_home = codex_record(run_root, resume=False)
            config = SimpleNamespace(codex_provider=emitted_codex)
            emitted_solver_policy = runner["solver_launch_environment_policy_record"](
                config
            )
            solver_environment_record = runner["solver_environment_record"]
            runtime_home = "/tmp/fixture-codex-runtime"
            solver_environment_record.__globals__["solver_environment"] = lambda _: {
                "PATH": emitted_codex["solverPath"]["value"],
                "HOME": "/nonexistent",
                "TMPDIR": "/tmp",
                "LC_ALL": "C",
                "LANG": "C",
                "TZ": "UTC",
                "CODEX_HOME": runtime_home,
                "LOGOS_SOLVER_CODEX_HOME": runtime_home,
                "LOGOS_SOLVER_CODEX_CONFIG": f"{runtime_home}/config.toml",
                "JAVA_HOME": str(
                    configured_path(
                        LOGOS_ROOT,
                        "LOGOS_JAVA_HOME"
                        if os.environ.get("LOGOS_JAVA_HOME")
                        else "JAVA_HOME",
                        required=True,
                    )
                ),
                "MAVEN_VERSION": "3.9.11",
                "LOGOS_CALCITE_RUNTIME_CLASSPATH_FILE": str(
                    (
                        LOGOS_ROOT / "frontend/calcite-wrapper/target/"
                        "logos-runtime-classpath.txt"
                    ).resolve()
                ),
            }
            emitted_solver_environment = solver_environment_record(config)
            summary = json.loads(self.original_summary)
            self.assertEqual(
                set(emitted_trusted),
                set(summary["configuration"]["trustedStack"]),
            )
            self.assertEqual(
                set(emitted_frontend),
                set(summary["configuration"]["frontendStack"]),
            )
            self.assertEqual(
                set(emitted_codex),
                set(summary["configuration"]["codexProvider"]),
            )
            self.assertEqual(
                emitted_solver_policy,
                summary["configuration"]["solverLaunchEnvironmentPolicy"],
            )
            self.assertEqual(
                emitted_solver_environment,
                summary["configuration"]["solverEnvironment"],
            )
            publisher["validate_trusted_stack"](emitted_trusted, run_root)
            publisher["validate_frontend_stack"](emitted_frontend, run_root)
            publisher["validate_codex_provider"](emitted_codex, run_root)

    def test_rejects_disabling_solver_argument(self) -> None:
        summary = json.loads(self.original_summary)
        for record in (summary, summary["configuration"]):
            record["solverArgs"] = ["--disable-proof-agent"]
            record["effectiveSolverArgs"] = [
                "--force-llm-assessment",
                "--disable-proof-agent",
            ]
        write_json(self.summary_path, summary)
        self.assert_rejected("disabling/short-circuit solver option")

    def test_rejects_custom_frontend_solver_argument(self) -> None:
        summary = json.loads(self.original_summary)
        for record in (summary, summary["configuration"]):
            record["solverArgs"] = ["--calcite-ir-command=/tmp/forged"]
            record["effectiveSolverArgs"] = [
                "--force-llm-assessment",
                "--calcite-ir-command=/tmp/forged",
            ]
        write_json(self.summary_path, summary)
        self.assert_rejected("disabling/short-circuit solver option")

    def test_rejects_trusted_stack_top_level_schema_drift(self) -> None:
        self.assert_trusted_manifest_rejected(
            lambda document: document.__setitem__("unreviewed", {}),
            "trusted-stack manifest has noncanonical fields",
        )

    def test_rejects_trusted_stack_dynamic_closure_drift(self) -> None:
        self.assert_trusted_manifest_rejected(
            lambda document: document["dynamicLinking"]["files"][0].__setitem__(
                "sha256", "invalid"
            ),
            "trusted stack dynamic linking.files[0]",
        )

    def test_rejects_trusted_inspection_environment_drift(self) -> None:
        self.assert_trusted_manifest_rejected(
            lambda document: document["trustedHostTools"][
                "inspectionEnvironment"
            ].__setitem__("workingDirectory", "/tmp"),
            "trusted inspection environment is not the fixed C policy",
        )

    def test_rejects_reviewed_ldd_script_digest_drift(self) -> None:
        def mutate(document: dict[str, object]) -> None:
            tools = document["trustedHostTools"]["tools"]
            next(row for row in tools if row["name"] == "ldd")["sha256"] = "0" * 64

        self.assert_trusted_manifest_rejected(
            mutate, "trusted ldd script path or reviewed digest changed"
        )

    def test_rejects_ldd_runtime_loader_closure_drift(self) -> None:
        self.assert_trusted_manifest_rejected(
            lambda document: document["trustedHostTools"]["lddRuntimeLoaders"][
                "candidates"
            ][0].__setitem__("sha256", "0" * 64),
            "has invalid loader evidence",
        )

    def test_rejects_system_resolver_closure_drift(self) -> None:
        self.assert_trusted_manifest_rejected(
            lambda document: document["trustedHostTools"][
                "systemResolverConfiguration"
            ]["paths"][1].__setitem__("state", "present"),
            "trusted system resolver configuration is incomplete",
        )

    def test_rejects_system_identity_closure_drift(self) -> None:
        self.assert_trusted_manifest_rejected(
            lambda document: document["trustedHostTools"][
                "systemIdentityConfiguration"
            ]["paths"][0].__setitem__("sha256", "invalid"),
            "has invalid required-file evidence",
        )

    def test_rejects_bwrap_selection_drift(self) -> None:
        self.assert_trusted_manifest_rejected(
            lambda document: document["executables"]["bwrap"].__setitem__(
                "searchPath", "/tmp"
            ),
            "trusted-stack manifest is empty, malformed, or unbound",
        )

    def test_rejects_trusted_environment_policy_record_drift(self) -> None:
        summary = json.loads(self.original_summary)
        summary["configuration"]["trustedStack"]["trustedCheckerEnvironmentPolicy"][
            "fixedVariables"
        ][0] = "PATH=/tmp"
        write_json(self.summary_path, summary)
        self.assert_rejected("trusted process environment policies are not exact")

    def test_rejects_trusted_closure_summary_cross_binding_drift(self) -> None:
        summary = json.loads(self.original_summary)
        summary["configuration"]["trustedStack"][
            "systemIdentityConfigurationPresentPathCount"
        ] = 1
        write_json(self.summary_path, summary)
        self.assert_rejected("trusted system identity closure is not cross-bound")

    def test_rejects_frontend_manifest_treatment_drift(self) -> None:
        summary = json.loads(self.original_summary)
        summary["configuration"]["frontendStack"]["effectiveCommand"] = (
            "/tmp/forged-frontend"
        )
        write_json(self.summary_path, summary)
        self.assert_rejected("frontend-stack manifest is malformed or not canonical")

    def test_rejects_frontend_launch_environment_drift(self) -> None:
        self.assert_frontend_manifest_rejected(
            lambda document: document["launchEnvironment"][
                "fixedVariables"
            ].__setitem__(0, "PATH=/tmp"),
            "frontend launch environment is not the fixed empty-base policy",
        )

    def test_rejects_frontend_launch_tool_order_drift(self) -> None:
        self.assert_frontend_manifest_rejected(
            lambda document: document["launchTools"]["tools"].reverse(),
            "frontend launch tools is incomplete, reordered, or malformed",
        )

    def test_rejects_frontend_launch_tool_dynamic_closure_drift(self) -> None:
        self.assert_frontend_manifest_rejected(
            lambda document: document["launchTools"]["dynamicLinking"]["files"][
                0
            ].__setitem__("sha256", "invalid"),
            "frontend launch-tool dynamic linking.files[0]",
        )

    def test_rejects_frontend_launch_summary_cross_binding_drift(self) -> None:
        summary = json.loads(self.original_summary)
        summary["configuration"]["frontendStack"]["launchToolCount"] = 7
        write_json(self.summary_path, summary)
        self.assert_rejected("frontend launch closure is not cross-bound")

    def test_rejects_codex_command_environment_policy_drift(self) -> None:
        self.assert_codex_manifest_rejected(
            lambda document: document["commandEnvironmentPolicy"][
                "hostEnvironmentAllowlist"
            ].append("BASH_ENV"),
            "Codex provider manifest is malformed or unbound",
        )

    def test_rejects_codex_lexical_wrapper_drift(self) -> None:
        self.assert_codex_manifest_rejected(
            lambda document: document["hostCodexCli"]["lexicalWrapper"].__setitem__(
                "sha256", "0" * 64
            ),
            "Codex lexical wrapper is not cross-bound",
        )

    def test_rejects_codex_interpreter_dynamic_closure_drift(self) -> None:
        self.assert_codex_manifest_rejected(
            lambda document: document["hostCodexCli"]["interpreterChain"][
                "dynamicLinking"
            ]["files"][0].__setitem__("sha256", "invalid"),
            "Codex interpreter dynamic linking.files[0]",
        )

    def test_rejects_codex_solver_path_drift(self) -> None:
        self.assert_codex_manifest_rejected(
            lambda document: document["hostCodexCli"]["solverPath"].__setitem__(
                "value", "/tmp"
            ),
            "Codex solver PATH value does not reconcile",
        )

    def test_rejects_solver_launch_environment_policy_drift(self) -> None:
        summary = json.loads(self.original_summary)
        summary["configuration"]["solverLaunchEnvironmentPolicy"]["fixedVariables"][
            0
        ] = "PATH=/tmp"
        write_json(self.summary_path, summary)
        self.assert_rejected("solver launch environment policy is malformed or unbound")

    def test_rejects_solver_environment_record_drift(self) -> None:
        summary = json.loads(self.original_summary)
        summary["configuration"]["solverEnvironment"]["variableCount"] = 11
        write_json(self.summary_path, summary)
        self.assert_rejected("solver launch environment record is malformed")

    def test_rejects_credential_material_in_provider_snapshot(self) -> None:
        self.codex_config.write_bytes(
            self.original_codex_config + b'api_key = "must-not-publish"\n'
        )
        config_digest = sha256(self.codex_config)
        provider = json.loads(self.original_codex_manifest)
        provider["config"]["sha256"] = config_digest
        provider["config"]["bytes"] = self.codex_config.stat().st_size
        write_canonical_json(self.codex_manifest, provider)
        summary = json.loads(self.original_summary)
        record = summary["configuration"]["codexProvider"]
        record["configSha256"] = config_digest
        record["configBytes"] = self.codex_config.stat().st_size
        record["manifestSha256"] = sha256(self.codex_manifest)
        write_json(self.summary_path, summary)
        self.assert_rejected("sanitized Codex config contains credential material")

    def test_rejects_missing_codex_package_closure(self) -> None:
        provider = json.loads(self.original_codex_manifest)
        del provider["hostCodexCli"]["packageFiles"]
        write_canonical_json(self.codex_manifest, provider)
        summary = json.loads(self.original_summary)
        summary["configuration"]["codexProvider"]["manifestSha256"] = sha256(
            self.codex_manifest
        )
        write_json(self.summary_path, summary)
        self.assert_rejected("Codex provider manifest is malformed or unbound")

    def test_rejects_postgres_profile_drift(self) -> None:
        summary = json.loads(self.original_summary)
        summary["configuration"]["postgresServerProfile"]["profile"][
            "serverVersion"
        ] = "17.5"
        write_json(self.summary_path, summary)
        self.assert_rejected("PostgreSQL server profile is not frozen PG17.4 UTC/C")

    def test_rejects_postgres_capacity_drift(self) -> None:
        summary = json.loads(self.original_summary)
        summary["configuration"]["postgresServerProfile"]["profile"][
            "maxConnections"
        ] = "95"
        write_json(self.summary_path, summary)
        self.assert_rejected("PostgreSQL server profile is not frozen PG17.4 UTC/C")

    def test_rejects_exact_input_hash_drift(self) -> None:
        summary = json.loads(self.original_summary)
        summary["results"][0]["inputFiles"]["source"]["sha256"] = "0" * 64
        write_json(
            self.full_run
            / "cases"
            / summary["results"][0]["caseId"]
            / "runner-result.json",
            summary["results"][0],
        )
        write_json(self.summary_path, summary)
        self.assert_rejected("inputFiles.source digest mismatch")

    def test_rejects_custom_proof_agent_command_even_when_rehashed(self) -> None:
        report = json.loads(self.original_report)
        report["proof"]["proofAgentConfiguration"]["command"] = (
            "codex exec --json --model gpt-5.6-sol -c model_reasoning_effort=medium custom"
        )
        write_json(self.first_report, report)
        summary = json.loads(self.original_summary)
        summary["results"][0]["reportEvidence"]["sha256"] = sha256(self.first_report)
        write_json(
            self.full_run
            / "cases"
            / summary["results"][0]["caseId"]
            / "runner-result.json",
            summary["results"][0],
        )
        write_json(self.summary_path, summary)
        self.assert_rejected("proof report treatment/configuration drifted")

    def test_rejects_broker_configuration_drift(self) -> None:
        summary = json.loads(self.original_summary)
        summary["configuration"]["proofAgent"]["diagnosticTransport"] = (
            "untrusted_file_request"
        )
        write_json(self.summary_path, summary)
        self.assert_rejected("diagnosticTransport differs from the frozen contract")

    def test_rejects_host_launch_environment_policy_drift(self) -> None:
        summary = json.loads(self.original_summary)
        policy = summary["configuration"]["proofAgent"][
            "trustedCheckerEnvironmentPolicy"
        ]
        policy["fixedVariables"][0] = "PATH=/tmp/hostile"
        write_json(self.summary_path, summary)
        self.assert_rejected(
            "trustedCheckerEnvironmentPolicy differs from the frozen contract"
        )

    def test_rejects_per_case_host_launch_environment_policy_drift(self) -> None:
        summary = json.loads(self.original_summary)
        row = summary["results"][0]
        policy = row["effectiveConfiguration"]["proofAgentLauncherEnvironmentPolicy"]
        policy["hostEnvironmentAllowlist"].append("LD_PRELOAD")
        write_json(self.first_runner_result, row)
        write_json(self.summary_path, summary)
        self.assert_rejected("effective per-case configuration drifted")

    def test_rejects_diagnostic_cache_digest_drift(self) -> None:
        report = json.loads(self.original_report)
        report["proof"]["proofAgentConfiguration"]["diagnosticCacheManifestSha256"] = (
            "0" * 64
        )
        write_json(self.first_report, report)
        summary = json.loads(self.original_summary)
        summary["results"][0]["reportEvidence"]["sha256"] = sha256(self.first_report)
        write_json(
            self.full_run
            / "cases"
            / summary["results"][0]["caseId"]
            / "runner-result.json",
            summary["results"][0],
        )
        write_json(self.summary_path, summary)
        self.assert_rejected("trusted diagnostic cache manifest drifted")

    def test_rejects_witness_cache_source_binding_drift(self) -> None:
        cache_root = (
            self.first_report.parent
            / "proof-stage/proof-agent/trusted-diagnostic-cache"
        )
        (cache_root / "Witness.v").write_text(
            "Definition forged_witness := True.\n", encoding="utf-8"
        )
        entries = (
            "Schema.v",
            "Schema.vo",
            "Queries.v",
            "Queries.vo",
            "Witness.v",
            "Witness.vo",
        )
        manifest = cache_root / "SHA256SUMS"
        manifest.write_text(
            "".join(f"{sha256(cache_root / name)}  {name}\n" for name in entries),
            encoding="utf-8",
        )
        report = json.loads(self.original_report)
        report["proof"]["proofAgentConfiguration"][
            "diagnosticCacheManifestSha256"
        ] = sha256(manifest)
        write_json(self.first_report, report)
        summary = json.loads(self.original_summary)
        summary["results"][0]["reportEvidence"]["sha256"] = sha256(
            self.first_report
        )
        write_json(self.first_runner_result, summary["results"][0])
        write_json(self.summary_path, summary)
        self.assert_rejected("trusted diagnostic cache source binding drifted")

    def test_rejects_tampered_initial_problem_checkpoint(self) -> None:
        self.first_initial_problem.write_text("tampered checkpoint\n", encoding="utf-8")
        self.assert_rejected("initial problem checkpoint evidence is incoherent")

    def test_rejects_incomplete_or_drifting_broker_source_audit_evidence(
        self,
    ) -> None:
        report = json.loads(self.original_report)
        report["proof"]["proofAgentRounds"][0]["diagnosticAcceptedSourceAudits"] = []
        self.assert_first_report_rejected(
            report, "accepted diagnostic request evidence does not reconcile"
        )

        report = json.loads(self.original_report)
        report["proof"]["proofAgentRounds"][0]["diagnosticRejectedSourceAudits"] = []
        self.assert_first_report_rejected(
            report, "rejected diagnostic source-audit evidence does not reconcile"
        )

        report = json.loads(self.original_report)
        report["proof"]["proofAgentRounds"][0]["diagnosticCheckerRequestPath"] = (
            "proof-stage/proof-agent/rounds/01/checker-request.json"
        )
        self.assert_first_report_rejected(
            report, "legacy diagnostic request-file state is not permitted"
        )

        summary = json.loads(self.original_summary)
        summary["results"][0]["proofMetrics"]["diagnosticPreservedArtifactCount"] += 1
        write_json(self.first_runner_result, summary["results"][0])
        write_json(self.summary_path, summary)
        self.first_report.write_bytes(self.original_report)
        self.assert_rejected("broker/preflight metrics disagree with report")

        accepted_audit = (
            self.first_report.parent / "proof-stage/proof-agent/rounds/01/"
            "interactive-diagnostics/01/audit.json"
        )
        original_accepted_audit = accepted_audit.read_bytes()
        try:
            write_json(
                accepted_audit,
                {
                    "passed": False,
                    "scannedFiles": ["fixture/Problem.v"],
                    "findings": [
                        {
                            "path": "fixture/Problem.v",
                            "line": 1,
                            "token": "Load",
                            "excerpt": "Load fixture.",
                        }
                    ],
                },
            )
            report = json.loads(self.original_report)
            report["proof"]["proofAgentRounds"][0]["diagnosticAcceptedSourceAudits"][0][
                "audit"
            ] = diagnostic_artifact_binding(self.first_report.parent, accepted_audit)
            self.assert_first_report_rejected(
                report, "has an incoherent source-audit outcome"
            )
        finally:
            accepted_audit.write_bytes(original_accepted_audit)

    def test_rejects_forged_diagnostic_elapsed_warning(self) -> None:
        summary = json.loads(self.original_summary)
        summary["results"][0]["proofMetrics"]["diagnosticElapsedWarnings"][0][
            "overrunMs"
        ] += 1
        write_json(self.first_runner_result, summary["results"][0])
        write_json(self.summary_path, summary)
        self.assert_rejected(
            "diagnostic elapsed warnings disagree with bound evidence"
        )

    def test_rejects_legacy_or_drifting_diagnostic_protocol(self) -> None:
        publisher = runpy.run_path(
            str(PUBLISHER), run_name="diagnostic_protocol_validator"
        )
        with self.assertRaisesRegex(
            publisher["PublishError"], "legacy.mode is invalid"
        ):
            publisher["validate_diagnostic_identity"](
                "problem_compile", "Problem.v", "assembly", "0" * 64, "legacy"
            )

        request_path = (
            self.first_report.parent
            / "proof-stage/proof-agent/rounds/01/interactive-diagnostics/01/"
            "request.json"
        )
        original_request = request_path.read_bytes()
        try:
            request = json.loads(original_request)
            request["candidateBytes"] += 1
            write_json(request_path, request)
            self.assert_rejected("diagnostic.request identity drifted")
        finally:
            request_path.write_bytes(original_request)

    def test_rejects_counterexample_round_limit_drift(self) -> None:
        summary = json.loads(self.original_summary)
        summary["maxCounterexampleRounds"] = 4
        write_json(self.summary_path, summary)
        self.assert_rejected("accepted frozen 389/32x/4h contract")

        summary = json.loads(self.original_summary)
        summary["configuration"]["maxCounterexampleRounds"] = 4
        write_json(self.summary_path, summary)
        self.assert_rejected("accepted frozen 389/32x/4h contract")

    def test_formal_countermodel_requires_exact_trusted_bindings(self) -> None:
        publisher = runpy.run_path(
            str(PUBLISHER), run_name="formal_countermodel_validator"
        )
        validate = publisher["validate_formal_countermodel_certificate"]
        publish_error = publisher["PublishError"]
        source_dir = self.first_report.parent
        problem_path = source_dir / "proof-stage/formal-sql/Problem.v"
        goal_path = source_dir / "proof-stage/formal-sql/Goal.v"
        report = json.loads(self.original_report)
        row = json.loads(self.original_first_runner_result)
        proof = report["proof"]
        round_record = proof["proofAgentRounds"][-1]
        closure_path = source_dir / round_record["authorityClosurePath"]
        checked_problem = closure_path.parent / "Problem.v"
        checked_goal = closure_path.parent / "Goal.v"
        context_relative = "proof-stage/formal-sql/context-manifest.json"
        proof["proofAgentConfiguration"]["context"][
            "manifestPath"
        ] = context_relative
        context_path = source_dir / context_relative
        paths = (problem_path, goal_path, checked_problem, checked_goal, context_path)
        originals = {
            path: path.read_bytes() if path.exists() else None for path in paths
        }
        try:
            problem_text = (
                "Definition generated_verification_claim : "
                "Logos.FormalSQL.VerificationConditions.verification_claim_kind :=\n"
                "  Logos.FormalSQL.VerificationConditions.VerificationCountermodel.\n"
                "Theorem generated_queries_verified : True. Proof. exact I. Qed.\n"
            )
            goal_text = (
                "Theorem generated_verification_certificate : True. "
                "Proof. exact I. Qed.\n"
            )
            problem_path.write_text(problem_text, encoding="utf-8")
            checked_problem.write_text(problem_text, encoding="utf-8")
            goal_path.write_text(goal_text, encoding="utf-8")
            checked_goal.write_text(goal_text, encoding="utf-8")
            write_json(
                context_path,
                {
                    "goalModule": {
                        "path": "Goal.v",
                        "sha256": sha256(goal_path),
                        "bytes": goal_path.stat().st_size,
                    }
                },
            )
            context_sha256 = sha256(context_path)
            authority_sha256 = round_record["authorityClosureSha256"]
            problem_sha256 = sha256(problem_path)
            problem_relative = "proof-stage/formal-sql/Problem.v"
            goal_relative = "proof-stage/formal-sql/Goal.v"
            proof["verificationMode"] = "outcome_unconditional"
            proof["backendStatus"] = "proof_complete"
            proof["certification"] = "FORMAL-COUNTERMODEL"
            proof["proofWorkspace"] = {
                "problemPath": problem_relative,
                "goalPath": goal_relative,
                "contextManifestPath": context_relative,
            }
            proof["proofAgentConfiguration"]["context"][
                "manifestSha256"
            ] = context_sha256
            round_record.update(
                {
                    "success": True,
                    "candidateClaim": "formal_countermodel",
                    "candidateProblemCompilePassed": True,
                    "candidateHasFinalTheorem": True,
                    "candidateProblemSha256": problem_sha256,
                    "contextManifestSha256": context_sha256,
                    "authorityClosureSha256": authority_sha256,
                    "proofCheckExitCode": 0,
                    "proofCheckTimedOut": False,
                    "audit": {"passed": True, "findings": []},
                }
            )
            proof["proofAgent"] = json.loads(json.dumps(round_record))
            row["proofMetrics"]["proofSource"].update(
                {"present": True, "sha256": problem_sha256}
            )
            counterexample = {
                "kind": "formalSqlCountermodel",
                "problem_path": problem_relative,
                "goal_path": goal_relative,
                "problem_sha256": problem_sha256,
                "context_manifest_sha256": context_sha256,
                "authority_closure_sha256": authority_sha256,
                "trusted_check_exit_code": 0,
                "theorem": "generated_verification_certificate",
            }
            validate("fixture-case", row, report, source_dir, counterexample)

            counterexample["problem_sha256"] = "0" * 64
            with self.assertRaisesRegex(
                publish_error, "fully bound trusted Rocq certificate"
            ):
                validate("fixture-case", row, report, source_dir, counterexample)
        finally:
            for path, original in originals.items():
                if original is None:
                    path.unlink(missing_ok=True)
                else:
                    path.write_bytes(original)

    def test_rejects_gate_that_completed_after_full_run(self) -> None:
        gate = json.loads(self.original_gate)
        gate["updatedAt"] = "2026-07-23T04:00:00Z"
        write_json(self.gate_summary, gate)
        new_digest = sha256(self.gate_summary)
        summary = json.loads(self.original_summary)
        summary["configuration"]["cohort16Gate"]["sha256"] = new_digest
        for row in summary["results"]:
            row["effectiveConfiguration"]["cohort16GateSha256"] = new_digest
        write_json(self.summary_path, summary)
        self.assert_rejected("did not complete before the full run")

    def test_rejects_gate_treatment_drift_even_when_rehashed(self) -> None:
        gate = json.loads(self.original_gate)
        gate["configuration"]["proofAgent"]["dockerImage"]["imageId"] = (
            "sha256:" + "9" * 64
        )
        write_json(self.gate_summary, gate)
        new_digest = sha256(self.gate_summary)
        summary = json.loads(self.original_summary)
        summary["configuration"]["cohort16Gate"]["sha256"] = new_digest
        for row in summary["results"]:
            row["effectiveConfiguration"]["cohort16GateSha256"] = new_digest
        write_json(self.summary_path, summary)
        self.assert_rejected("cohort16 gate is not a complete compatible 16-case run")

    def test_rejects_current_source_tree_drift(self) -> None:
        self.source_file.write_text("value = 2\n", encoding="utf-8")
        self.assert_rejected("current Logos source tree differs")

    def test_rejects_canonical_lifecycle_alias(self) -> None:
        (self.output / "latest").mkdir()
        self.assert_rejected("forbidden canonical lifecycle alias")


if __name__ == "__main__":
    unittest.main()
