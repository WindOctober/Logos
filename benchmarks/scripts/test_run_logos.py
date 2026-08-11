import ast
import hashlib
import json
import os
import re
import runpy
import shutil
import signal
import socket
import stat
import subprocess
import sys
import tarfile
import tempfile
import textwrap
import threading
import time
import unittest
from pathlib import Path
from unittest import mock


RUNNER = Path(__file__).with_name("run-logos")
DEFAULT_COUNTEREXAMPLE_COMMAND = (
    "codex exec --disable plugins --disable remote_plugin --disable plugin_hooks "
    "--disable skill_mcp_dependency_install --json --model gpt-5.6-sol "
    "-c model_reasoning_effort=medium --dangerously-bypass-approvals-and-sandbox "
    "--skip-git-repo-check -"
)
DEFAULT_COUNTEREXAMPLE_RESUME_COMMAND = (
    "codex exec resume --disable plugins --disable remote_plugin --disable plugin_hooks "
    "--disable skill_mcp_dependency_install --json --model gpt-5.6-sol "
    "-c model_reasoning_effort=medium --dangerously-bypass-approvals-and-sandbox "
    "--skip-git-repo-check {session_id} -"
)
DEFAULT_PROOF_AGENT_COMMAND = (
    "codex exec --disable plugins --disable remote_plugin --disable plugin_hooks "
    "--disable skill_mcp_dependency_install --disable goals --json --model gpt-5.6-sol "
    "-c model_reasoning_effort=medium --dangerously-bypass-approvals-and-sandbox "
    "--skip-git-repo-check --cd /workspace/problem - < proof-agent-prompt.md"
)
DEFAULT_PROOF_AGENT_RESUME_COMMAND = (
    "codex exec resume --disable plugins --disable remote_plugin --disable "
    "plugin_hooks --disable skill_mcp_dependency_install --disable goals --json --model "
    "gpt-5.6-sol -c model_reasoning_effort=medium "
    "--dangerously-bypass-approvals-and-sandbox --skip-git-repo-check "
    "{session_id} - < proof-agent-prompt.md"
)
TRUSTED_LAUNCH_EXCLUDED_VARIABLES = [
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
        "LOGOS_SHARED_ROCQ_CHECKER_RUNTIME_CACHE_DIR",
    ],
    "unlistedEnvironmentPolicy": "excluded_by_env_clear_before_process_start",
    "explicitlyExcludedVariables": TRUSTED_LAUNCH_EXCLUDED_VARIABLES,
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
        "LOGOS_PROOF_AGENT_MEMORY_LIMIT",
        "LOGOS_PROOF_AGENT_STORAGE_LIMIT_BYTES",
        "LOGOS_PROOF_AGENT_TIMEOUT",
    ],
    "unlistedEnvironmentPolicy": "excluded_by_env_clear_before_process_start",
    "explicitlyExcludedVariables": TRUSTED_LAUNCH_EXCLUDED_VARIABLES,
    "explicitlyExcludedPrefixes": ["BASH_FUNC_"],
}


class RocqAuthoritySnapshotUnitTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.runner = runpy.run_path(str(RUNNER), run_name="rocq_snapshot_unit_test")
        cls.runner_error = cls.runner["RunnerError"]

    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.source = self.root / "source"
        self.run_dir = self.root / "run"
        self.run_dir.mkdir()
        self.live_files = []
        for relative, payload in (
            ("vendor/FormalSQL/src/Data.v", b"Definition data := 1.\n"),
            ("theories/FormalSQL/Bridge.v", b"Definition bridge := 2.\n"),
        ):
            source = self.source / relative
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_bytes(payload)
            object_path = source.with_suffix(".vo")
            object_path.write_bytes(b"compiled:" + payload)
            object_mtime = object_path.stat().st_mtime_ns
            os.utime(source, ns=(object_mtime - 1, object_mtime - 1))
            self.live_files.extend((source, object_path))

    def tearDown(self) -> None:
        snapshot = self.run_dir / "runtime/trusted-rocq-authority"
        self.runner["make_tree_writable_for_cleanup"](snapshot)
        manifest = self.run_dir / "trusted-rocq-authority-manifest.json"
        if manifest.exists() and not manifest.is_symlink():
            manifest.chmod(0o600)
        self.temporary.cleanup()

    def namespace_record(self) -> dict[str, object]:
        digest = "a" * 64
        ldd_digest = self.runner["TRUSTED_LDD_SHA256S"][0]
        return {
            "policy": self.runner["TRUSTED_ROCQ_AUTHORITY_NAMESPACE_POLICY"],
            "root": "empty-tmpfs",
            "network": "unshared",
            "runtimeCanonicalPath": "run/runtime/trusted-rocq-switch",
            "runtimeCompiledInstallPrefix": "/source-switch/_opam",
            "runtimePrefixBinding": "same-immutable-snapshot-at-both-prefixes",
            "privateBuildBinding": "read-write-at-exact-absolute-path",
            "systemRuntimeBinding": "captured-files-read-only",
            "bwrapOuterLaunch": {
                "policy": "staged-interpreter-snapshot-libcap-system-closure-v1",
                "interpreterMountPath": "/lib64/ld-linux-x86-64.so.2",
                "interpreterSha256": digest,
                "libraryPath": (
                    "<runtime-snapshot>/_opam/lib:<private-build-system-runtime>"
                ),
                "bwrapSha256": digest,
                "libcapSha256": digest,
            },
            "systemRuntime": {
                "algorithm": "logos-private-rocq-system-runtime-closure-v1",
                "bwrapInterpreterMountPath": "/lib64/ld-linux-x86-64.so.2",
                "inspectionTools": {
                    "ldd": {
                        "selectedPath": "/usr/bin/ldd",
                        "resolvedPath": "/usr/bin/ldd",
                        "sha256": ldd_digest,
                        "bytes": 1,
                    },
                    "readelf": {
                        "selectedPath": "/usr/bin/readelf",
                        "resolvedPath": "/usr/bin/x86_64-linux-gnu-readelf",
                        "sha256": digest,
                        "bytes": 1,
                    },
                },
                "consumerCount": 1,
                "consumers": [
                    {
                        "path": "_opam/bin/rocq",
                        "sha256": digest,
                        "interpreterMountPath": "/lib64/ld-linux-x86-64.so.2",
                        "dependencyMountPaths": ["/lib/x86_64-linux-gnu/libc.so.6"],
                    }
                ],
                "fileCount": 2,
                "files": [
                    {
                        "mountPath": "/lib/x86_64-linux-gnu/libc.so.6",
                        "sourcePath": "/usr/lib/x86_64-linux-gnu/libc.so.6",
                        "stagedName": "libc.so.6",
                        "sha256": digest,
                        "bytes": 1,
                    },
                    {
                        "mountPath": "/lib64/ld-linux-x86-64.so.2",
                        "sourcePath": "/usr/lib/x86_64-linux-gnu/ld-linux-x86-64.so.2",
                        "stagedName": "ld-linux-x86-64.so.2",
                        "sha256": digest,
                        "bytes": 1,
                    },
                ],
            },
        }

    def pin(self, *, resume: bool = False) -> dict[str, object]:
        snapshot = self.snapshot_root()
        manifest = self.run_dir / "trusted-rocq-authority-manifest.json"
        if resume:
            document, digest = self.runner["read_rocq_authority_snapshot_manifest"](
                manifest
            )
            self.runner["verify_rocq_authority_snapshot_tree"](snapshot, document)
            return self.runner["rocq_authority_snapshot_summary"](
                snapshot, manifest, document, digest
            )

        snapshot.mkdir(parents=True)
        inputs = []
        for declaration_index, source in enumerate(
            sorted(path for path in self.live_files if path.suffix == ".v"), start=1
        ):
            relative = source.relative_to(self.source).as_posix()
            copied_source = snapshot / relative
            self.runner["copy_trusted_authority_file"](
                source,
                copied_source,
                hashlib.sha256(source.read_bytes()).hexdigest(),
                source.stat().st_size,
            )
            copied_object = copied_source.with_suffix(".vo")
            copied_object.write_bytes(b"private-compiled:" + source.read_bytes())
            copied_object.chmod(0o444)
            os.utime(copied_object, ns=(1_000_000_000, 1_000_000_000))
            inputs.append(
                {
                    "declarationIndex": declaration_index,
                    "logicalRoot": "SQLFS" if relative.startswith("vendor/") else "Logos",
                    "sourcePath": relative,
                    "sourceSha256": hashlib.sha256(source.read_bytes()).hexdigest(),
                    "sourceBytes": source.stat().st_size,
                    "origin": {"kind": "unit-test-source"},
                }
            )
        pairs = self.runner["trusted_source_object_pairs"](snapshot)
        pair_by_source = {pair["sourcePath"]: pair for pair in pairs}
        outputs = [
            {
                "sourcePath": record["sourcePath"],
                "objectPath": pair_by_source[record["sourcePath"]]["objectPath"],
                "objectSha256": pair_by_source[record["sourcePath"]]["objectSha256"],
                "objectBytes": pair_by_source[record["sourcePath"]]["objectBytes"],
            }
            for record in reversed(inputs)
        ]
        build_log = self.run_dir / "trusted-rocq-authority-build.log"
        build_log.write_text("unit-test private source build\n", encoding="utf-8")
        build_log.chmod(0o444)
        runtime = {
            "manifestPath": "run/trusted-rocq-runtime-manifest.json",
            "manifestSha256": "b" * 64,
            "policy": self.runner["TRUSTED_ROCQ_RUNTIME_SNAPSHOT_POLICY"],
        }
        build_inputs = {
            "frameworkSourceManifestPath": "run/framework-source-tree-manifest.json",
            "frameworkSourceManifestSha256": "c" * 64,
            "controlFiles": [{"path": "_CoqProject"}, {"path": "Makefile"}],
            "vendorSourceCount": 1,
            "logosSourceCount": 1,
            "sources": inputs,
        }
        document = self.runner["rocq_authority_snapshot_document"](
            pairs,
            outputs,
            build_inputs,
            runtime,
            {"path": "runtime/rocq", "sha256": "d" * 64, "bytes": 1},
            {
                "path": self.runner["workspace_display_path"](build_log),
                "sha256": hashlib.sha256(build_log.read_bytes()).hexdigest(),
                "bytes": build_log.stat().st_size,
            },
            self.namespace_record(),
        )
        for directory in sorted(
            (path for path in snapshot.rglob("*") if path.is_dir()), reverse=True
        ):
            directory.chmod(0o555)
        snapshot.chmod(0o555)
        manifest.write_bytes(self.runner["canonical_json_bytes"](document))
        manifest.chmod(0o444)
        self.runner["verify_rocq_authority_snapshot_tree"](snapshot, document)
        return self.runner["rocq_authority_snapshot_summary"](
            snapshot,
            manifest,
            document,
            hashlib.sha256(manifest.read_bytes()).hexdigest(),
        )

    def snapshot_root(self) -> Path:
        return self.run_dir / "runtime/trusted-rocq-authority"

    def test_no_rocq_build_flag_cannot_bypass_private_authority_build(self) -> None:
        parsed = self.runner["argument_parser"]().parse_args(["--no-rocq-build"])
        self.assertTrue(parsed.no_rocq_build)
        source = RUNNER.read_text(encoding="utf-8")
        self.assertNotRegex(source, r"args\.no_rocq_build|if\s+.*no_rocq_build")
        self.assertIn("Compatibility-only flag with no effect", source)

    def test_private_inspection_tool_recheck_rejects_digest_drift(self) -> None:
        records = {
            "ldd": {
                "selectedPath": "/usr/bin/ldd",
                "resolvedPath": "/usr/bin/ldd",
                "sha256": self.runner["TRUSTED_LDD_SHA256S"][0],
                "bytes": 1,
            }
        }
        observed = dict(records["ldd"])
        observed["sha256"] = "0" * 64
        verify = self.runner["verify_private_rocq_inspection_tools"]
        with mock.patch.dict(
            verify.__globals__,
            {"private_rocq_inspection_tool_record": lambda *args, **kwargs: observed},
        ), self.assertRaisesRegex(self.runner_error, "inspection authority drifted"):
            verify(records)

    def test_snapshot_is_physical_read_only_and_resume_isolated(self) -> None:
        record = self.pin()
        snapshot = self.snapshot_root()
        expected_files = {
            "vendor/FormalSQL/src/Data.v",
            "vendor/FormalSQL/src/Data.vo",
            "theories/FormalSQL/Bridge.v",
            "theories/FormalSQL/Bridge.vo",
        }
        observed_files = {
            path.relative_to(snapshot).as_posix()
            for path in snapshot.rglob("*")
            if path.is_file()
        }
        self.assertEqual(observed_files, expected_files)
        for relative in expected_files:
            copied = snapshot / relative
            live = self.source / relative
            self.assertNotEqual(copied.stat().st_ino, live.stat().st_ino)
            self.assertEqual(copied.stat().st_nlink, 1)
            self.assertEqual(stat.S_IMODE(copied.stat().st_mode), 0o444)
        for directory in [snapshot, *[p for p in snapshot.rglob("*") if p.is_dir()]]:
            self.assertEqual(stat.S_IMODE(directory.stat().st_mode), 0o555)

        copied_object = snapshot / "vendor/FormalSQL/src/Data.vo"
        launch_bytes = copied_object.read_bytes()
        self.assertTrue(launch_bytes.startswith(b"private-compiled:"))
        self.assertNotEqual(
            launch_bytes,
            (self.source / "vendor/FormalSQL/src/Data.vo").read_bytes(),
        )
        live_object = self.source / "vendor/FormalSQL/src/Data.vo"
        live_object.write_bytes(b"new external build")
        resumed = self.pin(resume=True)
        self.assertEqual(resumed["manifestSha256"], record["manifestSha256"])
        self.assertEqual(copied_object.read_bytes(), launch_bytes)

    def test_capture_rejects_stale_source_binding_without_publish(self) -> None:
        source = self.source / "vendor/FormalSQL/src/Data.v"
        expected_sha256 = hashlib.sha256(source.read_bytes()).hexdigest()
        expected_bytes = source.stat().st_size
        source.write_bytes(source.read_bytes() + b"(* concurrent mutation *)\n")
        with self.assertRaisesRegex(self.runner_error, "changed during capture"):
            self.runner["copy_trusted_authority_file"](
                source,
                self.root / "unpublished/Data.v",
                expected_sha256,
                expected_bytes,
            )
        self.assertFalse(self.snapshot_root().exists())

    def test_resume_rejects_snapshot_tampering(self) -> None:
        self.pin()
        snapshot = self.snapshot_root()
        target = snapshot / "vendor/FormalSQL/src/Data.vo"
        target.chmod(0o644)
        with self.assertRaisesRegex(self.runner_error, "snapshot file is invalid"):
            self.pin(resume=True)

    def test_snapshot_rejects_extra_and_hardlinked_files(self) -> None:
        self.pin()
        snapshot = self.snapshot_root()
        source_dir = snapshot / "vendor/FormalSQL/src"
        source_dir.chmod(0o755)
        extra = source_dir / "Extra.vo"
        extra.write_bytes(b"extra")
        extra.chmod(0o444)
        source_dir.chmod(0o555)
        with self.assertRaises(self.runner_error):
            self.pin(resume=True)

        source_dir.chmod(0o755)
        extra.unlink()
        original = source_dir / "Data.vo"
        alias = self.root / "same-inode.vo"
        os.link(original, alias)
        source_dir.chmod(0o555)
        try:
            with self.assertRaisesRegex(
                self.runner_error, "snapshot file is invalid"
            ):
                self.pin(resume=True)
        finally:
            alias.unlink()

    def test_snapshot_rejects_missing_and_symlinked_files(self) -> None:
        self.pin()
        snapshot = self.snapshot_root()
        source_dir = snapshot / "vendor/FormalSQL/src"
        target = source_dir / "Data.vo"
        source_dir.chmod(0o755)
        target.unlink()
        source_dir.chmod(0o555)
        with self.assertRaises(self.runner_error):
            self.pin(resume=True)

        source_dir.chmod(0o755)
        target.symlink_to(self.source / "vendor/FormalSQL/src/Data.vo")
        source_dir.chmod(0o555)
        with self.assertRaises(self.runner_error):
            self.pin(resume=True)


class OrdinaryTerminalProblemBindingUnitTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.runner = runpy.run_path(
            str(RUNNER), run_name="ordinary_problem_binding_unit_test"
        )
        cls.runner_error = cls.runner["RunnerError"]

    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.case_dir = Path(self.temporary.name) / "case"
        self.live = self.case_dir / "proof-stage/formal-sql/Problem.v"
        self.checked = (
            self.case_dir
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
            "proofWorkspace": {"problemPath": "proof-stage/formal-sql/Problem.v"}
        }
        self.agent = {
            "round": 1,
            "candidateClaim": "equivalence",
            "authorityClosurePath": (
                "proof-stage/proof-agent/rounds/01/checked-workspace/"
                "authority-closure.txt"
            ),
            "candidateProblemSha256": digest,
        }
        self.metrics = {
            "proofSource": {
                "path": self.runner["workspace_display_path"](self.live),
                "present": True,
                "sha256": digest,
                "bytes": len(self.payload),
            }
        }

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def validate(self) -> None:
        self.runner["validate_ordinary_terminal_problem_binding"](
            self.proof,
            self.agent,
            self.metrics,
            self.case_dir,
            "outcome_unconditional",
            "outcome_unconditional",
        )

    def rebind_payload(self, payload: bytes) -> None:
        self.payload = payload
        self.live.write_bytes(payload)
        self.checked.write_bytes(payload)
        digest = hashlib.sha256(payload).hexdigest()
        self.agent["candidateProblemSha256"] = digest
        self.metrics["proofSource"].update(
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
        self.agent.update(
            {"preconditionSource": source, "preconditionDefinition": definition}
        )
        return definition

    def validate_conditional(self, outcome: str) -> None:
        self.runner["validate_ordinary_terminal_problem_binding"](
            self.proof,
            self.agent,
            self.metrics,
            self.case_dir,
            "conditional",
            outcome,
        )

    def test_accepts_exact_live_checked_candidate_binding(self) -> None:
        self.validate()

    def test_rejects_live_problem_mutation_after_trusted_check(self) -> None:
        self.live.write_bytes(self.payload + b"(* mutable tail *)\n")
        with self.assertRaisesRegex(self.runner_error, "binding drifted"):
            self.validate()

    def test_rejects_noncanonical_workspace_problem_path(self) -> None:
        self.proof["proofWorkspace"]["problemPath"] = "Problem.v"
        with self.assertRaisesRegex(self.runner_error, "paths are not canonical"):
            self.validate()

    def test_rejects_coherently_rebound_countermodel_selector(self) -> None:
        self.rebind_payload(
            self.payload.replace(
                b"VerificationEquivalence", b"VerificationCountermodel"
            )
        )
        with self.assertRaisesRegex(self.runner_error, "unconditional equivalence"):
            self.validate()

    def test_rejects_unconditional_conditional_fields_and_claim_drift(self) -> None:
        self.agent["preconditionSource"] = "derived"
        with self.assertRaisesRegex(self.runner_error, "unconditional equivalence"):
            self.validate()
        self.agent.pop("preconditionSource")
        self.agent["candidateClaim"] = "formal_countermodel"
        with self.assertRaisesRegex(self.runner_error, "claim is not equivalence"):
            self.validate()

    def test_rejects_conditional_external_as_derived_reclassification(self) -> None:
        self.bind_conditional("external")
        with self.assertRaisesRegex(self.runner_error, "provenance binding drifted"):
            self.validate_conditional("conditional_derived")

    def test_accepts_conditional_derived_and_external_bindings(self) -> None:
        for source in ("derived", "external"):
            self.bind_conditional(source)
            self.validate_conditional(f"conditional_{source}")

    def test_rejects_conditional_definition_claim_and_theorem_drift(self) -> None:
        definition = self.bind_conditional("derived")
        self.agent["preconditionDefinition"] = definition + " "
        with self.assertRaisesRegex(self.runner_error, "provenance binding drifted"):
            self.validate_conditional("conditional_derived")
        self.bind_conditional("derived")
        forbidden = self.payload + (
            b"Definition generated_verification_claim : "
            b"Logos.FormalSQL.VerificationConditions.verification_claim_kind := "
            b"Logos.FormalSQL.VerificationConditions.VerificationEquivalence.\n"
        )
        self.rebind_payload(forbidden)
        with self.assertRaisesRegex(self.runner_error, "provenance binding drifted"):
            self.validate_conditional("conditional_derived")
        self.bind_conditional("derived")
        self.rebind_payload(
            self.payload.replace(
                b"generated_queries_equivalent", b"generated_queries_verified"
            )
        )
        with self.assertRaisesRegex(self.runner_error, "mode-specific theorem"):
            self.validate_conditional("conditional_derived")

    def test_rejects_intermediate_directory_symlink(self) -> None:
        checked_parent = self.checked.parent
        external = Path(self.temporary.name) / "external-checked"
        external.mkdir()
        (external / "Problem.v").write_bytes(self.payload)
        shutil.rmtree(checked_parent)
        checked_parent.symlink_to(external, target_is_directory=True)
        with self.assertRaisesRegex(self.runner_error, "not a real directory"):
            self.validate()


FRONTEND_LAUNCH_EXCLUDED_VARIABLES = TRUSTED_LAUNCH_EXCLUDED_VARIABLES + [
    "JAVA_TOOL_OPTIONS",
    "_JAVA_OPTIONS",
    "JDK_JAVA_OPTIONS",
    "CLASSPATH",
    "MAVEN_OPTS",
    "MAVEN_ARGS",
]
FRONTEND_LAUNCH_ENVIRONMENT_POLICY = {
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
    "unlistedEnvironmentPolicy": "excluded_by_env_clear_before_process_start",
    "explicitlyExcludedVariables": FRONTEND_LAUNCH_EXCLUDED_VARIABLES,
    "explicitlyExcludedPrefixes": ["BASH_FUNC_"],
}
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
COMMAND_PROVIDER_ENVIRONMENT_POLICY = {
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
    "unlistedEnvironmentPolicy": "excluded_by_env_clear_before_process_start",
    "explicitlyExcludedVariables": SOLVER_LAUNCH_EXCLUDED_VARIABLES,
    "explicitlyExcludedPrefixes": ["BASH_FUNC_"],
}


class TrustedStackManifestUnitTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.runner = runpy.run_path(str(RUNNER), run_name="runner_unit_test")
        cls.runner_error = cls.runner["RunnerError"]

    def write_stale_solver_marker(self, case_dir: Path, solver_pid: int) -> Path:
        marker = case_dir / self.runner["SOLVER_PID_MARKER"]
        identity = {
            "schemaVersion": 2,
            "pid": solver_pid,
            "processGroupId": solver_pid,
            "uid": os.getuid(),
            "bootId": self.runner["current_boot_id"](),
            "startTimeTicks": 1,
            "executableDevice": 1,
            "executableInode": 1,
            "processIsolationPolicy": self.runner[
                "CASE_PROCESS_ISOLATION_POLICY"
            ],
        }
        marker.write_text(
            self.runner["canonical_solver_pid_marker"](identity), encoding="ascii"
        )
        marker.chmod(0o600)
        return marker

    def test_literal_ldd_rtldlist_parser_fails_closed(self) -> None:
        parse = self.runner["parse_literal_ldd_rtldlist"]
        self.assertEqual(
            parse(b'RTLDLIST="/lib/ld-a.so /lib64/ld-b.so"\n'),
            ["/lib/ld-a.so", "/lib64/ld-b.so"],
        )
        malformed_or_dynamic = (
            b"RTLDLIST=$LOADERS\n",
            b'RTLDLIST="/lib/$ARCH/ld.so"\n',
            b"RTLDLIST='/lib/ld.so'\n",
            b'export RTLDLIST="/lib/ld.so"\n',
            b'RTLDLIST="/lib/ld.so" # trailing shell\n',
            b'RTLDLIST="/lib/ld.so"\nRTLDLIST="/lib/other.so"\n',
        )
        for script in malformed_or_dynamic:
            with self.subTest(script=script), self.assertRaises(self.runner_error):
                parse(script)

    def test_runner_proof_state_policies_match_solver_report_contract(self) -> None:
        proof_stage = (
            RUNNER.parents[2] / "crates/logos-solver/src/engine/proof_stage.rs"
        ).read_text(encoding="utf-8")
        policies = (
            "PROOF_AGENT_COMPILE_CHECKPOINT_POLICY",
            "PROOF_AGENT_SCRATCH_PERSISTENCE_POLICY",
        )
        for name in policies:
            with self.subTest(policy=name):
                declarations = re.findall(
                    rf'const {name}: &str\s*=\s*"([^"]+)";', proof_stage
                )
                self.assertEqual(
                    len(declarations),
                    1,
                    f"expected exactly one literal solver {name} report contract",
                )
                self.assertEqual(self.runner[name], declarations[0])

    def test_trusted_checker_environment_policy_matches_solver_contract(self) -> None:
        proof_stage = (
            RUNNER.parents[2] / "crates/logos-solver/src/engine/proof_stage.rs"
        ).read_text(encoding="utf-8")
        declaration = re.search(
            r"const TRUSTED_CHECKER_EXPLICIT_ENVIRONMENT: &\[&str\] = &\[(.*?)\];",
            proof_stage,
            re.DOTALL,
        )
        self.assertIsNotNone(declaration)
        solver_contract = re.findall(r'"([A-Z0-9_]+)"', declaration.group(1))
        runner_contract = self.runner[
            "trusted_checker_environment_policy_record"
        ]()["explicitContractVariables"]
        self.assertEqual(runner_contract, solver_contract)
        self.assertIn(
            "LOGOS_SHARED_ROCQ_CHECKER_RUNTIME_CACHE_DIR", runner_contract
        )

    def test_dynamic_trusted_cache_binds_ordered_modules_and_final_sources(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            case_dir = Path(temporary)
            formal_root = case_dir / "proof-stage/formal-sql"
            cache_root = (
                case_dir
                / "proof-stage/proof-agent/trusted-diagnostic-cache"
            )
            module_root = cache_root / "ProofModules"
            witness_module_root = cache_root / "WitnessModules"
            final_module_root = formal_root / "ProofModules"
            final_witness_module_root = formal_root / "WitnessModules"
            module_root.mkdir(parents=True)
            witness_module_root.mkdir(parents=True)
            final_module_root.mkdir(parents=True)
            final_witness_module_root.mkdir(parents=True)
            for name in ("Schema.v", "Queries.v", "WitnessData.v", "Witness.v"):
                source = f"Definition {name[:-2].lower()} : True := I.\n".encode()
                (formal_root / name).write_bytes(source)
                (cache_root / name).write_bytes(source)
                (cache_root / f"{name[:-2]}.vo").write_bytes(
                    f"object:{name}".encode()
                )
            module_names = ("CoreFacts.v", "OrderLift.v")
            (module_root / "ORDER").write_text(
                "".join(f"{name}\n" for name in module_names), encoding="utf-8"
            )
            for name in module_names:
                source = f"Lemma {name[:-2]} : True. exact I. Qed.\n".encode()
                (module_root / name).write_bytes(source)
                (module_root / f"{name[:-2]}.vo").write_bytes(
                    f"object:{name}".encode()
                )
                (final_module_root / name).write_bytes(source)
            witness_module_names = ("Table0001Check.v",)
            (witness_module_root / "ORDER").write_text(
                "".join(f"{name}\n" for name in witness_module_names),
                encoding="utf-8",
            )
            for name in witness_module_names:
                source = f"Lemma {name[:-2]} : True. exact I. Qed.\n".encode()
                (witness_module_root / name).write_bytes(source)
                (witness_module_root / f"{name[:-2]}.vo").write_bytes(
                    f"object:{name}".encode()
                )
                (final_witness_module_root / name).write_bytes(source)
            manifest_entries = [
                "Schema.v",
                "Schema.vo",
                "Queries.v",
                "Queries.vo",
                "WitnessData.v",
                "WitnessData.vo",
                "Witness.v",
                "Witness.vo",
                "WitnessModules/ORDER",
            ]
            for name in witness_module_names:
                manifest_entries.extend(
                    (f"WitnessModules/{name}", f"WitnessModules/{name[:-2]}.vo")
                )
            manifest_entries.append("ProofModules/ORDER")
            for name in module_names:
                manifest_entries.extend(
                    (f"ProofModules/{name}", f"ProofModules/{name[:-2]}.vo")
                )
            manifest = "".join(
                f"{hashlib.sha256((cache_root / name).read_bytes()).hexdigest()}  {name}\n"
                for name in manifest_entries
            )
            manifest_path = cache_root / "SHA256SUMS"
            manifest_path.write_text(manifest, encoding="utf-8")
            agent = {
                "diagnosticCacheManifestPath": (
                    "proof-stage/proof-agent/trusted-diagnostic-cache/SHA256SUMS"
                ),
                "diagnosticCacheManifestSha256": hashlib.sha256(
                    manifest.encode()
                ).hexdigest(),
            }

            checked = self.runner["validate_trusted_diagnostic_cache"](
                case_dir, agent
            )
            self.assertEqual(
                list(checked),
                ["ProofModules/CoreFacts.v", "ProofModules/OrderLift.v"],
            )
            self.assertEqual(
                checked["ProofModules/CoreFacts.v"],
                hashlib.sha256(
                    (module_root / "CoreFacts.v").read_bytes()
                ).hexdigest(),
            )

            (final_module_root / "CoreFacts.v").write_text(
                "Lemma forged : True. exact I. Qed.\n", encoding="utf-8"
            )
            with self.assertRaisesRegex(
                self.runner_error, "differs from trusted cache"
            ):
                self.runner["validate_trusted_diagnostic_cache"](case_dir, agent)
            (final_module_root / "CoreFacts.v").write_bytes(
                (module_root / "CoreFacts.v").read_bytes()
            )
            (module_root / "Unordered.v").write_text(
                "Lemma unordered : True. exact I. Qed.\n", encoding="utf-8"
            )
            with self.assertRaisesRegex(
                self.runner_error, "does not describe the exact cache tree"
            ):
                self.runner["validate_trusted_diagnostic_cache"](case_dir, agent)

    def test_all_supported_proof_complete_outcomes_are_classified(self) -> None:
        validate = self.runner["validate_completed_report"]
        with tempfile.TemporaryDirectory() as temporary:
            case_dir = Path(temporary).resolve()
            cases = (
                (
                    "safe_unconditional",
                    "SAFE-UNCONDITIONAL",
                    "safe_unconditional",
                    None,
                ),
                (
                    "outcome_unconditional",
                    "OUTCOME-UNCONDITIONAL",
                    "outcome_unconditional",
                    None,
                ),
                (
                    "conditional_derived",
                    "CONDITIONAL-DERIVED",
                    "conditional",
                    "derived",
                ),
                (
                    "conditional_external",
                    "CONDITIONAL-EXTERNAL",
                    "conditional",
                    "external",
                ),
            )
            for outcome, certification, mode, precondition_source in cases:
                with self.subTest(outcome=outcome):
                    formal_root = case_dir / "proof-stage/formal-sql"
                    checked_root = (
                        case_dir
                        / "proof-stage/proof-agent/rounds/01/checked-workspace"
                    )
                    formal_root.mkdir(parents=True, exist_ok=True)
                    checked_root.mkdir(parents=True, exist_ok=True)
                    if precondition_source is None:
                        problem_source = (
                            "Definition generated_verification_claim : "
                            "Logos.FormalSQL.VerificationConditions.verification_claim_kind := "
                            "Logos.FormalSQL.VerificationConditions.VerificationEquivalence.\n"
                            "Theorem generated_queries_verified : True. "
                            "Proof. exact I. Qed.\n"
                        )
                        precondition_definition = None
                    else:
                        constructor = {
                            "derived": "PreconditionDerived",
                            "external": "PreconditionExternal",
                        }[precondition_source]
                        precondition_definition = (
                            "Definition generated_precondition : "
                            "Logos.FormalSQL.VerificationConditions.verification_condition := "
                            "Logos.FormalSQL.VerificationConditions.ConditionTrue."
                        )
                        problem_source = (
                            "Definition generated_precondition_source : "
                            "Logos.FormalSQL.VerificationConditions.precondition_source := "
                            "Logos.FormalSQL.VerificationConditions."
                            f"{constructor}.\n{precondition_definition}\n"
                            "Theorem generated_queries_equivalent : True. "
                            "Proof. exact I. Qed.\n"
                        )
                    problem_bytes = problem_source.encode()
                    live_problem = formal_root / "Problem.v"
                    checked_problem = checked_root / "Problem.v"
                    live_problem.write_bytes(problem_bytes)
                    checked_problem.write_bytes(problem_bytes)
                    (checked_root / "authority-closure.txt").write_text(
                        "# synthetic terminal closure\n", encoding="utf-8"
                    )
                    problem_digest = hashlib.sha256(problem_bytes).hexdigest()
                    base_metrics = {
                        "proofRoundCount": 1,
                        "diagnosticInvocationCount": 1,
                        "finalProofCheckElapsedMs": 1,
                        "proofSource": {
                            "path": self.runner["workspace_display_path"](
                                live_problem
                            ),
                            "present": True,
                            "sha256": problem_digest,
                            "bytes": len(problem_bytes),
                        },
                    }
                    final_agent = {
                        "round": 1,
                        "success": True,
                        "exitCode": 0,
                        "candidateClaim": "equivalence",
                        "candidateProblemSha256": problem_digest,
                        "authorityClosurePath": (
                            "proof-stage/proof-agent/rounds/01/checked-workspace/"
                            "authority-closure.txt"
                        ),
                        "candidateProblemCompilePassed": True,
                        "candidateHasFinalTheorem": True,
                        "proofCheckExitCode": 0,
                        "proofCheckTimedOut": False,
                        "audit": {"passed": True, "findings": []},
                    }
                    proof = {
                        "backendStatus": "proof_complete",
                        "certification": certification,
                        "verificationMode": mode,
                        "proofWorkspace": {
                            "problemPath": "proof-stage/formal-sql/Problem.v"
                        },
                        "proofSearchTimedOut": False,
                        "proofAgentConfiguration": {"enabled": True},
                        "proofAgent": final_agent,
                        "proofAgentRounds": [final_agent],
                    }
                    if precondition_source is not None:
                        final_agent["preconditionSource"] = precondition_source
                        final_agent["preconditionDefinition"] = precondition_definition
                    report = {
                        "logDir": str(case_dir),
                        "outcome": outcome,
                        "proof": proof,
                    }
                    validate(report, {"proofMetrics": dict(base_metrics)}, case_dir)

                    for field, value in (
                        ("success", False),
                        ("candidateClaim", "formal_countermodel"),
                    ):
                        tampered = json.loads(json.dumps(report))
                        tampered["proof"]["proofAgent"][field] = value
                        with self.assertRaises(self.runner_error):
                            validate(
                                tampered,
                                {"proofMetrics": dict(base_metrics)},
                                case_dir,
                            )
                    tampered = json.loads(json.dumps(report))
                    tampered["proof"]["proofAgent"]["audit"] = {
                        "passed": False,
                        "findings": ["forged"],
                    }
                    tampered["proof"]["proofAgentRounds"][-1] = tampered[
                        "proof"
                    ]["proofAgent"]
                    with self.assertRaisesRegex(
                        self.runner_error, "complete proof-agent"
                    ):
                        validate(
                            tampered,
                            {"proofMetrics": dict(base_metrics)},
                            case_dir,
                        )

                    report["proof"]["certification"] = "OUTCOME-UNCONDITIONAL"
                    if certification != "OUTCOME-UNCONDITIONAL":
                        with self.assertRaisesRegex(
                            self.runner_error, "complete proof-agent"
                        ):
                            validate(
                                report,
                                {"proofMetrics": dict(base_metrics)},
                                case_dir,
                            )

    def test_uncertified_outcomes_require_rust_backend_coherence(self) -> None:
        validate = self.runner["validate_completed_report"]
        with tempfile.TemporaryDirectory() as temporary:
            case_dir = Path(temporary).resolve()

            def report_for(proof: object, outcome: str = "equivalence_verification_incomplete") -> dict:
                return {
                    "logDir": str(case_dir),
                    "outcome": outcome,
                    "proof": proof,
                }

            with self.assertRaisesRegex(self.runner_error, "incoherent proof status"):
                validate(report_for(None), {}, case_dir)
            with self.assertRaisesRegex(
                self.runner_error, "coherent uncertified proof evidence"
            ):
                validate(report_for(None, "needs_manual_review"), {}, case_dir)

            lowering = {
                "backendStatus": "lowering_blocked",
                "certification": None,
                "proofSearchTimedOut": False,
            }
            workspace = {
                "backendStatus": "workspace_generated",
                "certification": None,
                "proofSearchTimedOut": False,
                "proofWorkspace": {},
            }
            run_completed_round = {
                "success": False,
                "exitCode": 0,
                "candidateClaim": None,
                "proofCheckExitCode": None,
            }
            run_completed = {
                "backendStatus": "proof_agent_run_completed",
                "certification": None,
                "proofSearchTimedOut": False,
                "proofWorkspace": {},
                "proofAgent": run_completed_round,
                "proofAgentRounds": [run_completed_round],
            }
            failed_round = {
                "success": False,
                "exitCode": 2,
                "candidateClaim": None,
                "proofCheckExitCode": None,
            }
            failed = {
                "backendStatus": "proof_agent_failed",
                "certification": None,
                "proofSearchTimedOut": False,
                "proofWorkspace": {},
                "proofAgent": failed_round,
                "proofAgentRounds": [failed_round],
            }
            timeout_round = {
                "success": False,
                "exitCode": 124,
                "candidateClaim": None,
                "proofCheckExitCode": None,
            }
            timed_out = {
                "backendStatus": "proof_search_timed_out",
                "certification": None,
                "proofSearchTimedOut": True,
                "proofWorkspace": {},
                "proofAgent": timeout_round,
                "proofAgentRounds": [timeout_round],
            }
            for label, proof in (
                ("lowering", lowering),
                ("workspace", workspace),
                ("run completed", run_completed),
                ("failed", failed),
                ("timed out", timed_out),
            ):
                with self.subTest(valid=label):
                    validate(report_for(proof), {}, case_dir)

            checkpoint_sha256 = "a" * 64
            direct_review_round = {
                "success": False,
                "exitCode": 0,
                "candidateClaim": None,
                "candidateHasFinalTheorem": False,
                "candidateProblemCompilePassed": False,
                "candidateProblemSha256": checkpoint_sha256,
                "activeProblemCompileCheckpointSha256": checkpoint_sha256,
                "proofCheckExitCode": None,
                "proofCheckTimedOut": False,
                "audit": {"passed": True, "findings": []},
                "counterexampleHandoff": {
                    "decision": "needs_manual_review",
                    "reason": "the trusted contract lacks demand events",
                    "guidance": "inspect the binding evaluator",
                },
            }
            direct_review = {
                "backendStatus": "needs_manual_review",
                "certification": None,
                "proofSearchTimedOut": False,
                "proofWorkspace": {},
                "proofAgent": direct_review_round,
                "proofAgentRounds": [direct_review_round],
            }
            validate(
                report_for(direct_review, "needs_manual_review"),
                {},
                case_dir,
            )

            for label, mutate in (
                (
                    "wrong decision",
                    lambda value: value["proofAgent"]["counterexampleHandoff"].__setitem__(
                        "decision", "counterexample_candidate"
                    ),
                ),
                (
                    "empty reason",
                    lambda value: value["proofAgent"]["counterexampleHandoff"].__setitem__(
                        "reason", ""
                    ),
                ),
                (
                    "wrong backend",
                    lambda value: value.__setitem__(
                        "backendStatus", "proof_agent_run_completed"
                    ),
                ),
                (
                    "timeout mixed with review",
                    lambda value: value.__setitem__("proofSearchTimedOut", True),
                ),
                (
                    "missing compile-clean authority",
                    lambda value: value["proofAgent"].__setitem__(
                        "candidateProblemSha256", "b" * 64
                    ),
                ),
                (
                    "failed audit",
                    lambda value: value["proofAgent"]["audit"].__setitem__(
                        "passed", False
                    ),
                ),
            ):
                with self.subTest(invalid_direct_review=label):
                    forged = json.loads(json.dumps(direct_review))
                    mutate(forged)
                    forged["proofAgentRounds"][-1] = forged["proofAgent"]
                    with self.assertRaises(self.runner_error):
                        validate(
                            report_for(forged, "needs_manual_review"),
                            {},
                            case_dir,
                        )

            certified_review = json.loads(json.dumps(direct_review))
            certified_review["certification"] = "OUTCOME-UNCONDITIONAL"
            with self.assertRaises(self.runner_error):
                validate(
                    report_for(certified_review, "needs_manual_review"),
                    {},
                    case_dir,
                )

            counterexample_review_round = {
                "round": 1,
                "assessment": {
                    "decision": "needs_review",
                    "parse": {"success": True, "error": None},
                },
                "proposal": {
                    "decision": "needs_review",
                    "reason": "no finite executable witness is available",
                    "witnessSql": "",
                    "notes": "requires semantic review",
                },
                "validation": None,
            }
            counterexample_handoff_round = {
                "success": False,
                "exitCode": 0,
                "candidateClaim": None,
                "proofCheckExitCode": None,
                "counterexampleHandoff": {
                    "decision": "counterexample_candidate",
                    "reason": "a finite witness may separate the outcomes",
                    "guidance": "try one nonempty input row",
                },
            }
            counterexample_review_proof = {
                "backendStatus": "needs_manual_review",
                "certification": None,
                "proofSearchTimedOut": False,
                "proofWorkspace": {},
                "proofAgent": counterexample_handoff_round,
                "proofAgentRounds": [counterexample_handoff_round],
            }
            counterexample_review_report = report_for(
                counterexample_review_proof, "needs_manual_review"
            )
            counterexample_review_report["counterexample"] = None
            counterexample_review_report["rounds"] = [counterexample_review_round]
            stage_report = {
                "outcome": "needs_manual_review",
                "reason": "counterexample agent requested review",
                "rounds": [counterexample_review_round],
                "counterexample": None,
                "elapsedMs": 1,
                "llmUsage": {},
            }
            stage_report_path = case_dir / "counterexample-stage/report.json"
            stage_report_path.parent.mkdir(parents=True, exist_ok=True)
            stage_report_path.write_text(json.dumps(stage_report))
            validate(counterexample_review_report, {}, case_dir)

            forged_stage_report = dict(stage_report)
            forged_stage_report["rounds"] = []
            stage_report_path.write_text(json.dumps(forged_stage_report))
            with self.assertRaisesRegex(
                self.runner_error, "counterexample-stage authority"
            ):
                validate(counterexample_review_report, {}, case_dir)
            stage_report_path.write_text(json.dumps(stage_report))

            for label, mutate in (
                (
                    "non-review proposal",
                    lambda value: value["rounds"][-1]["proposal"].__setitem__(
                        "decision", "no_candidate"
                    ),
                ),
                (
                    "counterexample attached",
                    lambda value: value.__setitem__("counterexample", {}),
                ),
                (
                    "wrong backend",
                    lambda value: value["proof"].__setitem__(
                        "backendStatus", "proof_agent_run_completed"
                    ),
                ),
                (
                    "timeout mixed with review",
                    lambda value: value["proof"].__setitem__(
                        "proofSearchTimedOut", True
                    ),
                ),
                (
                    "certification attached",
                    lambda value: value["proof"].__setitem__(
                        "certification", "OUTCOME-UNCONDITIONAL"
                    ),
                ),
                (
                    "non-review top-level outcome",
                    lambda value: value.__setitem__(
                        "outcome", "equivalence_verification_incomplete"
                    ),
                ),
            ):
                with self.subTest(invalid_counterexample_review=label):
                    forged = json.loads(json.dumps(counterexample_review_report))
                    mutate(forged)
                    with self.assertRaises(self.runner_error):
                        validate(forged, {}, case_dir)

            validate(report_for(failed, "needs_manual_review"), {}, case_dir)

            unresumable_exit_zero = json.loads(json.dumps(run_completed))
            unresumable_exit_zero["backendStatus"] = "proof_agent_failed"
            unresumable_exit_zero["proofAgent"]["sessionId"] = None
            unresumable_exit_zero["proofAgent"]["error"] = (
                "proof agent output failed deterministic proof audit; proof repair "
                "cannot continue because Codex did not report the expected valid "
                "session UUID"
            )
            unresumable_exit_zero["proofAgentRounds"][-1] = (
                unresumable_exit_zero["proofAgent"]
            )
            validate(report_for(unresumable_exit_zero), {}, case_dir)

            for label, mutate in (
                (
                    "reported timeout without timeout flag",
                    lambda value: value.__setitem__(
                        "backendStatus", "proof_search_timed_out"
                    ),
                ),
                (
                    "timeout flag with completed status",
                    lambda value: value.__setitem__("proofSearchTimedOut", True),
                ),
                (
                    "nonzero failure labeled completed",
                    lambda value: value["proofAgent"].__setitem__("exitCode", 2),
                ),
            ):
                forged = json.loads(json.dumps(run_completed))
                mutate(forged)
                forged["proofAgentRounds"][-1] = forged["proofAgent"]
                with self.subTest(forged=label), self.assertRaisesRegex(
                    self.runner_error, "backend"
                ):
                    validate(report_for(forged), {}, case_dir)

            successful_round = {
                "success": True,
                "exitCode": 0,
                "candidateClaim": "equivalence",
                "proofCheckExitCode": 0,
            }
            forged_success = {
                "backendStatus": "proof_complete",
                "certification": None,
                "proofSearchTimedOut": False,
                "proofWorkspace": {},
                "proofAgent": successful_round,
                "proofAgentRounds": [successful_round],
            }
            with self.assertRaisesRegex(self.runner_error, "uncertified outcome"):
                validate(report_for(forged_success), {}, case_dir)

    def test_lowering_blocked_needs_no_post_lowering_cache_or_context(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            case_dir = Path(temporary).resolve()
            config = mock.Mock(
                verification_mode="outcome-unconditional",
                sql_time_zone="UTC",
                sql_default_collation="C",
                sql_character_classification="C",
                sql_locale_provider="libc",
                sql_server_encoding="UTF8",
                case_timeout_seconds=14_400,
                proof_check_timeout_seconds=420,
                proof_agent_memory_limit_mib=6144,
                proof_agent_storage_limit_mib=2048,
                proof_docker_image_effective="sha256:" + "a" * 64,
                input_files={},
            )
            agent = {
                "enabled": True,
                "command": self.runner["DEFAULT_PROOF_AGENT_COMMAND"],
                "resumeCommand": self.runner["DEFAULT_PROOF_AGENT_RESUME_COMMAND"],
                "timeoutSeconds": 14_100,
                "trustedCheckTimeoutSeconds": 420,
                "memoryLimitMib": 6144,
                "dockerImage": "sha256:" + "a" * 64,
                "sessionRestartAfterFailedRounds": 16,
                "sessionHomePolicy": "isolated_per_generation",
                "diagnosticTransport": "host_unix_broker",
                "diagnosticCachePolicy": (
                    "preflight_built_source_digest_bound_host_only"
                ),
                "diagnosticTimeoutPolicy": (
                    "positive_request_bounded_only_by_current_invocation_deadline"
                ),
                "diagnosticBudgetPolicy": "bounded_by_invocation_deadline",
                "diagnosticCheckerParallelismMax": 1,
                "diagnosticCheckerSchedulingPolicy": (
                    "sequential_host_broker_invocation_deadline_bounded"
                ),
                "compileCheckpointPolicy": self.runner[
                    "PROOF_AGENT_COMPILE_CHECKPOINT_POLICY"
                ],
                "scratchPersistencePolicy": self.runner[
                    "PROOF_AGENT_SCRATCH_PERSISTENCE_POLICY"
                ],
                "writableStorageLimitBytes": 2048 * 1024 * 1024,
                "writableStoragePolicy": (
                    "single_kernel_tmpfs_all_agent_writes_with_read_only_root_v1"
                ),
                "scratchAllowedExtensions": ["v", "md", "txt"],
                "trustedCheckerEnvironmentPolicy": self.runner[
                    "trusted_checker_environment_policy_record"
                ](),
                "proofAgentLauncherEnvironmentPolicy": self.runner[
                    "proof_agent_launcher_environment_policy_record"
                ](),
                "staticPromptAndPrimerBytes": 123,
            }
            proof = {
                "sqlEnvironment": {
                    "defaultCollation": "C",
                    "characterClassification": "C",
                    "localeProvider": "libc",
                    "serverEncoding": "UTF8",
                },
                "verificationMode": "outcome_unconditional",
                "backendStatus": "lowering_blocked",
                "proofAgentConfiguration": agent,
                "proofSearchTimedOut": False,
            }
            report = {
                "logDir": str(case_dir),
                "outcome": "equivalence_verification_incomplete",
                "proof": proof,
            }
            metrics = self.runner["proof_metrics_from_report"](
                report,
                mock.Mock(case_id="fixture"),
                config,
                case_dir,
            )
            self.assertEqual(metrics["proofRoundCount"], 0)
            self.assertEqual(metrics["preflightInvocationCount"], 0)
            self.assertEqual(metrics["staticPromptAndPrimerBytes"], 123)
            self.runner["validate_completed_report"](
                report, {"proofMetrics": metrics}, case_dir
            )

            agent["trustedEnvironmentPreflight"] = {
                "timeoutSeconds": 420,
                "elapsedMs": 1,
                "exitCode": 0,
                "timedOut": False,
            }
            with self.assertRaisesRegex(
                self.runner_error, "post-lowering authority evidence"
            ):
                self.runner["proof_metrics_from_report"](
                    report,
                    mock.Mock(case_id="fixture"),
                    config,
                    case_dir,
                )

    def test_fixed_witness_workspace_transition_is_digest_and_generation_bound(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            case_dir = Path(temporary)
            selected = case_dir / "selected/nonwetune-flat/fixture"
            selected.mkdir(parents=True)
            (selected / "schema.sql").write_text("CREATE TABLE t(x INT);\n")
            (selected / "sql1.sql").write_text("SELECT x FROM t;\n")
            (selected / "sql2.sql").write_text("SELECT x FROM t;\n")
            (selected / "metadata.json").write_text(
                json.dumps({"flatCaseId": "fixture"}), encoding="utf-8"
            )
            case = mock.Mock(
                case_id="nonwetune-flat__fixture",
                flat_case_id="fixture",
                input_dir=selected,
                schema=selected / "schema.sql",
                source=selected / "sql1.sql",
                target=selected / "sql2.sql",
            )
            config = mock.Mock(
                proof_check_timeout_seconds=5,
                verification_mode="outcome-unconditional",
                input_files={
                    case.case_id: {
                        "source": {
                            "sha256": hashlib.sha256(case.source.read_bytes()).hexdigest()
                        },
                        "target": {
                            "sha256": hashlib.sha256(case.target.read_bytes()).hexdigest()
                        },
                    }
                },
            )

            def write_generation(generation: int, problem: bytes) -> tuple[dict, dict]:
                root = (
                    case_dir
                    / "proof-stage/proof-agent/workspace-generations"
                    / f"{generation:04d}"
                )
                preflight = {
                    "timeoutSeconds": 5,
                    "elapsedMs": generation,
                    "exitCode": 0,
                    "timedOut": False,
                }
                preflight_root = root / "trusted-environment-preflight"
                preflight_root.mkdir(parents=True)
                (preflight_root / "stdout.txt").write_bytes(b"")
                (preflight_root / "stderr.txt").write_bytes(b"")
                (preflight_root / "invocation.json").write_text(
                    json.dumps(preflight), encoding="utf-8"
                )
                checkpoint_root = root / "initial-problem-checkpoint"
                checkpoint_root.mkdir()
                (checkpoint_root / "Problem.v").write_bytes(problem)
                (checkpoint_root / "stdout.txt").write_bytes(b"")
                (checkpoint_root / "stderr.txt").write_bytes(b"")
                problem_sha256 = hashlib.sha256(problem).hexdigest()
                invocation = {
                    "sequence": 0,
                    "mode": "problem",
                    "candidateSha256": problem_sha256,
                    "candidatePath": "Problem.v",
                    "purpose": "assembly",
                    "compilePassed": True,
                    "problemCompilePassed": True,
                    "compileCheckpointAdvanced": True,
                    "stdoutSha256": hashlib.sha256(b"").hexdigest(),
                    "stderrSha256": hashlib.sha256(b"").hexdigest(),
                    "requestedTimeoutSeconds": 5,
                    "effectiveTimeoutSeconds": 5,
                    "startedAtUnixMs": 100 + generation,
                    "elapsedMs": generation,
                    "exitCode": 0,
                    "timedOut": False,
                }
                (checkpoint_root / "invocation.json").write_text(
                    json.dumps(invocation), encoding="utf-8"
                )
                evidence = {
                    "workspaceGeneration": generation,
                    "path": (
                        "proof-stage/proof-agent/workspace-generations/"
                        f"{generation:04d}/initial-problem-checkpoint/Problem.v"
                    ),
                    "sha256": problem_sha256,
                    "round": 0,
                    "sequence": 0,
                }
                return preflight, evidence

            preflight_one, _ = write_generation(1, b"Definition g1 := True.\n")
            preflight_two, checkpoint_two = write_generation(
                2, b"Definition g2 := True.\n"
            )
            context_digests = {}
            for index in (1, 2):
                checked = (
                    case_dir
                    / f"proof-stage/proof-agent/rounds/{index:02d}/checked-workspace"
                )
                checked.mkdir(parents=True)
                context_files = {
                    "source.sql": case.source.read_bytes(),
                    "target.sql": case.target.read_bytes(),
                    "query-shape.json": f"{{\"generation\":{index}}}\n".encode(),
                    "ordered-signatures.json": b"[]\n",
                    "observation-certificates.json": b"[]\n",
                    "semantic-primer.md": b"primer\n",
                    "search-rocq-declarations.py": b"#!/usr/bin/python3\n",
                    "Schema.v": f"Definition Schema_{index} := True.\n".encode(),
                    "Queries.v": f"Definition Queries_{index} := True.\n".encode(),
                    "Witness.v": f"Definition Witness_{index} := True.\n".encode(),
                    "Problem.v": f"Definition Problem_{index} := True.\n".encode(),
                    "Goal.v": f"Definition Goal_{index} := True.\n".encode(),
                }
                for name, data in context_files.items():
                    (checked / name).write_bytes(data)

                def context_binding(name):
                    data = context_files[name]
                    return {
                        "path": name,
                        "bytes": len(data),
                        "sha256": hashlib.sha256(data).hexdigest(),
                    }

                manifest = {
                    "schemaVersion": 8,
                    "authority": self.runner["PROOF_CONTEXT_AUTHORITY"],
                    "verificationMode": "outcome_unconditional",
                    "staticPromptAndPrimerBytes": 100,
                    "sourceSql": context_binding("source.sql"),
                    "targetSql": context_binding("target.sql"),
                    "queryShape": context_binding("query-shape.json"),
                    "orderedSignatures": context_binding("ordered-signatures.json"),
                    "observationCertificates": context_binding("observation-certificates.json"),
                    "semanticPrimer": context_binding("semantic-primer.md"),
                    "declarationSearch": context_binding("search-rocq-declarations.py"),
                    "schemaModule": context_binding("Schema.v"),
                    "queriesModule": context_binding("Queries.v"),
                    "witnessModule": context_binding("Witness.v"),
                    "goalModule": context_binding("Goal.v"),
                }
                context_bytes = (json.dumps(manifest, indent=2) + "\n").encode()
                (checked / "context-manifest.json").write_bytes(context_bytes)
                context_digests[index] = hashlib.sha256(context_bytes).hexdigest()
                (checked / "ProofModules").mkdir()
            context_one_sha256 = context_digests[1]
            context_two_sha256 = context_digests[2]

            def write_cache(cache_root: Path, source_root: Path) -> dict:
                module_root = cache_root / "ProofModules"
                module_root.mkdir(parents=True)
                entries = [
                    "Schema.v",
                    "Schema.vo",
                    "Queries.v",
                    "Queries.vo",
                    "Witness.v",
                    "Witness.vo",
                    "ProofModules/ORDER",
                ]
                for name in ("Schema.v", "Queries.v", "Witness.v"):
                    (cache_root / name).write_bytes((source_root / name).read_bytes())
                    (cache_root / f"{name[:-2]}.vo").write_bytes(
                        f"object:{name}".encode()
                    )
                (module_root / "ORDER").write_bytes(b"")
                manifest = "".join(
                    f"{hashlib.sha256((cache_root / name).read_bytes()).hexdigest()}  {name}\n"
                    for name in entries
                )
                (cache_root / "SHA256SUMS").write_text(manifest, encoding="utf-8")
                return {
                    "manifestSha256": hashlib.sha256(manifest.encode()).hexdigest()
                }

            archive_manifest = (
                "proof-stage/proof-agent/workspace-generations/0001/"
                "trusted-diagnostic-cache/SHA256SUMS"
            )
            archive_cache = case_dir / Path(archive_manifest).parent
            archive_record = write_cache(
                archive_cache,
                case_dir / "proof-stage/proof-agent/rounds/01/checked-workspace",
            )
            live_manifest = (
                "proof-stage/proof-agent/trusted-diagnostic-cache/SHA256SUMS"
            )
            live_cache = case_dir / Path(live_manifest).parent
            live_record = write_cache(
                live_cache,
                case_dir / "proof-stage/proof-agent/rounds/02/checked-workspace",
            )

            handoff = {
                "guidance": "construct a typed witness",
                "decision": "counterexample_candidate",
                "reason": "candidate mismatch",
            }
            handoff_reordered = {
                "reason": "candidate mismatch",
                "guidance": "construct a typed witness",
                "decision": "counterexample_candidate",
            }
            self.assertEqual(
                self.runner["canonical_json_sha256"](handoff, "fixture"),
                self.runner["canonical_json_sha256"](
                    handoff_reordered, "fixture"
                ),
            )
            rounds = [
                {
                    "round": 1,
                    "workspaceGeneration": 1,
                    "contextManifestSha256": context_one_sha256,
                    "counterexampleHandoff": handoff,
                    "sessionGeneration": 1,
                    "sessionRestarted": False,
                    "checkpointTransition": "newWorkspaceInitial",
                    "compileCheckpointRestored": False,
                    "sessionId": "session-one",
                    "success": False,
                },
                {
                    "round": 2,
                    "workspaceGeneration": 2,
                    "contextManifestSha256": context_two_sha256,
                    "activeProblemCompileCheckpointSha256": checkpoint_two[
                        "sha256"
                    ],
                    "sessionGeneration": 2,
                    "sessionRestarted": True,
                    "sessionRestartReason": "fixedWitnessReplacement",
                    "checkpointTransition": "newWorkspaceInitial",
                    "compileCheckpointRestored": False,
                    "sessionId": "session-two",
                    "success": False,
                },
            ]
            transition = {
                "afterRound": 1,
                "fromWorkspaceGeneration": 1,
                "toWorkspaceGeneration": 2,
                "reason": "fixedWitnessReplacement",
                "triggeringHandoffSha256": self.runner[
                    "canonical_json_sha256"
                ](handoff_reordered, "fixture"),
                "fromContextManifestSha256": context_one_sha256,
                "toContextManifestSha256": context_two_sha256,
                "fromTrustedDiagnosticCache": {
                    "workspaceGeneration": 1,
                    "manifestPath": archive_manifest,
                    "manifestSha256": archive_record["manifestSha256"],
                },
                "newTrustedEnvironmentPreflight": preflight_two,
                "newInitialProblemCompileCheckpoint": checkpoint_two,
            }
            proof = {"proofWorkspaceTransitions": [transition]}
            state = self.runner["validate_proof_workspace_transitions"](
                proof,
                case,
                rounds,
                {"manifestSha256": context_two_sha256},
                {
                    "trustedEnvironmentPreflight": preflight_one,
                    "diagnosticCacheManifestPath": live_manifest,
                    "diagnosticCacheManifestSha256": live_record["manifestSha256"],
                    "staticPromptAndPrimerBytes": 100,
                },
                case_dir,
                config,
            )
            self.assertEqual(len(state["preflights"]), 2)
            self.assertEqual(set(state["initialCheckpoints"]), {1, 2})
            self.runner["validate_proof_agent_session_sequence"](
                rounds,
                "fixture",
                workspace_transitions_by_round=state["transitionsByRound"],
            )

            transition["triggeringHandoffSha256"] = "0" * 64
            with self.assertRaisesRegex(self.runner_error, "handoff binding"):
                self.runner["validate_proof_workspace_transitions"](
                    proof,
                    case,
                    rounds,
                    {"manifestSha256": context_two_sha256},
                    {
                        "trustedEnvironmentPreflight": preflight_one,
                        "diagnosticCacheManifestPath": live_manifest,
                        "diagnosticCacheManifestSha256": live_record[
                            "manifestSha256"
                        ],
                        "staticPromptAndPrimerBytes": 100,
                    },
                    case_dir,
                    config,
                )

    def test_deterministic_tail_v2_preserves_ordered_modules_and_elapsed_warning(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            case_dir = Path(temporary)
            config = mock.Mock(
                verification_mode="outcome-unconditional",
                proof_check_timeout_seconds=5,
            )

            def binding(path: Path) -> dict:
                return {
                    "path": path.relative_to(case_dir).as_posix(),
                    "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
                    "bytes": path.stat().st_size,
                }

            formal = case_dir / "proof-stage/formal-sql"
            formal_modules = formal / "ProofModules"
            formal_modules.mkdir(parents=True)
            problem = (
                "Definition generated_verification_claim : "
                "Logos.FormalSQL.VerificationConditions.verification_claim_kind :=\n"
                "  Logos.FormalSQL.VerificationConditions.VerificationEquivalence.\n"
                "Theorem generated_queries_verified : True. Proof. exact I. Qed.\n"
            ).encode()
            sources = {
                "Schema.v": b"Definition schema := True.\n",
                "Queries.v": b"Definition queries := True.\n",
                "Witness.v": b"Definition witness := True.\n",
                "Problem.v": problem,
                "Goal.v": b"Theorem goal : True. exact I. Qed.\n",
            }
            for name, data in sources.items():
                (formal / name).write_bytes(data)
            module_source = b"Lemma CoreFacts : True. exact I. Qed.\n"
            (formal_modules / "CoreFacts.v").write_bytes(module_source)

            round_root = case_dir / "proof-stage/proof-agent/rounds/01"
            diagnostic = round_root / "interactive-diagnostics/01"
            checked = diagnostic / "checked-workspace"
            checked.mkdir(parents=True)
            (checked / "Problem.v").write_bytes(problem)
            (diagnostic / "stdout.txt").write_bytes(b"")
            (diagnostic / "stderr.txt").write_bytes(b"")
            candidate_sha256 = hashlib.sha256(problem).hexdigest()
            request = {
                "schemaVersion": 2,
                "nonce": "a" * 64,
                "mode": "problem",
                "candidatePath": "Problem.v",
                "purpose": "assembly",
                "candidateSha256": candidate_sha256,
                "candidateBytes": len(problem),
                "requestedTimeoutSeconds": 5,
            }
            invocation = {
                "sequence": 1,
                "mode": "problem",
                "candidateSha256": candidate_sha256,
                "candidatePath": "Problem.v",
                "purpose": "assembly",
                "compilePassed": True,
                "problemCompilePassed": True,
                "compileCheckpointAdvanced": True,
                "stdoutSha256": hashlib.sha256(b"").hexdigest(),
                "stderrSha256": hashlib.sha256(b"").hexdigest(),
                "requestedTimeoutSeconds": 5,
                "effectiveTimeoutSeconds": 5,
                "startedAtUnixMs": 100,
                "elapsedMs": 1,
                "exitCode": 0,
                "timedOut": False,
            }
            audit = {"passed": True, "scannedFiles": [], "findings": []}
            for name, value in (
                ("request.json", request),
                ("invocation.json", invocation),
                ("audit.json", audit),
            ):
                (diagnostic / name).write_text(json.dumps(value), encoding="utf-8")

            base_error = (
                "proof-agent container produced an unsafe or invalid export archive"
            )
            suffix = (
                "proof repair cannot continue because Codex did not report the "
                "expected valid session UUID"
            )
            run_record = {
                "round": 1,
                "success": False,
                "exitCode": 2,
                "sessionId": None,
                "usageError": (
                    "Codex invocation did not emit exactly one thread.started event"
                ),
                "error": base_error,
                "proofCheckExitCode": None,
                "proofCheckElapsedMs": None,
                "proofCheckTimedOut": False,
                "updatedProblemCompileCheckpointSha256": candidate_sha256,
                "diagnosticCheckerInvocations": [invocation],
            }
            final_round = dict(run_record)
            final_round["error"] = f"{base_error}; {suffix}"
            round_root.mkdir(parents=True, exist_ok=True)
            run_path = round_root / "run.json"
            run_path.write_text(json.dumps(run_record), encoding="utf-8")
            stderr_path = round_root / "stderr.txt"
            stderr_path.write_text(base_error, encoding="utf-8")

            recovery_root = case_dir / "proof-stage/deterministic-tail-recovery"
            staging = recovery_root / "staging-workspace"
            staging_modules = staging / "ProofModules"
            staging_modules.mkdir(parents=True)
            for name, data in sources.items():
                (staging / name).write_bytes(data)
            (staging_modules / "CoreFacts.v").write_bytes(module_source)
            order_path = recovery_root / "proof-module-order.txt"
            order_path.write_text("CoreFacts.v\n", encoding="utf-8")
            ordered_names = [
                "Schema.v",
                "Queries.v",
                "Witness.v",
                "Problem.v",
                "Goal.v",
                "ProofModules/CoreFacts.v",
            ]
            manifest = {
                "schemaVersion": 2,
                "checkpointSha256": candidate_sha256,
                "proofModuleOrder": {
                    "path": "proof-module-order.txt",
                    "sha256": hashlib.sha256(order_path.read_bytes()).hexdigest(),
                    "bytes": order_path.stat().st_size,
                    "modules": ["CoreFacts.v"],
                },
                "files": [
                    {
                        "name": name,
                        "sha256": hashlib.sha256((staging / name).read_bytes()).hexdigest(),
                        "bytes": (staging / name).stat().st_size,
                    }
                    for name in ordered_names
                ],
            }
            manifest_path = recovery_root / "staging-manifest.json"
            manifest_path.write_text(json.dumps(manifest), encoding="utf-8")
            checker = (
                case_dir
                / "proof-stage/proof-agent/trusted-launcher/run-trusted-rocq-check.sh"
            )
            checker.parent.mkdir(parents=True)
            checker.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            trusted_stdout = recovery_root / "trusted-check.stdout.txt"
            trusted_stderr = recovery_root / "trusted-check.stderr.txt"
            trusted_stdout.write_bytes(b"")
            trusted_stderr.write_bytes(b"")

            recovery = {
                "schemaVersion": 1,
                "status": "published",
                "recoveredAt": "2026-07-30T00:00:00Z",
                "claim": "equivalence",
                "sourceFailure": {
                    "round": 1,
                    "agentExitCode": 2,
                    "agentError": final_round["error"],
                    "agentUsageError": final_round["usageError"],
                    "runRecord": binding(run_path),
                    "stderr": binding(stderr_path),
                },
                "checkpoint": {
                    "round": 1,
                    "sequence": 1,
                    "problem": binding(checked / "Problem.v"),
                    "request": binding(diagnostic / "request.json"),
                    "invocation": binding(diagnostic / "invocation.json"),
                    "audit": binding(diagnostic / "audit.json"),
                },
                "stagingWorkspace": {
                    "path": "proof-stage/deterministic-tail-recovery/staging-workspace",
                    "manifest": binding(manifest_path),
                },
                "trustedCheck": {
                    "checker": binding(checker),
                    "timeoutSeconds": 5,
                    "startedAtUnixMs": 200,
                    "elapsedMs": 12_001,
                    "exitCode": 0,
                    "timedOut": False,
                    "stdout": binding(trusted_stdout),
                    "stderr": binding(trusted_stderr),
                },
                "publishedProblem": binding(formal / "Problem.v"),
            }
            self.assertEqual(
                self.runner["validate_deterministic_tail_recovery"](
                    {"deterministicTailRecovery": recovery},
                    [final_round],
                    case_dir,
                    config,
                ),
                12_001,
            )
            warning = self.runner["trusted_elapsed_warning"](
                phase="deterministic_tail_trusted_check",
                timeout_seconds=5,
                elapsed_ms=12_001,
                round_number=1,
            )
            self.assertEqual(warning["overrunMs"], 1_001)

            trusted_check_tamper = json.loads(json.dumps(recovery))
            trusted_check_tamper["trustedCheck"]["exitCode"] = 1
            with self.assertRaisesRegex(
                self.runner_error, "trusted check was not accepted"
            ):
                self.runner["validate_deterministic_tail_recovery"](
                    {"deterministicTailRecovery": trusted_check_tamper},
                    [final_round],
                    case_dir,
                    config,
                )

            staging_binding_tamper = json.loads(json.dumps(recovery))
            staging_binding_tamper["stagingWorkspace"]["manifest"]["sha256"] = (
                "0" * 64
            )
            with self.assertRaisesRegex(self.runner_error, "manifest binding drifted"):
                self.runner["validate_deterministic_tail_recovery"](
                    {"deterministicTailRecovery": staging_binding_tamper},
                    [final_round],
                    case_dir,
                    config,
                )

            order_path.write_text("Other.v\n", encoding="utf-8")
            with self.assertRaisesRegex(self.runner_error, "order binding drifted"):
                self.runner["validate_deterministic_tail_recovery"](
                    {"deterministicTailRecovery": recovery},
                    [final_round],
                    case_dir,
                    config,
                )

    def test_gate_report_accepts_shared_validated_recovered_certificate(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            case_dir = Path(temporary)
            report_path = case_dir / "report.json"
            failed_round = {
                "round": 1,
                "success": False,
                "proofCheckExitCode": None,
                "proofCheckTimedOut": False,
            }
            report = {
                "logDir": str(case_dir),
                "outcome": "outcome_unconditional",
                "rounds": [],
                "proof": {
                    "verificationMode": "outcome_unconditional",
                    "backendStatus": "proof_complete",
                    "certification": "OUTCOME-UNCONDITIONAL",
                    "proofAgentRounds": [failed_round],
                    "deterministicTailRecovery": {
                        "schemaVersion": 1,
                        "status": "published",
                        "claim": "equivalence",
                    },
                },
            }
            report_path.write_text(json.dumps(report), encoding="utf-8")
            expected_metrics = {
                "proofRoundCount": 1,
                "diagnosticInvocationCount": 1,
                "finalProofCheckElapsedMs": 17,
            }
            case = mock.Mock(case_id="fixture")
            config = mock.Mock(verification_mode="outcome-unconditional")
            shared_metrics = mock.Mock(return_value=expected_metrics)

            def shared_completion(
                checked_report: dict,
                result: dict,
                checked_case_dir: Path,
                checked_case: object,
                checked_config: object,
            ) -> None:
                recovery = checked_report["proof"]["deterministicTailRecovery"]
                self.assertEqual(recovery["status"], "published")
                self.assertFalse(
                    any(
                        row.get("proofCheckExitCode") == 0
                        for row in checked_report["proof"]["proofAgentRounds"]
                    )
                )
                self.assertEqual(result["proofMetrics"], expected_metrics)
                self.assertEqual(checked_case_dir, case_dir)
                self.assertIs(checked_case, case)
                self.assertIs(checked_config, config)

            validate_gate = self.runner["validate_gate_report"]
            with mock.patch.dict(
                validate_gate.__globals__,
                {
                    "proof_metrics_from_report": shared_metrics,
                    "validate_completed_report": shared_completion,
                },
            ):
                validate_gate(
                    report_path,
                    case,
                    config,
                    expected_metrics,
                )
                with self.assertRaisesRegex(
                    self.runner_error, "proof metrics drifted"
                ):
                    validate_gate(
                        report_path,
                        case,
                        config,
                        {**expected_metrics, "finalProofCheckElapsedMs": 18},
                    )
            shared_metrics.assert_called_with(report, case, config, case_dir)

    def test_gate_completed_return_code_allows_only_strict_crash_recovery(
        self,
    ) -> None:
        coherent = self.runner["completed_return_code_is_coherent"]
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
            ("terminalizedByInvocation", True),
            ("reportEvidence", {"present": False}),
            ("runnerError", "framework failure"),
        ):
            with self.subTest(field=field, value=value):
                forged = dict(recovered)
                forged[field] = value
                self.assertFalse(coherent(forged))
        self.assertTrue(coherent({"status": "completed", "returnCode": 0}))
        self.assertFalse(coherent({"status": "completed", "returnCode": False}))
        self.assertFalse(coherent({"status": "completed", "returnCode": 7}))

    def test_missing_session_requires_terminal_handoff_or_fixed_witness_transition(
        self,
    ) -> None:
        handoff = {
            "decision": "counterexample_candidate",
            "reason": "candidate outcome difference",
            "guidance": "validate the concrete database witness",
        }
        missing_session = {
            "workspaceGeneration": 1,
            "sessionGeneration": 1,
            "sessionRestarted": False,
            "checkpointTransition": "newWorkspaceInitial",
            "compileCheckpointRestored": False,
            "sessionId": None,
            "success": False,
            "exitCode": 2,
            "usageError": (
                "Codex invocation did not emit exactly one thread.started event"
            ),
            "error": (
                "proof-agent container produced an unsafe or invalid export archive; "
                "proof repair cannot continue because Codex did not report the "
                "expected valid session UUID"
            ),
            "candidateClaim": None,
            "proofCheckExitCode": None,
            "counterexampleHandoff": handoff,
        }
        exact_handoff = self.runner[
            "terminal_round_has_unavailable_counterexample_handoff"
        ](missing_session)
        self.assertTrue(exact_handoff)
        self.runner["validate_proof_agent_session_sequence"](
            [missing_session],
            "terminal handoff",
            allow_terminal_unavailable_session=exact_handoff,
            workspace_transitions_by_round={},
        )

        malformed_handoff = json.loads(json.dumps(missing_session))
        malformed_handoff["counterexampleHandoff"]["decision"] = "continue"
        allow_malformed = self.runner[
            "terminal_round_has_unavailable_counterexample_handoff"
        ](malformed_handoff)
        self.assertFalse(allow_malformed)
        with self.assertRaisesRegex(self.runner_error, "has no sessionId"):
            self.runner["validate_proof_agent_session_sequence"](
                [malformed_handoff],
                "terminal continue",
                allow_terminal_unavailable_session=allow_malformed,
                workspace_transitions_by_round={},
            )

        fresh_generation = {
            "workspaceGeneration": 2,
            "sessionGeneration": 2,
            "sessionRestarted": True,
            "sessionRestartReason": "fixedWitnessReplacement",
            "checkpointTransition": "newWorkspaceInitial",
            "compileCheckpointRestored": False,
            "sessionId": "019f8c94-8ab5-7762-8e73-ee0f4f3af9de",
            "success": False,
        }
        self.runner["validate_proof_agent_session_sequence"](
            [missing_session, fresh_generation],
            "fixed witness transition",
            workspace_transitions_by_round={1: {"toWorkspaceGeneration": 2}},
        )

        changed_before_fixed_witness = {
            "workspaceGeneration": 1,
            "sessionGeneration": 1,
            "sessionRestarted": False,
            "checkpointTransition": "continued",
            "compileCheckpointRestored": False,
            "sessionId": "119f8c94-8ab5-7762-8e73-ee0f4f3af9de",
            "success": False,
            "exitCode": 0,
            "error": (
                "resumed Codex session changed from the expected session; proof repair "
                "cannot continue because Codex did not report the expected valid session UUID"
            ),
        }
        self.runner["validate_proof_agent_session_sequence"](
            [
                {
                    **missing_session,
                    "sessionId": "019f8c94-8ab5-7762-8e73-ee0f4f3af9de",
                    "exitCode": 0,
                    "usageError": None,
                    "error": "proof candidate needs repair",
                    "counterexampleHandoff": None,
                },
                changed_before_fixed_witness,
                {
                    **fresh_generation,
                    "sessionId": "219f8c94-8ab5-7762-8e73-ee0f4f3af9de",
                },
            ],
            "changed session followed by fixed witness transition",
            workspace_transitions_by_round={2: {"toWorkspaceGeneration": 2}},
        )
        with self.assertRaisesRegex(self.runner_error, "session changed"):
            self.runner["validate_proof_agent_session_sequence"](
                [
                    {
                        **missing_session,
                        "sessionId": "019f8c94-8ab5-7762-8e73-ee0f4f3af9de",
                        "exitCode": 0,
                        "usageError": None,
                        "error": "proof candidate needs repair",
                        "counterexampleHandoff": None,
                    },
                    changed_before_fixed_witness,
                ],
                "changed session without fixed witness transition",
                workspace_transitions_by_round={},
            )

        trusted_success_after_changed_session = {
            **changed_before_fixed_witness,
            "success": True,
            "usageError": (
                "resumed Codex session changed from "
                "019f8c94-8ab5-7762-8e73-ee0f4f3af9de to "
                "119f8c94-8ab5-7762-8e73-ee0f4f3af9de"
            ),
            "error": None,
        }
        self.runner["validate_proof_agent_session_sequence"](
            [
                {
                    **missing_session,
                    "sessionId": "019f8c94-8ab5-7762-8e73-ee0f4f3af9de",
                    "exitCode": 0,
                    "usageError": None,
                    "error": "proof candidate needs repair",
                    "counterexampleHandoff": None,
                },
                trusted_success_after_changed_session,
            ],
            "trusted success after changed session telemetry",
            allow_terminal_unavailable_session=True,
            workspace_transitions_by_round={},
        )
        with self.assertRaisesRegex(self.runner_error, "session changed"):
            self.runner["validate_proof_agent_session_sequence"](
                [
                    {
                        **missing_session,
                        "sessionId": "019f8c94-8ab5-7762-8e73-ee0f4f3af9de",
                        "exitCode": 0,
                        "usageError": None,
                        "error": "proof candidate needs repair",
                        "counterexampleHandoff": None,
                    },
                    trusted_success_after_changed_session,
                ],
                "unbound changed session success telemetry",
                workspace_transitions_by_round={},
            )

        established_session = {
            "workspaceGeneration": 1,
            "sessionGeneration": 1,
            "sessionRestarted": False,
            "checkpointTransition": "newWorkspaceInitial",
            "compileCheckpointRestored": False,
            "sessionId": "019f8c94-8ab5-7762-8e73-ee0f4f3af9de",
            "success": False,
        }
        changed_session = {
            "workspaceGeneration": 1,
            "sessionGeneration": 1,
            "sessionRestarted": False,
            "checkpointTransition": "continued",
            "compileCheckpointRestored": False,
            "sessionId": "119f8c94-8ab5-7762-8e73-ee0f4f3af9de",
            "success": False,
            "exitCode": 0,
            "error": (
                "resumed Codex session changed; proof repair cannot continue because "
                "Codex did not report the expected valid session UUID"
            ),
        }
        self.runner["validate_proof_agent_session_sequence"](
            [established_session, changed_session],
            "terminal changed session failure",
            allow_terminal_unavailable_session=True,
            workspace_transitions_by_round={},
        )
        with self.assertRaisesRegex(self.runner_error, "session changed"):
            self.runner["validate_proof_agent_session_sequence"](
                [established_session, changed_session],
                "nonterminal changed session",
                workspace_transitions_by_round={},
            )

        changed_session["candidateClaim"] = None
        changed_session["proofCheckExitCode"] = None
        changed_session["counterexampleHandoff"] = handoff
        terminal_report = {
            "outcome": "not_equivalent",
            "counterexample": {"kind": "dataDifference"},
        }
        strict_terminal = self.runner[
            "report_has_strict_terminal_counterexample_handoff"
        ](terminal_report, changed_session)
        self.assertTrue(strict_terminal)
        self.runner["validate_proof_agent_session_sequence"](
            [established_session, changed_session],
            "terminal changed-session handoff",
            allow_terminal_unavailable_session=(
                strict_terminal
                and self.runner["round_has_unresumable_session_suffix"](
                    changed_session
                )
            ),
            workspace_transitions_by_round={},
        )

        manual_report = {"outcome": "needs_manual_review", "counterexample": None}
        self.assertFalse(
            self.runner["report_has_strict_terminal_counterexample_handoff"](
                manual_report, changed_session
            )
        )
        manual_proof = {
            "proofWorkspace": {},
            "proofAgentRounds": [changed_session],
            "proofAgent": changed_session,
            "proofSearchTimedOut": False,
            "deterministicTailRecovery": None,
            "certification": None,
            "backendStatus": "proof_agent_failed",
        }
        self.assertEqual(
            self.runner["validate_proof_backend_coherence"](
                manual_report, manual_proof
            ),
            "proof_agent_failed",
        )
        forged_manual_terminal = dict(manual_proof)
        forged_manual_terminal["backendStatus"] = "proof_agent_run_completed"
        with self.assertRaisesRegex(
            self.runner_error, "differs from Rust evidence mapping"
        ):
            self.runner["validate_proof_backend_coherence"](
                manual_report, forged_manual_terminal
            )

        checkpoint_sha256 = "a" * 64
        direct_manual_round = {
            **changed_session,
            "candidateClaim": None,
            "candidateHasFinalTheorem": False,
            "candidateProblemCompilePassed": False,
            "candidateProblemSha256": checkpoint_sha256,
            "activeProblemCompileCheckpointSha256": checkpoint_sha256,
            "proofCheckExitCode": None,
            "proofCheckTimedOut": False,
            "audit": {"passed": True, "findings": []},
            "counterexampleHandoff": {
                "decision": "needs_manual_review",
                "reason": "trusted demand semantics are unavailable",
                "guidance": "inspect the binding evaluator",
            },
        }
        self.assertTrue(
            self.runner["report_has_direct_manual_review"](
                manual_report, direct_manual_round
            )
        )
        self.runner["validate_proof_agent_session_sequence"](
            [established_session, direct_manual_round],
            "direct manual review with unavailable terminal session",
            allow_terminal_unavailable_session=True,
            workspace_transitions_by_round={},
        )
        direct_manual_proof = {
            "proofWorkspace": {},
            "proofAgentRounds": [direct_manual_round],
            "proofAgent": direct_manual_round,
            "proofSearchTimedOut": False,
            "deterministicTailRecovery": None,
            "certification": None,
            "backendStatus": "needs_manual_review",
        }
        self.assertEqual(
            self.runner["validate_proof_backend_coherence"](
                manual_report, direct_manual_proof
            ),
            "needs_manual_review",
        )

    def test_cid_only_cleanup_preserves_artifacts_without_touching_docker(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            case_dir = Path(temporary) / "case"
            host_tmp = case_dir / "proof-stage/proof-agent/host-tmp"
            host_tmp.mkdir(parents=True)
            cid_path = host_tmp / ".round-fixture.container.cid"
            container_id = "d" * 64
            cid_path.write_text(container_id, encoding="ascii")
            evidence = case_dir / "proof-stage/proof-agent/rounds/01/evidence.json"
            evidence.parent.mkdir(parents=True)
            evidence.write_text("trusted evidence", encoding="utf-8")
            other_host_tmp = (
                Path(temporary)
                / "other-case/proof-stage/proof-agent/host-tmp/round-other"
            )
            other_host_tmp.mkdir(parents=True)
            with mock.patch.object(self.runner["subprocess"], "run") as run:
                with self.assertRaisesRegex(
                    self.runner_error, "cidfile has no matching managed identity"
                ):
                    self.runner["cleanup_case_proof_containers"](case_dir)
            run.assert_not_called()
            self.assertTrue(cid_path.is_file())
            self.assertTrue(host_tmp.is_dir())
            self.assertEqual(evidence.read_text(encoding="utf-8"), "trusted evidence")
            self.assertTrue(other_host_tmp.is_dir())

    def test_proof_host_cleanup_without_container_removes_only_host_tmp(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            case_dir = Path(temporary) / "case"
            host_tmp = case_dir / "proof-stage/proof-agent/host-tmp"
            (host_tmp / "round-fixture/scratch").mkdir(parents=True)
            (host_tmp / "round-fixture/scratch/work.v").write_text(
                "temporary", encoding="utf-8"
            )
            evidence = case_dir / "proof-stage/formal-sql/Problem.v"
            evidence.parent.mkdir(parents=True)
            evidence.write_text("Definition retained := True.", encoding="utf-8")
            with mock.patch.object(self.runner["subprocess"], "run") as run:
                self.runner["cleanup_case_proof_containers"](case_dir)
            run.assert_not_called()
            self.assertFalse(host_tmp.exists())
            self.assertTrue(evidence.is_file())

    def test_proof_host_cleanup_preserves_stale_cidfile_without_identity(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            case_dir = Path(temporary) / "case"
            host_tmp = case_dir / "proof-stage/proof-agent/host-tmp"
            host_tmp.mkdir(parents=True)
            container_id = "e" * 64
            (host_tmp / ".round-stale.container.cid").write_text(
                container_id, encoding="ascii"
            )
            with mock.patch.object(self.runner["subprocess"], "run") as run:
                with self.assertRaisesRegex(
                    self.runner_error, "cidfile has no matching managed identity"
                ):
                    self.runner["cleanup_case_proof_containers"](case_dir)
            run.assert_not_called()
            self.assertTrue(host_tmp.is_dir())

    def test_missing_container_diagnostic_matching_is_case_insensitive(self) -> None:
        matches = self.runner["docker_diagnostic_reports_missing_container"]
        self.assertTrue(matches("Error: No such object: logos-proof-deadbeef"))
        self.assertTrue(matches("error: no such container: logos-proof-deadbeef"))
        self.assertFalse(matches("error: no such image: logos-proof-deadbeef"))
        self.assertFalse(matches("permission denied"))

    def test_launcher_and_outer_cleanup_refuse_cid_without_identity(self) -> None:
        launcher_path = (
            RUNNER.parents[2]
            / "crates/logos-solver/scripts/run-proof-agent-docker.sh"
        )
        launcher = launcher_path.read_text(encoding="utf-8")
        start = launcher.index("cleanup() {")
        end = launcher.index("\n}\n\ntrap cleanup EXIT", start) + len("\n}\n")
        cleanup_source = launcher[start:end]
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            case_dir = root / "case"
            host_tmp = case_dir / "proof-stage/proof-agent/host-tmp"
            host_tmp.mkdir(parents=True)
            cid_path = host_tmp / ".round-fixture.container.cid"
            container_id = "c" * 64
            cid_path.write_text(container_id, encoding="ascii")
            unrelated_cid = root / "other-case/.round-other.container.cid"
            unrelated_cid.parent.mkdir()
            unrelated_cid.write_text("d" * 64, encoding="ascii")
            snippet = (
                "set -u\n"
                "AUTHORITY_STAGE=\nEXPORT_STAGE=\nHANDOFF_STAGE=\n"
                "DOCKER_STDOUT=\nDOCKER_STDERR=\n"
                'CONTAINER_CID_FILE="$1"\n'
                "CONTAINER_IDENTITY_FILE=\nCONTAINER_NAME=\n"
                "CONTAINER_CLEANUP_TOKEN=\n"
                "docker() { echo 'transient daemon failure' >&2; return 1; }\n"
                + cleanup_source
                + "cleanup\n"
            )
            failed_cleanup = subprocess.run(
                ["bash", "-c", snippet, "launcher-cleanup-test", str(cid_path)],
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                check=False,
            )
            self.assertEqual(failed_cleanup.returncode, 0, failed_cleanup.stderr)
            self.assertTrue(cid_path.is_file())
            self.assertIn(
                "preserving proof-agent cidfile without managed identity",
                failed_cleanup.stderr,
            )

            with mock.patch.object(self.runner["subprocess"], "run") as docker_run:
                with self.assertRaisesRegex(
                    self.runner_error, "cidfile has no matching managed identity"
                ):
                    self.runner["cleanup_case_proof_containers"](case_dir)
            docker_run.assert_not_called()
            self.assertTrue(cid_path.is_file())
            self.assertTrue(host_tmp.is_dir())
            self.assertTrue(unrelated_cid.is_file())

    def test_proof_host_cleanup_recovers_empty_cid_from_managed_identity(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            case_dir = Path(temporary) / "case"
            host_tmp = case_dir / "proof-stage/proof-agent/host-tmp"
            host_tmp.mkdir(parents=True)
            prefix = host_tmp / ".round-empty"
            cid_path = prefix.with_name(prefix.name + ".container.cid")
            identity_path = prefix.with_name(
                prefix.name + ".container.identity.json"
            )
            cid_path.write_bytes(b"")
            token = "a" * 64
            name = f"logos-proof-{token}"
            identity_path.write_text(
                json.dumps(
                    {
                        "schemaVersion": 1,
                        "cidFile": cid_path.name,
                        "containerName": name,
                        "cleanupToken": token,
                        "labels": {
                            self.runner["PROOF_CONTAINER_MANAGED_LABEL"]: "true",
                            self.runner["PROOF_CONTAINER_TOKEN_LABEL"]: token,
                        },
                    }
                )
                + "\n",
                encoding="utf-8",
            )
            identity_path.chmod(0o600)
            container_id = "b" * 64
            inspected = subprocess.CompletedProcess(
                ["docker", "inspect"],
                0,
                f"{container_id}|/{name}|true|{token}\n".encode("ascii"),
                b"",
            )
            removed = subprocess.CompletedProcess(
                ["docker", "rm", "-f", container_id], 0, b"", b""
            )
            with mock.patch.object(
                self.runner["subprocess"], "run", side_effect=[inspected, removed]
            ) as run:
                self.runner["cleanup_case_proof_containers"](case_dir)
            self.assertEqual(run.call_count, 2)
            inspect_argv = run.call_args_list[0].args[0]
            self.assertEqual(inspect_argv[:3], ["docker", "inspect", "--format"])
            self.assertEqual(
                inspect_argv[3],
                '{{printf "%s|%s|%s|%s" .Id .Name '
                '(index .Config.Labels "org.logos.proof-agent.managed") '
                '(index .Config.Labels "org.logos.proof-agent.cleanup-token")}}',
            )
            self.assertEqual(inspect_argv[-1], name)
            self.assertEqual(
                run.call_args_list[1].args[0],
                ["docker", "rm", "-f", container_id],
            )
            self.assertFalse(host_tmp.exists())

    def test_proof_host_cleanup_never_removes_name_reused_with_wrong_label(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            case_dir = Path(temporary) / "case"
            host_tmp = case_dir / "proof-stage/proof-agent/host-tmp"
            host_tmp.mkdir(parents=True)
            prefix = host_tmp / ".round-forged"
            cid_path = prefix.with_name(prefix.name + ".container.cid")
            identity_path = prefix.with_name(
                prefix.name + ".container.identity.json"
            )
            cid_path.write_bytes(b"")
            token = "c" * 64
            name = f"logos-proof-{token}"
            identity_path.write_text(
                json.dumps(
                    {
                        "schemaVersion": 1,
                        "cidFile": cid_path.name,
                        "containerName": name,
                        "cleanupToken": token,
                        "labels": {
                            self.runner["PROOF_CONTAINER_MANAGED_LABEL"]: "true",
                            self.runner["PROOF_CONTAINER_TOKEN_LABEL"]: token,
                        },
                    }
                )
                + "\n",
                encoding="utf-8",
            )
            identity_path.chmod(0o600)
            container_id = "d" * 64
            forged = subprocess.CompletedProcess(
                ["docker", "inspect"],
                0,
                f"{container_id}|/{name}|true|{'e' * 64}\n".encode("ascii"),
                b"",
            )
            with mock.patch.object(
                self.runner["subprocess"], "run", return_value=forged
            ) as run:
                with self.assertRaisesRegex(
                    self.runner_error, "container identity mismatch"
                ):
                    self.runner["cleanup_case_proof_containers"](case_dir)
            run.assert_called_once()
            self.assertTrue(cid_path.is_file())
            self.assertTrue(identity_path.is_file())

    def test_empty_cid_retries_until_delayed_managed_name_is_visible(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            case_dir = Path(temporary) / "case"
            host_tmp = case_dir / "proof-stage/proof-agent/host-tmp"
            host_tmp.mkdir(parents=True)
            prefix = host_tmp / ".round-delayed"
            cid_path = prefix.with_name(prefix.name + ".container.cid")
            identity_path = prefix.with_name(
                prefix.name + ".container.identity.json"
            )
            cid_path.write_bytes(b"")
            token = "f" * 64
            name = f"logos-proof-{token}"
            identity_path.write_text(
                json.dumps(
                    {
                        "schemaVersion": 1,
                        "cidFile": cid_path.name,
                        "containerName": name,
                        "cleanupToken": token,
                        "labels": {
                            self.runner["PROOF_CONTAINER_MANAGED_LABEL"]: "true",
                            self.runner["PROOF_CONTAINER_TOKEN_LABEL"]: token,
                        },
                    }
                )
                + "\n",
                encoding="utf-8",
            )
            identity_path.chmod(0o600)
            missing = subprocess.CompletedProcess(
                ["docker", "inspect"],
                1,
                b"",
                f"error: no such object: {name}\n".encode("ascii"),
            )
            container_id = "1" * 64
            visible = subprocess.CompletedProcess(
                ["docker", "inspect"],
                0,
                f"{container_id}|/{name}|true|{token}\n".encode("ascii"),
                b"",
            )
            removed = subprocess.CompletedProcess(
                ["docker", "rm", "-f", container_id], 0, b"", b""
            )
            cleanup = self.runner["cleanup_case_proof_containers"]
            with (
                mock.patch.object(
                    self.runner["subprocess"],
                    "run",
                    side_effect=[missing, visible, removed],
                ) as run,
                mock.patch.object(
                    cleanup.__globals__["time"],
                    "monotonic",
                    side_effect=[0.0, 1.1],
                ),
                mock.patch.object(cleanup.__globals__["time"], "sleep"),
            ):
                cleanup(case_dir)
            self.assertEqual(run.call_count, 3)
            self.assertFalse(host_tmp.exists())

    def test_empty_cid_unresolved_after_bound_preserves_cleanup_authority(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            case_dir = Path(temporary) / "case"
            host_tmp = case_dir / "proof-stage/proof-agent/host-tmp"
            host_tmp.mkdir(parents=True)
            prefix = host_tmp / ".round-unresolved"
            cid_path = prefix.with_name(prefix.name + ".container.cid")
            identity_path = prefix.with_name(
                prefix.name + ".container.identity.json"
            )
            cid_path.write_bytes(b"")
            token = "2" * 64
            name = f"logos-proof-{token}"
            identity_path.write_text(
                json.dumps(
                    {
                        "schemaVersion": 1,
                        "cidFile": cid_path.name,
                        "containerName": name,
                        "cleanupToken": token,
                        "labels": {
                            self.runner["PROOF_CONTAINER_MANAGED_LABEL"]: "true",
                            self.runner["PROOF_CONTAINER_TOKEN_LABEL"]: token,
                        },
                    }
                )
                + "\n",
                encoding="utf-8",
            )
            identity_path.chmod(0o600)
            missing = subprocess.CompletedProcess(
                ["docker", "inspect"],
                1,
                b"",
                f"Error: No such object: {name}\n".encode("ascii"),
            )
            cleanup = self.runner["cleanup_case_proof_containers"]
            with (
                mock.patch.object(
                    self.runner["subprocess"], "run", return_value=missing
                ) as run,
                mock.patch.object(
                    cleanup.__globals__["time"],
                    "monotonic",
                    side_effect=[0.0, 31.0],
                ),
            ):
                with self.assertRaisesRegex(
                    self.runner_error, "creation remained ambiguous"
                ):
                    cleanup(case_dir)
            run.assert_called_once()
            self.assertTrue(cid_path.is_file())
            self.assertTrue(identity_path.is_file())

    def test_proof_host_cleanup_rejects_symlink_redirection(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            case_dir = root / "case"
            proof_agent = case_dir / "proof-stage/proof-agent"
            proof_agent.mkdir(parents=True)
            external = root / "external"
            external.mkdir()
            marker = external / "keep"
            marker.write_text("outside", encoding="utf-8")
            os.symlink(external, proof_agent / "host-tmp")
            with mock.patch.object(self.runner["subprocess"], "run") as run:
                with self.assertRaises(self.runner_error):
                    self.runner["cleanup_case_proof_containers"](case_dir)
            run.assert_not_called()
            self.assertEqual(marker.read_text(encoding="utf-8"), "outside")

    def test_proof_host_cleanup_rejects_symlinked_cidfile(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            case_dir = root / "case"
            host_tmp = case_dir / "proof-stage/proof-agent/host-tmp"
            host_tmp.mkdir(parents=True)
            external_cid = root / "external.cid"
            external_cid.write_text("d" * 64, encoding="ascii")
            os.symlink(external_cid, host_tmp / ".round-fixture.container.cid")
            with mock.patch.object(self.runner["subprocess"], "run") as run:
                with self.assertRaises(self.runner_error):
                    self.runner["cleanup_case_proof_containers"](case_dir)
            run.assert_not_called()
            self.assertEqual(external_cid.read_text(encoding="ascii"), "d" * 64)

    def test_proof_host_cleanup_removes_only_exact_sidecar_bound_socket_dir(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            socket_root = root / "tmp"
            socket_root.mkdir()
            case_dir = root / "case"
            host_tmp = case_dir / "proof-stage/proof-agent/host-tmp"
            host_tmp.mkdir(parents=True)
            solver_pid = 424242
            marker = self.write_stale_solver_marker(case_dir, solver_pid)
            directory_name = f"logos-pds-{solver_pid}-bound123"
            socket_directory = socket_root / directory_name
            socket_directory.mkdir(mode=0o700)
            broker = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
            broker.bind(str(socket_directory / "socket"))
            broker.close()
            sidecar = host_tmp / (
                f".diagnostic-socket-{solver_pid}-01-{directory_name}.json"
            )
            sidecar.write_text(
                json.dumps(
                    {
                        "schemaVersion": 1,
                        "solverPid": solver_pid,
                        "directory": str(socket_directory),
                    }
                )
                + "\n",
                encoding="utf-8",
            )
            sidecar.chmod(0o600)
            pending = host_tmp / (
                f".pending-diagnostic-socket-{solver_pid}-01-{directory_name}.tmp"
            )
            pending.write_text("publication interrupted", encoding="utf-8")
            reserved_only_name = f"logos-pds-{solver_pid}-reserved-only"
            reserved_only = host_tmp / (
                f".diagnostic-socket-{solver_pid}-100-{reserved_only_name}.json"
            )
            reserved_only.write_text(
                json.dumps(
                    {
                        "schemaVersion": 1,
                        "solverPid": solver_pid,
                        "directory": str(socket_root / reserved_only_name),
                    }
                )
                + "\n",
                encoding="utf-8",
            )
            reserved_only.chmod(0o600)
            unrelated = socket_root / f"logos-pds-{solver_pid}-unrecorded"
            unrelated.mkdir(mode=0o700)
            cleanup = self.runner["cleanup_case_proof_containers"]
            with mock.patch.dict(
                cleanup.__globals__,
                {"SHORT_DIAGNOSTIC_SOCKET_ROOT": socket_root},
            ):
                cleanup(case_dir)
            self.assertFalse(socket_directory.exists())
            self.assertFalse(host_tmp.exists())
            self.assertFalse(marker.exists())
            self.assertTrue(unrelated.is_dir())

    def test_proof_host_cleanup_rejects_anomalous_bound_socket_directory(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            socket_root = root / "tmp"
            socket_root.mkdir()
            case_dir = root / "case"
            host_tmp = case_dir / "proof-stage/proof-agent/host-tmp"
            host_tmp.mkdir(parents=True)
            solver_pid = 434343
            marker = self.write_stale_solver_marker(case_dir, solver_pid)
            directory_name = f"logos-pds-{solver_pid}-bound456"
            socket_directory = socket_root / directory_name
            socket_directory.mkdir(mode=0o700)
            (socket_directory / "unexpected").write_text("keep", encoding="utf-8")
            sidecar = host_tmp / (
                f".diagnostic-socket-{solver_pid}-01-{directory_name}.json"
            )
            sidecar.write_text(
                json.dumps(
                    {
                        "schemaVersion": 1,
                        "solverPid": solver_pid,
                        "directory": str(socket_directory),
                    }
                )
                + "\n",
                encoding="utf-8",
            )
            sidecar.chmod(0o600)
            cleanup = self.runner["cleanup_case_proof_containers"]
            with mock.patch.dict(
                cleanup.__globals__,
                {"SHORT_DIAGNOSTIC_SOCKET_ROOT": socket_root},
            ):
                with self.assertRaises(self.runner_error):
                    cleanup(case_dir)
            self.assertTrue(socket_directory.is_dir())
            self.assertTrue((socket_directory / "unexpected").is_file())

    def test_hard_crash_cleanup_reclaims_only_identity_bound_solver_tree(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            case_dir = root / "case"
            (case_dir / "proof-stage/proof-agent/host-tmp").mkdir(parents=True)
            trigger = root / "trigger"
            spawned = root / "spawned"
            escaped_token = f"logos-escaped-{os.getpid()}-{time.time_ns()}"
            unrelated_token = f"logos-unrelated-{os.getpid()}-{time.time_ns()}"
            worker_source = (
                "import os,pathlib,subprocess,sys,time; "
                "trigger=pathlib.Path(sys.argv[1]); "
                "spawned=pathlib.Path(sys.argv[2]); token=sys.argv[3]; "
                "\nwhile not trigger.exists(): time.sleep(.005)\n"
                "deadline=time.monotonic()+2; first=True\n"
                "while time.monotonic()<deadline:\n"
                " child=subprocess.Popen([sys.executable,'-c',"
                "'import time; time.sleep(60)',token],start_new_session=True)\n"
                " if first: spawned.write_text('started'); first=False\n"
                " time.sleep(.005)\n"
            )
            payload_source = (
                "import subprocess,sys,time; "
                f"subprocess.Popen([sys.executable,'-c',{worker_source!r},"
                f"{str(trigger)!r},{str(spawned)!r},{escaped_token!r}]); "
                "time.sleep(60)"
            )
            supervisor = self.runner["CASE_PROCESS_SUPERVISOR_SOURCE"]
            bootstrap = self.runner["CASE_PROCESS_BOOTSTRAP"]
            solver = subprocess.Popen(
                self.runner["case_process_supervisor_command"](
                    (sys.executable, "-c", payload_source),
                    bootstrap,
                    supervisor,
                ),
                env={"PATH": "/usr/bin:/bin", "LC_ALL": "C"},
                start_new_session=True,
            )
            unrelated = subprocess.Popen(
                [
                    sys.executable,
                    "-c",
                    "import time; time.sleep(60)",
                    unrelated_token,
                ],
                start_new_session=True,
            )
            try:
                identity = self.runner["write_solver_pid_marker"](
                    case_dir, solver, supervisor
                )
                self.assertIsNotNone(identity)
                self.assertTrue(
                    self.runner["solver_process_identity_matches"](identity)
                )
                trigger.write_text("go", encoding="ascii")
                deadline = time.monotonic() + 5
                while not spawned.is_file() and time.monotonic() < deadline:
                    time.sleep(0.01)
                self.assertTrue(spawned.is_file(), "escape worker did not start")
                self.assertTrue(processes_with_argument(escaped_token))

                self.runner["cleanup_case_proof_containers"](
                    case_dir, termination_grace_seconds=0.2
                )
                solver.wait(timeout=5)
                deadline = time.monotonic() + 3
                while processes_with_argument(escaped_token) and time.monotonic() < deadline:
                    time.sleep(0.02)
                self.assertEqual(processes_with_argument(escaped_token), [])
                self.assertIsNone(unrelated.poll())
                self.assertTrue(processes_with_argument(unrelated_token))
                self.assertFalse(
                    (case_dir / self.runner["SOLVER_PID_MARKER"]).exists()
                )
            finally:
                for process in (solver, unrelated):
                    if process.poll() is None:
                        process.kill()
                    try:
                        process.wait(timeout=5)
                    except subprocess.TimeoutExpired:
                        pass
                for process_id in processes_with_argument(escaped_token):
                    try:
                        os.kill(process_id, signal.SIGKILL)
                    except ProcessLookupError:
                        pass

    def test_stale_solver_identity_never_kills_reused_pid(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            case_dir = Path(temporary) / "case"
            (case_dir / "proof-stage/proof-agent/host-tmp").mkdir(parents=True)
            unrelated = subprocess.Popen(
                [sys.executable, "-c", "import time; time.sleep(60)"],
                start_new_session=True,
            )
            try:
                observed = self.runner["observe_solver_process_identity"](
                    unrelated.pid
                )
                self.assertIsNotNone(observed)
                identity = dict(observed[0])
                identity["startTimeTicks"] += 1
                marker = case_dir / self.runner["SOLVER_PID_MARKER"]
                marker.write_text(
                    self.runner["canonical_solver_pid_marker"](identity),
                    encoding="ascii",
                )
                marker.chmod(0o600)

                self.runner["cleanup_case_proof_containers"](
                    case_dir, termination_grace_seconds=0.1
                )
                self.assertIsNone(unrelated.poll())
                self.assertFalse(marker.exists())
            finally:
                if unrelated.poll() is None:
                    try:
                        os.killpg(unrelated.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                unrelated.wait(timeout=5)

    def test_live_termination_serializes_group_signal_with_reaping(self) -> None:
        process = subprocess.Popen(
            [sys.executable, "-c", "import time; time.sleep(60)"],
            start_new_session=True,
        )
        managed = self.runner["ManagedProcess"](process)
        waiter_result: list[int] = []
        waiter_error: list[BaseException] = []

        def wait_for_process() -> None:
            try:
                waiter_result.append(managed.wait(10.0))
            except BaseException as error:
                waiter_error.append(error)

        waiter = threading.Thread(target=wait_for_process)
        original_killpg = os.killpg

        def terminate_and_observe_unreaped_leader(pid: int, sig: int) -> None:
            original_killpg(pid, sig)
            deadline = time.monotonic() + 3
            state = None
            stat_path = Path(f"/proc/{pid}/stat")
            while time.monotonic() < deadline:
                try:
                    raw = stat_path.read_text(encoding="ascii")
                except FileNotFoundError:
                    raw = ""
                if raw:
                    close = raw.rfind(")")
                    fields = raw[close + 1 :].split()
                    state = fields[0] if fields else None
                    if state == "Z":
                        break
                time.sleep(0.005)
            self.assertEqual(state, "Z")
            # The worker's pidfd wait has observed exit by now, but it cannot
            # reap while termination holds the managed-record lock.
            time.sleep(0.05)
            self.assertTrue(stat_path.exists())

        try:
            waiter.start()
            with mock.patch.object(
                self.runner["os"],
                "killpg",
                side_effect=terminate_and_observe_unreaped_leader,
            ):
                self.runner["terminate_process_group"](managed, 0.2)
            waiter.join(timeout=5)
            self.assertFalse(waiter.is_alive())
            self.assertEqual(waiter_error, [])
            self.assertEqual(len(waiter_result), 1)
            self.assertLess(waiter_result[0], 0)
        finally:
            if waiter.is_alive():
                waiter.join(timeout=1)
            if not managed.has_exited():
                self.runner["terminate_process_group"](managed, 0.1)
            else:
                managed.wait(0.0)
            managed.close()

    def test_run_case_guarded_cleans_host_tmp_for_every_terminal_path(self) -> None:
        case = mock.Mock(case_id="suite__case")
        config = mock.Mock(
            run_dir=Path("/tmp/runner-fixture"), termination_grace_seconds=0.25
        )
        registry = mock.Mock()
        stop_event = threading.Event()
        terminal_results = (
            {"status": "completed"},
            {"status": "timed_out"},
            {"status": "cancelled"},
        )
        guarded = self.runner["run_case_guarded"]
        for expected in terminal_results:
            with self.subTest(status=expected["status"]):
                cleanup = mock.Mock()
                with mock.patch.dict(
                    guarded.__globals__,
                    {
                        "run_case": mock.Mock(return_value=expected.copy()),
                        "cleanup_case_proof_containers": cleanup,
                    },
                ):
                    actual = guarded(case, config, registry, stop_event, 1)
                self.assertEqual(actual, expected)
                cleanup.assert_called_once_with(
                    config.run_dir / "cases" / case.case_id,
                    termination_grace_seconds=0.25,
                )

        cleanup = mock.Mock()
        write_result = mock.Mock()
        with mock.patch.dict(
            guarded.__globals__,
            {
                "run_case": mock.Mock(side_effect=RuntimeError("fixture failure")),
                "cleanup_case_proof_containers": cleanup,
                "base_result": mock.Mock(return_value={}),
                "write_case_result": write_result,
            },
        ):
            actual = guarded(case, config, registry, stop_event, 1)
        self.assertEqual(actual["status"], "failed")
        self.assertIn("fixture failure", actual["runnerError"])
        cleanup.assert_called_once_with(
            config.run_dir / "cases" / case.case_id,
            termination_grace_seconds=0.25,
        )
        write_result.assert_called_once_with(config, case, actual)

    def test_recovered_formal_countermodel_deep_validates_deterministic_tail(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            case_dir = Path(temporary).resolve()
            rounds = [{"round": 1, "success": False, "exitCode": 2}]
            proof = {
                "backendStatus": "proof_complete",
                "certification": "FORMAL-COUNTERMODEL",
                "proofWorkspace": {},
                "proofSearchTimedOut": False,
                "deterministicTailRecovery": {
                    "status": "published",
                    "claim": "formal_countermodel",
                },
                "proofAgent": rounds[-1],
                "proofAgentRounds": rounds,
            }
            report = {
                "logDir": str(case_dir),
                "outcome": "not_equivalent",
                "counterexample": {},
                "proof": proof,
            }
            config = mock.Mock()
            deep_validator = mock.Mock(
                side_effect=self.runner_error("deep recovery validation sentinel")
            )
            validate_formal = self.runner[
                "validate_formal_countermodel_certificate"
            ]
            with mock.patch.dict(
                validate_formal.__globals__,
                {"validate_deterministic_tail_recovery": deep_validator},
            ), self.assertRaisesRegex(
                self.runner_error, "deep recovery validation sentinel"
            ):
                self.runner["validate_completed_report"](
                    report,
                    {},
                    case_dir,
                    config=config,
                )
            deep_validator.assert_called_once_with(
                proof,
                rounds,
                case_dir,
                config,
            )

    def test_formal_countermodel_report_requires_bound_trusted_artifacts(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            case_dir = Path(temporary).resolve()
            formal_dir = case_dir / "proof-stage/formal-sql"
            round_dir = (
                case_dir / "proof-stage/proof-agent/rounds/01/checked-workspace"
            )
            formal_dir.mkdir(parents=True)
            round_dir.mkdir(parents=True)
            problem_path = formal_dir / "Problem.v"
            goal_path = formal_dir / "Goal.v"
            context_path = formal_dir / "context-manifest.json"
            closure_path = round_dir / "authority-closure.txt"
            problem_path.write_text(
                "Definition generated_verification_claim : "
                "Logos.FormalSQL.VerificationConditions.verification_claim_kind :=\n"
                "  Logos.FormalSQL.VerificationConditions.VerificationCountermodel.\n"
                "Theorem generated_queries_verified : True. Proof. exact I. Qed.\n",
                encoding="utf-8",
            )
            goal_path.write_text(
                "Theorem generated_verification_certificate : True. "
                "Proof. exact I. Qed.\n",
                encoding="utf-8",
            )
            (round_dir / "Problem.v").write_bytes(problem_path.read_bytes())
            (round_dir / "Goal.v").write_bytes(goal_path.read_bytes())
            context_path.write_text(
                json.dumps(
                    {
                        "goalModule": {
                            "path": "Goal.v",
                            "bytes": goal_path.stat().st_size,
                            "sha256": hashlib.sha256(
                                goal_path.read_bytes()
                            ).hexdigest(),
                        }
                    }
                )
                + "\n",
                encoding="utf-8",
            )
            closure_path.write_text("trusted\n", encoding="utf-8")
            digest = self.runner["sha256_file"]

            def relative(path: Path) -> str:
                return path.relative_to(case_dir).as_posix()

            problem_digest = digest(problem_path)
            context_digest = digest(context_path)
            closure_digest = digest(closure_path)
            counterexample = {
                "kind": "formalSqlCountermodel",
                "problem_path": relative(problem_path),
                "goal_path": relative(goal_path),
                "problem_sha256": problem_digest,
                "context_manifest_sha256": context_digest,
                "authority_closure_sha256": closure_digest,
                "trusted_check_exit_code": 0,
                "theorem": "generated_verification_certificate",
            }
            agent = {
                "success": True,
                "exitCode": 0,
                "candidateClaim": "formal_countermodel",
                "candidateProblemCompilePassed": True,
                "candidateHasFinalTheorem": True,
                "candidateProblemSha256": problem_digest,
                "contextManifestSha256": context_digest,
                "authorityClosurePath": relative(closure_path),
                "authorityClosureSha256": closure_digest,
                "proofCheckExitCode": 0,
                "proofCheckTimedOut": False,
                "audit": {"passed": True, "findings": []},
            }
            report = {
                "logDir": str(case_dir),
                "outcome": "not_equivalent",
                "counterexample": counterexample,
                "proof": {
                    "verificationMode": "outcome_unconditional",
                    "backendStatus": "proof_complete",
                    "certification": "FORMAL-COUNTERMODEL",
                    "proofSearchTimedOut": False,
                    "proofWorkspace": {
                        "problemPath": relative(problem_path),
                        "goalPath": relative(goal_path),
                        "contextManifestPath": relative(context_path),
                    },
                    "proofAgentConfiguration": {
                        "enabled": True,
                        "context": {
                            "manifestPath": relative(context_path),
                            "manifestSha256": context_digest,
                        },
                    },
                    "proofAgent": agent,
                    "proofAgentRounds": [agent],
                },
            }
            result = {
                "proofMetrics": {
                    "proofRoundCount": 1,
                    "finalProofCheckElapsedMs": 7,
                    "proofSource": {
                        "present": True,
                        "sha256": problem_digest,
                    },
                }
            }
            validate = self.runner["validate_completed_report"]
            validate(report, result, case_dir)

            for label, mutate in (
                (
                    "problem digest",
                    lambda value: value["counterexample"].__setitem__(
                        "problem_sha256", "0" * 64
                    ),
                ),
                (
                    "context artifact",
                    lambda value: value["proof"]["proofAgentConfiguration"][
                        "context"
                    ].__setitem__("manifestPath", relative(goal_path)),
                ),
                (
                    "authority closure",
                    lambda value: value["proof"]["proofAgent"].__setitem__(
                        "authorityClosureSha256", "0" * 64
                    ),
                ),
                (
                    "claim",
                    lambda value: value["proof"]["proofAgent"].__setitem__(
                        "candidateClaim", "outcome_unconditional"
                    ),
                ),
            ):
                tampered = json.loads(json.dumps(report))
                mutate(tampered)
                with self.subTest(label=label), self.assertRaises(self.runner_error):
                    validate(tampered, result, case_dir)

    def test_not_equivalent_database_witness_is_strict_and_authority_bound(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            case_dir = Path(temporary).resolve()
            (case_dir / "counterexample-stage").mkdir()
            (case_dir / "input").mkdir()
            (case_dir / "proof-stage").mkdir()
            (case_dir / "validation").mkdir()
            selected = case_dir / "selected/nonwetune-flat/fixture"
            selected.mkdir(parents=True)
            selected_sql = {
                "schema.sql": "CREATE TABLE t(x INT);",
                "sql1.sql": "SELECT x FROM t;",
                "sql2.sql": "SELECT x FROM t;",
            }
            for name, sql in selected_sql.items():
                (selected / name).write_text(sql, encoding="utf-8")
            metadata_path = selected / "metadata.json"
            metadata_path.write_text(
                json.dumps({"flatCaseId": "fixture"}), encoding="utf-8"
            )
            case = mock.Mock(
                case_id="nonwetune-flat__fixture",
                relative_dir="nonwetune-flat/fixture",
                flat_case_id="fixture",
                input_dir=selected,
                schema=selected / "schema.sql",
                source=selected / "sql1.sql",
                target=selected / "sql2.sql",
            )
            input_files = {
                name: {
                    "path": str(path),
                    "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
                }
                for name, path in (
                    ("schema", case.schema),
                    ("source", case.source),
                    ("target", case.target),
                    ("metadata", metadata_path),
                )
            }
            config = mock.Mock(
                verification_mode="outcome-unconditional",
                sql_default_collation="C",
                sql_character_classification="C",
                sql_locale_provider="libc",
                sql_server_encoding="UTF8",
                input_files={case.case_id: input_files},
            )
            result = {
                "proofMetrics": {},
                "effectiveConfiguration": {
                    "verificationMode": "outcome-unconditional"
                },
            }
            sql_environment = {
                "defaultCollation": "C",
                "characterClassification": "C",
                "localeProvider": "libc",
                "serverEncoding": "UTF8",
            }
            integrity_contract = {
                "caseId": "fixture",
                "source": str(metadata_path),
                "tables": [],
            }
            verification_input = {
                "sqlEnvironment": sql_environment,
                "integrityContract": integrity_contract,
                "schema": {"path": str(case.schema), "sql": selected_sql["schema.sql"]},
                "sourceQuery": {"path": str(case.source), "sql": selected_sql["sql1.sql"]},
                "targetQuery": {"path": str(case.target), "sql": selected_sql["sql2.sql"]},
            }
            input_path = case_dir / "input/verification-input.json"
            integrity_path = case_dir / "input/integrity-contract.json"
            lowering_path = case_dir / "proof-stage/formal-sql-lowering.json"
            input_path.write_text(json.dumps(verification_input), encoding="utf-8")
            integrity_path.write_text(json.dumps(integrity_contract), encoding="utf-8")
            (case_dir / "input/schema-ir.json").write_text(
                '{"tables":[]}', encoding="utf-8"
            )
            for name in ("source-ir.json", "target-ir.json"):
                (case_dir / "input" / name).write_text("{}", encoding="utf-8")
            lowering = {
                "schemaVersion": 1,
                "sqlEnvironment": sql_environment,
                "inputBindings": {
                    "schemaVersion": 1,
                    "caseId": "fixture",
                    "schemaSqlSha256": input_files["schema"]["sha256"],
                    "sourceSqlSha256": input_files["source"]["sha256"],
                    "targetSqlSha256": input_files["target"]["sha256"],
                    "verificationInputSha256": hashlib.sha256(input_path.read_bytes()).hexdigest(),
                    "integrityContractSha256": hashlib.sha256(integrity_path.read_bytes()).hexdigest(),
                    "schemaIrSha256": hashlib.sha256((case_dir / "input/schema-ir.json").read_bytes()).hexdigest(),
                    "sourceIrSha256": hashlib.sha256((case_dir / "input/source-ir.json").read_bytes()).hexdigest(),
                    "targetIrSha256": hashlib.sha256((case_dir / "input/target-ir.json").read_bytes()).hexdigest(),
                },
                "source": [],
                "target": [],
            }
            lowering_path.write_text(json.dumps(lowering), encoding="utf-8")
            input_sha256 = hashlib.sha256(
                json.dumps(
                    verification_input,
                    ensure_ascii=False,
                    separators=(",", ":"),
                ).encode()
            ).hexdigest()
            lowering_sha256 = hashlib.sha256(
                json.dumps(lowering, separators=(",", ":")).encode()
            ).hexdigest()
            input_key = self.runner["verification_input_stable_key"](
                verification_input
            )
            source_fact = {
                "statement": 1,
                "permutationClosed": True,
                "successBagFunctional": {
                    "status": "proven",
                    "rule": "source bag is functional",
                },
                "successObservationFunctional": {
                    "status": "proven",
                    "rule": "source sequence is functional",
                },
            }
            target_fact = {
                "statement": 1,
                "permutationClosed": False,
                "successBagFunctional": {
                    "status": "unknown",
                    "residual": "target bag residual",
                },
                "successObservationFunctional": {
                    "status": "unknown",
                    "residual": "target sequence residual",
                },
            }
            authority = {
                "schemaVersion": 1,
                "verificationInputKey": input_key,
                "verificationInputSha256": input_sha256,
                "loweringSha256": lowering_sha256,
                "source": [source_fact],
                "target": [target_fact],
            }
            (case_dir / "counterexample-stage/observation-certificates.json").write_text(
                json.dumps(authority), encoding="utf-8"
            )

            def certificate(comparison: str) -> dict:
                suffix = "Bag" if comparison == "bag" else "Observation"
                source_status = source_fact[f"success{suffix}Functional"]
                target_status = target_fact[f"success{suffix}Functional"]
                return {
                    "schemaVersion": 1,
                    "verificationInputKey": input_key,
                    "verificationInputSha256": input_sha256,
                    "loweringSha256": lowering_sha256,
                    "statement": 1,
                    "comparison": comparison,
                    "sourceDerivation": source_status["rule"],
                    "targetDerivation": target_status["residual"],
                }

            data_difference = {
                "kind": "dataDifference",
                "statement": 1,
                "witness_sql": "INSERT INTO t VALUES (1);",
                "source_result": "[]",
                "target_result": "[{\"x\":1}]",
                "diff_sample": "[{\"side\":\"target_minus_source\"}]",
                "certificate": certificate("bag"),
            }
            row_difference = {
                "kind": "rowSequenceDifference",
                "statement": 1,
                "witness_sql": "INSERT INTO t VALUES (1);",
                "first_differing_row": 1,
                "source_result": "[[1]]",
                "target_result": "[[2]]",
                "certificate": certificate("sequence"),
            }
            mismatch = {
                "kind": "programLength",
                "reason": "query program lengths differ",
                "source_statement_count": 2,
                "target_statement_count": 1,
            }
            schema_difference = {
                "kind": "outputSchemaMismatch",
                "mismatch": mismatch,
            }
            (case_dir / "validation/output-schema-preflight.json").write_text(
                json.dumps(
                    {
                        "schemaName": "fixture_schema",
                        "result": {"kind": "mismatch", "mismatch": mismatch},
                    }
                ),
                encoding="utf-8",
            )
            report = {
                "logDir": str(case_dir),
                "outcome": "not_equivalent",
                "counterexample": data_difference,
                "proof": None,
            }

            def publish_counterexample_stage(counterexample: dict) -> None:
                rounds = []
                if counterexample["kind"] in (
                    "dataDifference",
                    "rowSequenceDifference",
                ):
                    expected_result = dict(counterexample)
                    expected_result.pop("witness_sql")
                    assessment = {
                        "round": 1,
                        "proposalPath": "rounds/01/proposal.json",
                        "candidatePath": "rounds/01/candidate.json",
                    }
                    proposal = {
                        "decision": "counterexample_candidate",
                        "reason": "fixture candidate",
                        "witnessSql": counterexample["witness_sql"],
                    }
                    validation = {
                        "schemaName": "fixture_schema",
                        "result": expected_result,
                    }
                    rounds = [
                        {
                            "round": 1,
                            "assessment": assessment,
                            "proposal": proposal,
                            "validation": validation,
                        }
                    ]
                    round_root = case_dir / "rounds/01"
                    round_root.mkdir(parents=True, exist_ok=True)
                    (round_root / "witness.sql").write_text(
                        counterexample["witness_sql"], encoding="utf-8"
                    )
                    (round_root / "validation.json").write_text(
                        json.dumps(validation), encoding="utf-8"
                    )
                    outcome = (
                        "data_difference"
                        if counterexample["kind"] == "dataDifference"
                        else "row_sequence_difference"
                    )
                    (round_root / "round-report.json").write_text(
                        json.dumps(
                            {
                                "round": 1,
                                "assessment": assessment,
                                "validation": {
                                    "startedMsSinceEpoch": 1,
                                    "elapsedMs": 1,
                                    "result": outcome,
                                },
                                "outcome": "counterexample_validated",
                                "error": None,
                            }
                        ),
                        encoding="utf-8",
                    )
                stage = {
                    "outcome": "not_equivalent",
                    "reason": "fixture terminal counterexample",
                    "rounds": rounds,
                    "counterexample": counterexample,
                    "elapsedMs": 1,
                    "llmUsage": {},
                }
                report["rounds"] = rounds
                (case_dir / "counterexample-stage/report.json").write_text(
                    json.dumps(stage), encoding="utf-8"
                )

            validate = self.runner["validate_completed_report"]
            for counterexample in (
                data_difference,
                row_difference,
                schema_difference,
            ):
                with self.subTest(kind=counterexample["kind"]):
                    report["counterexample"] = counterexample
                    publish_counterexample_stage(counterexample)
                    if counterexample["kind"] == "outputSchemaMismatch":
                        schema_ir_bytes = (case_dir / "input/schema-ir.json").read_bytes()
                        lowering_bytes = lowering_path.read_bytes()
                        (case_dir / "input/schema-ir.json").unlink()
                        lowering_path.unlink()
                        try:
                            validate(report, result, case_dir, case, config)
                        finally:
                            (case_dir / "input/schema-ir.json").write_bytes(
                                schema_ir_bytes
                            )
                            lowering_path.write_bytes(lowering_bytes)
                    else:
                        validate(report, result, case_dir, case, config)

            report["counterexample"] = data_difference
            publish_counterexample_stage(data_difference)
            witness_path = case_dir / "rounds/01/witness.sql"
            witness_path.write_text("INSERT INTO t VALUES (999);", encoding="utf-8")
            with self.assertRaisesRegex(
                self.runner_error, "validation artifacts drifted"
            ):
                validate(report, result, case_dir, case, config)
            publish_counterexample_stage(data_difference)
            validation_path = case_dir / "rounds/01/validation.json"
            forged_validation = json.loads(validation_path.read_text())
            forged_validation["result"]["source_result"] = "forged"
            validation_path.write_text(json.dumps(forged_validation), encoding="utf-8")
            with self.assertRaisesRegex(
                self.runner_error, "validation artifacts drifted"
            ):
                validate(report, result, case_dir, case, config)
            publish_counterexample_stage(data_difference)

            handoff = {
                "decision": "counterexample_candidate",
                "reason": "candidate outcome difference",
                "guidance": "validate the concrete PostgreSQL witness",
            }
            handoff_round = {
                "success": False,
                "exitCode": 2,
                "candidateClaim": None,
                "proofCheckExitCode": None,
                "counterexampleHandoff": handoff,
            }
            handoff_proof = {
                "verificationMode": "outcome_unconditional",
                "backendStatus": "proof_agent_run_completed",
                "certification": None,
                "proofSearchTimedOut": False,
                "proofWorkspace": {},
                "proofAgentConfiguration": {"enabled": True},
                "proofAgent": handoff_round,
                "proofAgentRounds": [handoff_round],
            }
            handoff_result = {
                **result,
                "proofMetrics": {
                    "proofRoundCount": 1,
                    "preflightInvocationCount": 1,
                    "initialProblemCompileInvocationCount": 1,
                    "proofSource": {"present": True},
                },
            }
            report["counterexample"] = data_difference
            report["proof"] = handoff_proof
            publish_counterexample_stage(data_difference)
            validate(report, handoff_result, case_dir, case, config)
            forged_handoff_report = json.loads(json.dumps(report))
            forged_handoff_report["proof"]["proofAgent"][
                "counterexampleHandoff"
            ]["decision"] = "prove_equivalence"
            forged_handoff_report["proof"]["proofAgentRounds"][-1] = (
                forged_handoff_report["proof"]["proofAgent"]
            )
            forged_handoff_report["proof"]["backendStatus"] = "proof_agent_failed"
            with self.assertRaisesRegex(
                self.runner_error, "strict terminal handoff provenance"
            ):
                validate(
                    forged_handoff_report,
                    handoff_result,
                    case_dir,
                    case,
                    config,
                )

            report["proof"] = None
            malformed = [
                {"kind": "dataDifference"},
                {**data_difference, "statement": True},
                {**data_difference, "extra": "forged"},
                {
                    **data_difference,
                    "certificate": {
                        **data_difference["certificate"],
                        "loweringSha256": "0" * 64,
                    },
                },
            ]
            for index, counterexample in enumerate(malformed):
                report["counterexample"] = counterexample
                (case_dir / "counterexample-stage/report.json").write_text(
                    json.dumps(
                        {
                            "outcome": "not_equivalent",
                            "counterexample": counterexample,
                        }
                    ),
                    encoding="utf-8",
                )
                with self.subTest(malformed=index), self.assertRaises(
                    self.runner_error
                ):
                    validate(report, result, case_dir, case, config)

            report["counterexample"] = data_difference
            report["proof"] = {"certification": "FORMAL-COUNTERMODEL"}
            with self.assertRaises(self.runner_error):
                validate(report, result, case_dir, case, config)

            report["proof"] = None
            report["counterexample"] = data_difference
            publish_counterexample_stage(data_difference)
            config.verification_mode = "conditional"
            result["effectiveConfiguration"]["verificationMode"] = "conditional"
            report["counterexample"] = schema_difference
            publish_counterexample_stage(schema_difference)
            validate(report, result, case_dir, case, config)
            report["counterexample"] = data_difference
            publish_counterexample_stage(data_difference)
            with self.assertRaisesRegex(
                self.runner_error, "not terminal in conditional mode"
            ):
                validate(report, result, case_dir, case, config)
            config.verification_mode = "outcome-unconditional"
            result["effectiveConfiguration"]["verificationMode"] = (
                "outcome-unconditional"
            )

            copied_input = json.loads(json.dumps(verification_input))
            copied_input["sourceQuery"]["sql"] = "SELECT 999;"
            input_path.write_text(json.dumps(copied_input), encoding="utf-8")
            with self.assertRaisesRegex(
                self.runner_error, "identifies another case"
            ):
                validate(report, result, case_dir, case, config)

    def test_input_authority_uses_flat_case_id_and_declared_sidecar(self) -> None:
        validate = self.runner["validate_case_input_and_lowering_authority"]
        shapes = (
            (
                "nonwetune-flat/verieql-calcite__calcite-148",
                "verieql-calcite__calcite-148",
                False,
            ),
            ("wetune-issues/31", "wetune-issues__31", True),
        )
        for relative_dir, flat_case_id, uses_sidecar in shapes:
            with self.subTest(relative_dir=relative_dir), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary)
                selected = root / "selected" / relative_dir
                selected.mkdir(parents=True)
                sql_values = {
                    "schema.sql": "CREATE TABLE t(x INT);\n",
                    "sql1.sql": "SELECT x FROM t;\n",
                    "sql2.sql": "SELECT x FROM t;\n",
                }
                for name, sql in sql_values.items():
                    (selected / name).write_text(sql, encoding="utf-8")
                metadata_path = selected / "metadata.json"
                sidecar_path = root / "semantic-sidecar.json"
                metadata = {"flatCaseId": flat_case_id}
                integrity_source = str(metadata_path)
                integrity_tables = []
                if uses_sidecar:
                    sidecar = {
                        "checks": [],
                        "foreignKeys": [],
                        "primaryKeys": [{"table": "T", "columns": ["id"]}],
                        "semanticSchema": {
                            "typeSemantics": self.runner[
                                "WETUNE_RAW_TYPE_SEMANTICS"
                            ],
                            "tables": [
                                {
                                    "name": "T",
                                    "columns": [
                                        {
                                            "autoIncrement": False,
                                            "default": None,
                                            "generated": False,
                                            "inlinePrimary": False,
                                            "inlineUnique": False,
                                            "name": "id",
                                            "normalizedFrontendType": "INTEGER",
                                            "notNull": True,
                                            "nullable": False,
                                            "sourceDeclaration": "id integer NOT NULL",
                                            "sourceType": "integer",
                                        }
                                    ],
                                }
                            ]
                        },
                        "uniqueIndexes": [],
                        "uniqueKeys": [],
                        "unsupportedSemanticConstraints": [],
                    }
                    sidecar_path.write_text(json.dumps(sidecar), encoding="utf-8")
                    integrity_source = str(sidecar_path)
                    integrity_tables = [
                        {
                            "name": "t",
                            "constraints": {
                                "notNull": ["id"],
                                "primaryKey": ["id"],
                            },
                        }
                    ]
                    metadata.update(
                        {
                            "integrityContract": {
                                "sourceKind": "wetune_base_schema_sidecar",
                                "authoritativeForLogos": True,
                                "semanticSidecar": str(sidecar_path),
                                "sidecarAuthority": "integrity_declarations_only",
                            },
                            "semanticConstraints": {
                                "source": str(sidecar_path),
                                "checks": 0,
                                "columns": 1,
                                "foreignKeys": 0,
                                "primaryKeys": 1,
                                "uniqueIndexes": 0,
                                "uniqueKeys": 0,
                            },
                            "renamedIdentifiers": {},
                        }
                    )
                metadata_path.write_text(json.dumps(metadata), encoding="utf-8")
                case = mock.Mock(
                    case_id=relative_dir.replace("/", "__"),
                    relative_dir=relative_dir,
                    flat_case_id=flat_case_id,
                    input_dir=selected,
                    schema=selected / "schema.sql",
                    source=selected / "sql1.sql",
                    target=selected / "sql2.sql",
                )
                input_files = {
                    key: {
                        "path": str(path),
                        "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
                    }
                    for key, path in (
                        ("schema", case.schema),
                        ("source", case.source),
                        ("target", case.target),
                        ("metadata", metadata_path),
                    )
                }
                if uses_sidecar:
                    input_files["semanticSidecar"] = {
                        "path": str(sidecar_path),
                        "sha256": hashlib.sha256(sidecar_path.read_bytes()).hexdigest(),
                    }
                config = mock.Mock(
                    sql_default_collation="C",
                    sql_character_classification="C",
                    sql_locale_provider="libc",
                    sql_server_encoding="UTF8",
                    input_files={case.case_id: input_files},
                )
                case_dir = root / "case-output"
                artifact_root = case_dir / "input"
                artifact_root.mkdir(parents=True)
                environment = {
                    "defaultCollation": "C",
                    "characterClassification": "C",
                    "localeProvider": "libc",
                    "serverEncoding": "UTF8",
                }
                integrity = {
                    "caseId": flat_case_id,
                    "source": integrity_source,
                    "tables": integrity_tables,
                }
                schema_ir = {
                    "tables": [
                        {
                            "name": "t",
                            "columns": [{"name": "id", "ty": "integer"}],
                            **(
                                {"constraints": integrity_tables[0]["constraints"]}
                                if integrity_tables
                                else {}
                            ),
                        }
                    ]
                }
                verification = {
                    "sqlEnvironment": environment,
                    "integrityContract": integrity,
                    "schema": {"path": str(case.schema), "sql": sql_values["schema.sql"]},
                    "sourceQuery": {"path": str(case.source), "sql": sql_values["sql1.sql"]},
                    "targetQuery": {"path": str(case.target), "sql": sql_values["sql2.sql"]},
                }
                artifacts = {
                    "verification-input.json": verification,
                    "integrity-contract.json": integrity,
                    "schema-ir.json": schema_ir,
                    "source-ir.json": {},
                    "target-ir.json": {},
                }
                for name, value in artifacts.items():
                    (artifact_root / name).write_text(
                        json.dumps(value), encoding="utf-8"
                    )
                bindings = {
                    "schemaVersion": 1,
                    "caseId": flat_case_id,
                    "schemaSqlSha256": input_files["schema"]["sha256"],
                    "sourceSqlSha256": input_files["source"]["sha256"],
                    "targetSqlSha256": input_files["target"]["sha256"],
                    "verificationInputSha256": hashlib.sha256((artifact_root / "verification-input.json").read_bytes()).hexdigest(),
                    "integrityContractSha256": hashlib.sha256((artifact_root / "integrity-contract.json").read_bytes()).hexdigest(),
                    "schemaIrSha256": hashlib.sha256((artifact_root / "schema-ir.json").read_bytes()).hexdigest(),
                    "sourceIrSha256": hashlib.sha256((artifact_root / "source-ir.json").read_bytes()).hexdigest(),
                    "targetIrSha256": hashlib.sha256((artifact_root / "target-ir.json").read_bytes()).hexdigest(),
                }
                proof_stage = case_dir / "proof-stage"
                proof_stage.mkdir()
                (proof_stage / "formal-sql-lowering.json").write_text(
                    json.dumps(
                        {
                            "sqlEnvironment": environment,
                            "inputBindings": bindings,
                        }
                    ),
                    encoding="utf-8",
                )
                validate(case_dir, case, config, require_lowering=True)

                schema_ir_artifact = artifact_root / "schema-ir.json"
                schema_ir_bytes = schema_ir_artifact.read_bytes()
                schema_ir_artifact.write_text(
                    json.dumps(schema_ir, indent=2) + "\n", encoding="utf-8"
                )
                with self.assertRaisesRegex(
                    self.runner_error,
                    "FormalSQL lowering input binding digest drifted",
                ):
                    validate(case_dir, case, config, require_lowering=True)
                schema_ir_artifact.write_bytes(schema_ir_bytes)

                if uses_sidecar:
                    metadata["integrityContract"]["authoritativeForLogos"] = False
                    metadata_path.write_text(json.dumps(metadata), encoding="utf-8")
                    input_files["metadata"]["sha256"] = hashlib.sha256(
                        metadata_path.read_bytes()
                    ).hexdigest()
                    with self.assertRaisesRegex(
                        self.runner_error, "sidecar authority"
                    ):
                        validate(case_dir, case, config, require_lowering=True)
                else:
                    metadata["constraintScope"] = "pair"
                    metadata["constraints"] = [
                        {"primary": [{"value": "T__id"}]}
                    ]
                    metadata_path.write_text(json.dumps(metadata), encoding="utf-8")
                    input_files["metadata"]["sha256"] = hashlib.sha256(
                        metadata_path.read_bytes()
                    ).hexdigest()
                    with self.assertRaisesRegex(
                        self.runner_error, "selected pair constraint"
                    ):
                        validate(case_dir, case, config, require_lowering=True)

    def test_pair_integrity_binds_full_schema_and_metadata_subset(self) -> None:
        validate = self.runner["validate_effective_integrity_contract"]
        canonicalize = self.runner["pair_metadata_integrity_tables"]
        child_constraints = {
            "notNull": ["id", "parent_id"],
            "primaryKey": ["id"],
            "unique": [{"columns": ["payload"]}],
            "foreignKeys": [
                {
                    "columns": ["parent_id"],
                    "referencedTable": "parent",
                    "referencedColumns": ["id"],
                    "matchType": "simple",
                    "referentialActions": "ON DELETE CASCADE",
                }
            ],
        }
        parent_constraints = {
            "notNull": ["id"],
            "primaryKey": ["id"],
        }
        ddl_only_constraints = {"notNull": ["x"]}
        schema_ir = {
            "tables": [
                {
                    "name": "child",
                    "columns": [
                        {"name": "id", "ty": "integer"},
                        {"name": "parent_id", "ty": "integer"},
                        {"name": "payload", "ty": "integer"},
                    ],
                    "constraints": child_constraints,
                },
                {
                    "name": "parent",
                    "columns": [{"name": "id", "ty": "integer"}],
                    "constraints": parent_constraints,
                },
                {
                    "name": "ddl_only",
                    "columns": [{"name": "x", "ty": "integer"}],
                    "constraints": ddl_only_constraints,
                },
            ]
        }
        metadata = {
            "constraintScope": "pair",
            "constraints": [
                {"primary": [{"value": "PARENT__ID"}]},
                {"not_null": {"value": "CHILD__PARENT_ID"}},
                {"not_null": {"value": "CHILD__PARENT_ID"}},
                {"primary": [{"value": "CHILD__ID"}]},
                {
                    "foreign": [
                        {"value": "CHILD__PARENT_ID"},
                        {"value": "PARENT__ID"},
                    ]
                },
                {
                    "foreign": [
                        {"value": "CHILD__PARENT_ID"},
                        {"value": "PARENT__ID"},
                    ]
                },
            ],
        }
        integrity = {
            "tables": [
                {"name": "child", "constraints": child_constraints},
                {"name": "parent", "constraints": parent_constraints},
                {"name": "ddl_only", "constraints": ddl_only_constraints},
            ]
        }
        self.assertEqual(
            canonicalize(metadata, schema_ir),
            [
                {
                    "name": "child",
                    "constraints": {
                        "notNull": ["id", "parent_id"],
                        "primaryKey": ["id"],
                        "foreignKeys": [
                            {
                                "columns": ["parent_id"],
                                "referencedTable": "parent",
                                "referencedColumns": ["id"],
                                "matchType": "simple",
                            }
                        ],
                    },
                },
                {"name": "parent", "constraints": parent_constraints},
            ],
        )
        validate(metadata, integrity, None, schema_ir)

        # DDL declarations are part of the effective contract even when pair
        # metadata is empty.
        validate(
            {"constraintScope": "none", "constraints": []},
            integrity,
            None,
            schema_ir,
        )

        string_not_null_schema = {
            "tables": [
                {
                    "name": "s",
                    "columns": [{"name": "name", "ty": "text"}],
                    "constraints": {"notNull": ["name"]},
                }
            ]
        }
        string_not_null_integrity = {
            "tables": [
                {"name": "s", "constraints": {"notNull": ["name"]}}
            ]
        }
        validate(
            {"constraintScope": "none", "constraints": []},
            string_not_null_integrity,
            None,
            string_not_null_schema,
        )
        string_primary_schema = json.loads(json.dumps(string_not_null_schema))
        string_primary_schema["tables"][0]["constraints"]["primaryKey"] = [
            "name"
        ]
        string_primary_integrity = {
            "tables": [
                {
                    "name": "s",
                    "constraints": {
                        "notNull": ["name"],
                        "primaryKey": ["name"],
                    },
                }
            ],
            "requiresPostgresUtf8CTextSemantics": True,
        }
        validate(
            {"constraintScope": "none", "constraints": []},
            string_primary_integrity,
            None,
            string_primary_schema,
        )
        forged_string_flag = json.loads(json.dumps(string_primary_integrity))
        forged_string_flag.pop("requiresPostgresUtf8CTextSemantics")
        with self.assertRaisesRegex(self.runner_error, "text-semantics authority"):
            validate(
                {"constraintScope": "none", "constraints": []},
                forged_string_flag,
                None,
                string_primary_schema,
            )

        reordered = json.loads(json.dumps(integrity))
        reordered["tables"].reverse()
        with self.assertRaisesRegex(self.runner_error, "accepted schema IR"):
            validate(metadata, reordered, None, schema_ir)

        # Co-removing a metadata declaration from both generated artifacts is
        # rejected by the independent selected-metadata subset check.
        co_mutated_schema = json.loads(json.dumps(schema_ir))
        co_mutated_integrity = json.loads(json.dumps(integrity))
        co_mutated_schema["tables"][0]["constraints"]["notNull"] = ["id"]
        co_mutated_integrity["tables"][0]["constraints"]["notNull"] = ["id"]
        with self.assertRaisesRegex(self.runner_error, "pair NOT NULL"):
            validate(metadata, co_mutated_integrity, None, co_mutated_schema)

        # Match Rust: exact spelling wins; otherwise only one ASCII-folded
        # candidate is accepted. Unicode case folding is never substituted.
        case_schema = {
            "tables": [
                {"name": "Foo", "columns": [{"name": "ID", "ty": "integer"}]},
                {"name": "foo", "columns": [{"name": "id", "ty": "integer"}]},
                {"name": "ß", "columns": [{"name": "x", "ty": "integer"}]},
            ]
        }
        self.assertEqual(
            canonicalize(
                {
                    "constraintScope": "pair",
                    "constraints": [{"primary": [{"value": "Foo__ID"}]}],
                },
                case_schema,
            )[0]["name"],
            "Foo",
        )
        for endpoint, message in (
            ("FOO__ID", "ambiguously case-folds"),
            ("missing__id", "unknown table"),
            ("SS__x", "unknown table"),
        ):
            with self.subTest(endpoint=endpoint), self.assertRaisesRegex(
                self.runner_error, message
            ):
                canonicalize(
                    {
                        "constraintScope": "pair",
                        "constraints": [{"primary": [{"value": endpoint}]}],
                    },
                    case_schema,
                )

        conflicting = json.loads(json.dumps(metadata))
        conflicting["constraints"].append(
            {"primary": [{"value": "CHILD__PARENT_ID"}]}
        )
        with self.assertRaisesRegex(self.runner_error, "conflicting primary"):
            canonicalize(conflicting, schema_ir)

    def test_wetune_integrity_exactly_binds_all_constraint_fields(self) -> None:
        def column(name: str, ty: str, *, not_null: bool) -> dict:
            return {
                "autoIncrement": False,
                "default": None,
                "generated": False,
                "inlinePrimary": False,
                "inlineUnique": False,
                "name": name,
                "normalizedFrontendType": ty,
                "notNull": not_null,
                "nullable": not not_null,
                "sourceDeclaration": f"{name} {ty.lower()}",
                "sourceType": ty.lower(),
            }

        sidecar = {
            "checks": [
                {
                    "expression": "(flag = 1)",
                    "source": "create_table",
                    "table": "T",
                }
            ],
            "foreignKeys": [
                {
                    "actions": "ON DELETE CASCADE",
                    "columns": ["parent_id"],
                    "refColumns": ["id"],
                    "refTable": "P",
                    "source": "alter_table",
                    "table": "T",
                }
            ],
            "primaryKeys": [
                {"columns": ["id"], "table": "T"},
                {"columns": ["id"], "table": "P"},
            ],
            "semanticSchema": {
                "typeSemantics": self.runner["WETUNE_RAW_TYPE_SEMANTICS"],
                "tables": [
                    {
                        "name": "T",
                        "columns": [
                            column("id", "INTEGER", not_null=True),
                            column("parent_id", "INTEGER", not_null=False),
                            column("name", "VARCHAR(255)", not_null=False),
                            column("flag", "INTEGER", not_null=False),
                        ],
                    },
                    {
                        "name": "P",
                        "columns": [column("id", "INTEGER", not_null=True)],
                    },
                ],
            },
            "uniqueIndexes": [
                {
                    "source": "create_unique_index",
                    "table": "T",
                    "terms": ["lower((name)::text) varchar_pattern_ops"],
                    "where": "(name IS NOT NULL)",
                }
            ],
            "uniqueKeys": [
                {
                    "columns": ["name"],
                    "nullableColumns": ["name"],
                    "semantics": "sql_unique_allows_multiple_nulls",
                    "table": "T",
                }
            ],
            "unsupportedSemanticConstraints": [],
        }
        metadata = {
            "renamedIdentifiers": {},
            "semanticConstraints": {
                "checks": 1,
                "columns": 5,
                "foreignKeys": 1,
                "primaryKeys": 2,
                "uniqueIndexes": 1,
                "uniqueKeys": 1,
            },
        }
        integrity = {
            "tables": [
                {
                    "name": "p",
                    "constraints": {
                        "notNull": ["id"],
                        "primaryKey": ["id"],
                    },
                },
                {
                    "name": "t",
                    "constraints": {
                        "notNull": ["id"],
                        "primaryKey": ["id"],
                        "unique": [{"columns": ["name"]}],
                        "foreignKeys": [
                            {
                                "columns": ["parent_id"],
                                "referencedTable": "p",
                                "referencedColumns": ["id"],
                                "matchType": "simple",
                                "referentialActions": "ON DELETE CASCADE",
                            }
                        ],
                        "checks": [
                            {
                                "expression": {
                                    "kind": "comparison",
                                    "comparison": "equal",
                                    "left": {"kind": "column", "name": "flag"},
                                    "right": {
                                        "kind": "literal",
                                        "raw": "1",
                                        "ty": "integer",
                                    },
                                },
                                "sourceSql": '( "flag" = 1 )',
                            }
                        ],
                        "uniqueIndexes": [
                            {
                                "terms": [
                                    {
                                        "expression": {
                                            "kind": "lower",
                                            "expression": {
                                                "kind": "cast",
                                                "expression": {
                                                    "kind": "column",
                                                    "name": "name",
                                                },
                                                "ty": "text",
                                            },
                                        },
                                        "sourceSql": (
                                            'LOWER ( ( "name" ) :: TEXT ) '
                                            "VARCHAR_PATTERN_OPS"
                                        ),
                                        "direction": "asc",
                                        "operatorClass": "varchar_pattern_ops",
                                    }
                                ],
                                "predicate": {
                                    "kind": "is_not_null",
                                    "expression": {
                                        "kind": "column",
                                        "name": "name",
                                    },
                                },
                                "predicateSql": '( "name" IS NOT NULL )',
                            }
                        ],
                    },
                },
            ],
            "requiresPostgresUtf8CTextSemantics": True,
        }
        schema_ir = {
            "tables": [
                {
                    "name": "p",
                    "columns": [{"name": "id", "ty": "integer"}],
                    "constraints": integrity["tables"][0]["constraints"],
                },
                {
                    "name": "t",
                    "columns": [
                        {"name": "id", "ty": "integer"},
                        {"name": "parent_id", "ty": "integer"},
                        {"name": "name", "ty": "text"},
                        {"name": "flag", "ty": "integer"},
                    ],
                    "constraints": integrity["tables"][1]["constraints"],
                },
            ]
        }
        validate = self.runner["validate_effective_integrity_contract"]
        validate(metadata, integrity, sidecar, schema_ir)
        reversed_tables = json.loads(json.dumps(integrity))
        reversed_tables["tables"].reverse()
        with self.assertRaisesRegex(self.runner_error, "accepted schema IR"):
            validate(metadata, reversed_tables, sidecar, schema_ir)

        mutations = (
            lambda value: value["tables"][1]["constraints"]["foreignKeys"][0].__setitem__(
                "referencedTable", "q"
            ),
            lambda value: value["tables"][1]["constraints"]["unique"][0].__setitem__(
                "columns", ["id"]
            ),
            lambda value: value["tables"][1]["constraints"]["checks"][0][
                "expression"
            ]["right"].__setitem__("raw", "2"),
            lambda value: value["tables"][1]["constraints"]["uniqueIndexes"][0][
                "predicate"
            ].__setitem__("kind", "is_null"),
        )
        for index, mutate in enumerate(mutations):
            forged = json.loads(json.dumps(integrity))
            mutate(forged)
            with self.subTest(field_mutation=index), self.assertRaisesRegex(
                self.runner_error, "accepted schema IR|exact renamed sidecar"
            ):
                validate(metadata, forged, sidecar, schema_ir)

        duplicate = json.loads(json.dumps(integrity))
        duplicate["tables"].append(duplicate["tables"][0])
        with self.assertRaisesRegex(
            self.runner_error, "accepted schema IR|rows are malformed"
        ):
            validate(metadata, duplicate, sidecar, schema_ir)
        malformed = json.loads(json.dumps(integrity))
        malformed["tables"][0] = {"name": "p"}
        with self.assertRaisesRegex(
            self.runner_error, "accepted schema IR|rows are malformed"
        ):
            validate(metadata, malformed, sidecar, schema_ir)

        substituted_sidecar = json.loads(json.dumps(sidecar))
        substituted_sidecar["foreignKeys"][0]["refTable"] = "T"
        with self.assertRaisesRegex(self.runner_error, "exact renamed sidecar"):
            validate(metadata, integrity, substituted_sidecar, schema_ir)

    def test_trusted_checker_host_tool_registry_matches_manifest_exactly(self) -> None:
        expected = [
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
            "mv",
            "readlink",
            "stat",
            "id",
            "flock",
        ]
        self.assertEqual(list(self.runner["TRUSTED_HOST_TOOL_NAMES"]), expected)
        checker = (
            RUNNER.parents[2] / "crates/logos-solver/scripts/run-trusted-rocq-check.sh"
        ).read_text(encoding="utf-8")
        marker = "for host_tool in \\\n"
        start = checker.index(marker) + len(marker)
        end = checker.index("; do", start)
        script_names = checker[start:end].replace("\\\n", " ").split()
        self.assertEqual(script_names, expected)

    def test_rocq_runtime_configuration_uses_canonical_manifest_path_order(self) -> None:
        collect = self.runner["rocq_runtime_configuration_records"]
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            for relative in (
                "findlib.conf",
                "findlib/META",
                "rocq-runtime/META",
            ):
                path = root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(f"{relative}\n", encoding="utf-8")
            records = collect(root)
        paths = [record["path"] for record in records]
        self.assertEqual(paths, sorted(paths))
        self.assertEqual(
            paths,
            ["findlib.conf", "findlib/META", "rocq-runtime/META"],
        )

    def test_ldd_loader_mutation_and_absent_to_present_change_closure(self) -> None:
        closure = self.runner["ldd_runtime_loader_closure"]
        canonical = self.runner["canonical_json_bytes"]
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            present = root / "ld-present.so"
            absent = root / "ld-absent.so"
            script = root / "ldd"
            present.write_bytes(b"\x7fELFsynthetic-loader-v1")
            present.chmod(0o755)
            script.write_text(f'RTLDLIST="{present} {absent}"\n', encoding="utf-8")

            first = closure(script)
            first_digest = hashlib.sha256(canonical(first)).hexdigest()
            self.assertEqual(
                [row["state"] for row in first["candidates"]],
                ["present", "absent"],
            )

            present.write_bytes(b"\x7fELFsynthetic-loader-v2")
            second = closure(script)
            second_digest = hashlib.sha256(canonical(second)).hexdigest()
            self.assertNotEqual(first_digest, second_digest)
            self.assertNotEqual(
                first["candidates"][0]["sha256"],
                second["candidates"][0]["sha256"],
            )

            absent.write_bytes(b"\x7fELFnewly-present-loader")
            absent.chmod(0o755)
            third = closure(script)
            third_digest = hashlib.sha256(canonical(third)).hexdigest()
            self.assertNotEqual(second_digest, third_digest)
            self.assertEqual(third["presentCandidateCount"], 2)
            self.assertEqual(third["candidates"][1]["state"], "present")

    def test_trusted_inspection_environment_is_clear_then_allowlist(self) -> None:
        inspect = self.runner["trusted_command_output"]
        hostile = {
            "BASH_ENV": "/tmp/hostile-bash-env",
            "LD_PRELOAD": "/tmp/hostile-preload.so",
            "LD_LIBRARY_PATH": "/tmp/hostile-libraries",
            "OCAMLPATH": "/tmp/hostile-ocaml",
            "CAML_LD_LIBRARY_PATH": "/tmp/hostile-stublibs",
            "CDPATH": "/tmp/hostile-cdpath",
            "TMPDIR": "/tmp/hostile-tmp",
            "BASH_FUNC_hostile%%": "() { :; }",
        }
        previous = {name: os.environ.get(name) for name in hostile}
        try:
            os.environ.update(hostile)
            output = inspect(["/usr/bin/env"], "sanitized environment regression")
        finally:
            for name, value in previous.items():
                if value is None:
                    os.environ.pop(name, None)
                else:
                    os.environ[name] = value
        self.assertEqual(
            set(output.splitlines()),
            {"LANG=C", "LC_ALL=C", "PATH=/usr/bin:/bin"},
        )

    def test_real_ldd_loader_closure_binds_32_bit_and_x32_absence(self) -> None:
        closure = self.runner["ldd_runtime_loader_closure"](Path("/usr/bin/ldd"))
        self.assertEqual(
            [row["selectedPath"] for row in closure["candidates"]],
            [
                "/lib/ld-linux.so.2",
                "/lib64/ld-linux-x86-64.so.2",
                "/libx32/ld-linux-x32.so.2",
            ],
        )
        by_path = {row["selectedPath"]: row for row in closure["candidates"]}
        loader32 = by_path["/lib/ld-linux.so.2"]
        self.assertEqual(loader32["state"], "present")
        self.assertTrue(loader32["selectedPathIsSymlink"])
        self.assertEqual(loader32["resolvedPath"], "/usr/lib32/ld-linux.so.2")
        self.assertEqual(
            loader32["sha256"],
            "8bfac642322e3e03bbf5cb7f8ffed50ee8a8119f0ce7d9da9dd54cb961436abf",
        )
        self.assertTrue(loader32["elfCheck"]["passed"])
        self.assertEqual(by_path["/libx32/ld-linux-x32.so.2"]["state"], "absent")

    def test_frontend_environment_is_constructed_from_an_exact_minimum(self) -> None:
        build = self.runner["canonical_frontend_environment"]
        hostile = {
            "BASH_ENV": "/tmp/hostile-bash-env",
            "BASH_FUNC_readlink%%": "() { :; }",
            "LD_LIBRARY_PATH": "/tmp/hostile-libraries",
            "JAVA_TOOL_OPTIONS": "-Dhostile=true",
            "HTTP_PROXY": "http://hostile.invalid:8080",
            "OPENAI_API_KEY": "hostile",
        }
        previous = {name: os.environ.get(name) for name in hostile}
        try:
            os.environ.update(hostile)
            environment = build(include_runtime_classpath=True)
        finally:
            for name, value in previous.items():
                if value is None:
                    os.environ.pop(name, None)
                else:
                    os.environ[name] = value
        self.assertEqual(
            set(environment),
            {
                "PATH",
                "HOME",
                "TMPDIR",
                "LC_ALL",
                "LANG",
                "TZ",
                "JAVA_HOME",
                "MAVEN_VERSION",
                "LOGOS_CALCITE_RUNTIME_CLASSPATH_FILE",
            },
        )
        self.assertEqual(environment["PATH"], "/usr/bin:/bin")
        self.assertEqual(environment["HOME"], "/nonexistent")
        self.assertEqual(environment["TMPDIR"], "/tmp")
        self.assertEqual(environment["TZ"], "UTC")

    def test_system_identity_configuration_is_required_and_digest_bound(self) -> None:
        build = self.runner["system_identity_configuration_record"]
        globals_ = build.__globals__
        original = globals_["TRUSTED_SYSTEM_IDENTITY_CONFIGURATION_PATHS"]
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            first = root / "nsswitch.conf"
            second = root / "passwd"
            first.write_text("passwd: files\n", encoding="utf-8")
            second.write_text("user:x:1:1::/:/bin/false\n", encoding="utf-8")
            globals_["TRUSTED_SYSTEM_IDENTITY_CONFIGURATION_PATHS"] = (
                first,
                second,
            )
            try:
                initial = build()
                self.assertEqual(initial["presentPathCount"], 2)
                initial_digest = initial["paths"][1]["sha256"]
                second.write_text("user:x:2:2::/:/bin/false\n", encoding="utf-8")
                self.assertNotEqual(build()["paths"][1]["sha256"], initial_digest)
                second.unlink()
                with self.assertRaisesRegex(self.runner_error, "is missing"):
                    build()
                second.symlink_to(first)
                with self.assertRaisesRegex(self.runner_error, "non-symlink"):
                    build()
            finally:
                globals_["TRUSTED_SYSTEM_IDENTITY_CONFIGURATION_PATHS"] = original

    def test_real_codex_path_binds_lexical_wrapper_env_and_node(self) -> None:
        record = self.runner["codex_cli_record"]()
        self.assertEqual(record["lexicalWrapper"]["path"], record["invocationPath"])
        if "node" not in record:
            self.skipTest("configured Codex CLI is not the frozen Node launcher")
        self.assertEqual(
            record["interpreterChain"]["envExecutable"]["selectedPath"],
            "/usr/bin/env",
        )
        self.assertEqual(
            record["solverPath"]["directories"][0]["path"],
            str(Path(record["invocationPath"]).parent),
        )
        self.assertEqual(
            record["solverPath"]["directories"][1]["path"],
            str(Path(record["node"]["invocationPath"]).parent),
        )

    def test_counterexample_resume_command_is_session_bound(self) -> None:
        validate = self.runner["validate_counterexample_provider_commands"]
        session_id = "019fa8c6-b1d2-7841-a064-5202662bf9e4"
        report = {
            "rounds": [
                {
                    "assessment": {
                        "provider": {
                            "command": DEFAULT_COUNTEREXAMPLE_COMMAND,
                            "sessionId": session_id,
                            "sessionResumed": False,
                        }
                    }
                },
                {
                    "assessment": {
                        "provider": {
                            "command": DEFAULT_COUNTEREXAMPLE_RESUME_COMMAND.replace(
                                "{session_id}", session_id
                            ),
                            "sessionId": session_id,
                            "sessionResumed": True,
                        }
                    }
                },
            ]
        }
        validate(report)
        report["rounds"][1]["assessment"]["provider"]["command"] = (
            DEFAULT_COUNTEREXAMPLE_RESUME_COMMAND.replace(
                "{session_id}", "019fa8c6-b1d2-7841-a064-5202662bf9e5"
            )
        )
        with self.assertRaisesRegex(self.runner_error, "overridden or incoherent"):
            validate(report)


class LogosBenchmarkRunnerTests(unittest.TestCase):
    def test_codex_runtime_home_is_private_and_run_local(self) -> None:
        runner = runpy.run_path(str(RUNNER), run_name="runner_unit_test")
        stage = runner["stage_codex_runtime_home"]
        with tempfile.TemporaryDirectory(dir=RUNNER.parents[2]) as temp:
            root = Path(temp)
            source_home = root / "source-home"
            source_home.mkdir()
            (source_home / "auth.json").write_text(
                '{"credential":"fixture"}\n', encoding="utf-8"
            )
            config = root / "config.toml"
            config.write_text('model = "gpt-5.6-sol"\n', encoding="utf-8")
            runtime_parent = root / "runtime-parent"
            runtime_parent.mkdir()

            runtime_home = stage(source_home, config, runtime_parent)
            try:
                self.assertEqual(runtime_home.parent, runtime_parent)
                self.assertTrue(runtime_home.name.startswith(".codex-runtime-"))
                self.assertEqual(stat.S_IMODE(runtime_home.stat().st_mode), 0o700)
                self.assertEqual(
                    stat.S_IMODE((runtime_home / "auth.json").stat().st_mode),
                    0o600,
                )
                self.assertEqual(
                    stat.S_IMODE((runtime_home / "config.toml").stat().st_mode),
                    0o600,
                )
            finally:
                shutil.rmtree(runtime_home)

            with self.assertRaisesRegex(
                runner["RunnerError"], "outside the system temporary tree"
            ):
                stage(source_home, config, Path("/tmp"))

    def test_codex_runtime_root_is_private_and_outside_run_artifacts(self) -> None:
        runner = runpy.run_path(str(RUNNER), run_name="runner_unit_test")
        runtime_root = runner["prepare_codex_runtime_root"]()
        self.assertEqual(runtime_root, runner["CODEX_RUNTIME_ROOT"].resolve())
        self.assertEqual(stat.S_IMODE(runtime_root.stat().st_mode), 0o700)
        self.assertFalse(runtime_root.is_relative_to(runner["DEFAULT_RUN_ROOT"]))

    def test_proof_export_rejects_unsanitized_helper_symlink_and_keeps_sessions(
        self,
    ) -> None:
        launcher = (
            RUNNER.parents[2]
            / "crates/logos-solver/scripts/run-proof-agent-docker.sh"
        ).read_text(encoding="utf-8")
        export_error = launcher.index("non-regular proof-agent export entry")
        program_start = (
            launcher.rindex("3<<'PY'\n", 0, export_error) + len("3<<'PY'\n")
        )
        program_end = launcher.index("\nPY\n", program_start)
        extractor = launcher[program_start:program_end]

        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            staged = root / "staged/codex-home"
            (staged / "sessions").mkdir(parents=True)
            (staged / "sessions/session.jsonl").write_text(
                '{"type":"fixture"}\n', encoding="utf-8"
            )
            helper_dir = staged / "tmp/arg0/codex-arg-fixture"
            helper_dir.mkdir(parents=True)
            (helper_dir / "codex-execve-wrapper").symlink_to("/bin/true")

            def extract(name: str) -> subprocess.CompletedProcess[str]:
                archive = root / f"{name}.tar"
                destination = root / f"{name}-output"
                destination.mkdir()
                with tarfile.open(archive, mode="w") as bundle:
                    bundle.add(staged, arcname="codex-home", recursive=True)
                return subprocess.run(
                    [
                        sys.executable,
                        "-c",
                        extractor,
                        str(archive),
                        str(destination),
                        str(1024 * 1024),
                        "1024",
                    ],
                    text=True,
                    capture_output=True,
                    check=False,
                )

            unsafe = extract("unsafe")
            self.assertNotEqual(unsafe.returncode, 0)
            self.assertIn("non-regular proof-agent export entry", unsafe.stderr)

            shutil.rmtree(staged / "tmp")
            safe = extract("safe")
            self.assertEqual(safe.returncode, 0, safe.stderr)
            self.assertEqual(
                (root / "safe-output/codex-home/sessions/session.jsonl").read_text(
                    encoding="utf-8"
                ),
                '{"type":"fixture"}\n',
            )

    def test_final_theorem_detection_ignores_nested_rocq_comments(self) -> None:
        runner = runpy.run_path(str(RUNNER), run_name="runner_unit_test")
        declares = runner["problem_declares_final_theorem"]
        for mode, theorem, goal in (
            (
                "outcome-unconditional",
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
                other_mode = (
                    "conditional" if mode == "outcome-unconditional"
                    else "outcome-unconditional"
                )
                self.assertFalse(
                    declares(
                        f"Theorem {theorem} : {goal}.\nProof. exact I. Qed.",
                        other_mode,
                    )
                )

    def test_final_theorem_detection_requires_a_direct_theorem_sentence(self) -> None:
        runner = runpy.run_path(str(RUNNER), run_name="runner_unit_test")
        declares = runner["problem_declares_final_theorem"]
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

    def test_claim_detection_requires_the_fully_qualified_trusted_type(self) -> None:
        runner = runpy.run_path(str(RUNNER), run_name="runner_unit_test")
        declares_equivalence = runner["problem_declares_equivalence_claim"]
        declares_countermodel = runner["problem_declares_formal_countermodel_claim"]
        qualified_prefix = (
            "Definition generated_verification_claim : "
            "Logos.FormalSQL.VerificationConditions.verification_claim_kind :=\n"
            "  Logos.FormalSQL.VerificationConditions."
        )
        self.assertTrue(
            declares_equivalence(qualified_prefix + "VerificationEquivalence.")
        )
        self.assertTrue(
            declares_countermodel(qualified_prefix + "VerificationCountermodel.")
        )
        shadowable = (
            "Definition generated_verification_claim : verification_claim_kind :=\n"
            "  Logos.FormalSQL.VerificationConditions.VerificationCountermodel."
        )
        self.assertFalse(declares_equivalence(shadowable))
        self.assertFalse(declares_countermodel(shadowable))

    def test_rocq_comment_stripping_preserves_strings_and_line_count(self) -> None:
        runner = runpy.run_path(str(RUNNER), run_name="runner_unit_test")
        strip_comments = runner["strip_rocq_comments"]
        text = textwrap.dedent(
            '''\
            Definition label := "(* literal *) and a doubled "" quote".
            (* outer
               (* nested *)
            *)
            Definition kept := True.
            '''
        )
        stripped = strip_comments(text)
        self.assertIn('"(* literal *) and a doubled "" quote"', stripped)
        self.assertEqual(len(stripped.splitlines()), len(text.splitlines()))
        self.assertNotIn("outer", stripped)
        self.assertIn("Definition kept := True.", stripped)

    def test_v2_diagnostic_identity_accepts_problem_module_and_scratch(self) -> None:
        runner = runpy.run_path(str(RUNNER), run_name="runner_unit_test")
        validate_identity = runner["validate_diagnostic_identity"]
        validate_request = runner["validate_diagnostic_request_v2"]
        runner_error = runner["RunnerError"]
        digest = "a" * 64
        for mode, path, purpose in (
            ("problem", "Problem.v", "assembly"),
            ("module", "ProofModules/CoreFacts.v", "static-obligation"),
            ("scratch", "scratch/core/bridge.v", "semantic-equivalence"),
        ):
            validate_identity(mode, path, purpose, digest, "fixture")
            validate_request(
                {
                    "schemaVersion": 2,
                    "nonce": "b" * 64,
                    "mode": mode,
                    "candidatePath": path,
                    "purpose": purpose,
                    "candidateSha256": digest,
                    "candidateBytes": 123,
                    "requestedTimeoutSeconds": 30,
                },
                mode=mode,
                candidate_path=path,
                purpose=purpose,
                candidate_sha256=digest,
                candidate_bytes=123,
                requested_timeout_seconds=30,
                description="fixture request",
            )
        with self.assertRaisesRegex(runner_error, "normalized scratch"):
            validate_identity(
                "scratch", "scratch/../escape.v", "semantic-equivalence", digest, "fixture"
            )
        for invalid_module in (
            "ProofModules/lowercase.v",
            "ProofModules/Nested/Core.v",
            "ProofModules/Core.vo",
            "ProofModules/../Core.v",
        ):
            with self.subTest(path=invalid_module), self.assertRaisesRegex(
                runner_error, "UppercaseRocqIdentifier"
            ):
                validate_identity(
                    "module",
                    invalid_module,
                    "static-obligation",
                    digest,
                    "fixture",
                )
        with self.assertRaisesRegex(runner_error, "schemaVersion 2"):
            validate_request(
                {
                    "schemaVersion": 1,
                    "nonce": "b" * 64,
                    "mode": "problem",
                    "candidatePath": "Problem.v",
                    "purpose": "assembly",
                    "candidateSha256": digest,
                    "candidateBytes": 123,
                    "requestedTimeoutSeconds": 30,
                },
                mode="problem",
                candidate_path="Problem.v",
                purpose="assembly",
                candidate_sha256=digest,
                candidate_bytes=123,
                requested_timeout_seconds=30,
                description="fixture request",
            )

    def test_problem_diagnostic_checkpoint_dedup_tracks_latest_pass(self) -> None:
        runner = runpy.run_path(str(RUNNER), run_name="runner_unit_test")
        validate = runner["validate_diagnostic_checkpoint_dedup"]
        runner_error = runner["RunnerError"]
        initial = "a" * 64
        advanced = "b" * 64
        validate("scratch", initial, initial)
        validate("problem", advanced, initial)
        with self.assertRaisesRegex(
            runner_error, "duplicates the active compile checkpoint"
        ):
            validate("problem", initial, initial)
        with self.assertRaisesRegex(
            runner_error, "duplicates the active compile checkpoint"
        ):
            validate("problem", advanced, advanced)

    def test_proof_session_restarts_are_bounded_and_never_reuse_ids(self) -> None:
        runner = runpy.run_path(str(RUNNER), run_name="runner_unit_test")
        validate = runner["validate_proof_agent_session_sequence"]
        runner_error = runner["RunnerError"]
        self.assertEqual(
            runner["PROOF_AGENT_SESSION_RESTART_AFTER_FAILED_ROUNDS"], 16
        )
        rounds = [
            {
                "workspaceGeneration": 1,
                "sessionGeneration": 1,
                "sessionRestarted": False,
                "sessionId": "session-a",
                "checkpointTransition": (
                    "newWorkspaceInitial" if index == 0 else "continued"
                ),
                "compileCheckpointRestored": False,
                "success": False,
            }
            for index in range(16)
        ] + [
            {
                "workspaceGeneration": 1,
                "sessionGeneration": 2,
                "sessionRestarted": True,
                "sessionRestartReason": "failedRoundLimit",
                "sessionId": "session-b",
                "checkpointTransition": "restoredExisting",
                "compileCheckpointRestored": True,
                "success": False,
            }
        ]
        validate(rounds, "fixture", workspace_transitions_by_round={})

        rounds[-1]["sessionId"] = "session-a"
        with self.assertRaisesRegex(runner_error, "reused after a bounded restart"):
            validate(rounds, "fixture", workspace_transitions_by_round={})

    def test_failed_proof_round_audit_does_not_reject_later_clean_round(self) -> None:
        runner = runpy.run_path(str(RUNNER), run_name="runner_unit_test")
        validate = runner["validate_proof_round_audit"]
        rejected = {
            "success": False,
            "proofCheckExitCode": None,
            "proofCheckElapsedMs": None,
            "proofCheckTimedOut": False,
            "audit": {
                "passed": False,
                "scannedFiles": ["rounds/01/Problem.v"],
                "findings": [
                    {
                        "path": "rounds/01/Problem.v",
                        "line": 1,
                        "token": "generated_verification_claim",
                        "excerpt": "the claim is not complete",
                    }
                ],
            },
        }
        accepted = {
            "success": True,
            "proofCheckExitCode": 0,
            "proofCheckElapsedMs": 1,
            "proofCheckTimedOut": False,
            "audit": {
                "passed": True,
                "scannedFiles": ["rounds/02/Problem.v"],
                "findings": [],
            },
        }
        validate(rejected, "round 1")
        validate(accepted, "round 2")

        rejected["success"] = True
        with self.assertRaisesRegex(
            runner["RunnerError"], "claims success despite"
        ):
            validate(rejected, "forged round")

    def test_terminal_export_failure_may_preserve_missing_session_fact(self) -> None:
        runner = runpy.run_path(str(RUNNER), run_name="runner_unit_test")
        validate = runner["validate_proof_agent_session_sequence"]
        record = {
            "sessionGeneration": 1,
            "sessionRestarted": False,
            "sessionId": None,
            "success": False,
            "exitCode": 2,
            "usageError": (
                "Codex invocation did not emit exactly one thread.started event"
            ),
            "error": (
                "proof agent exited with status exit status: 2; proof repair "
                "cannot continue because Codex did not report the expected valid "
                "session UUID"
            ),
        }
        validate(
            [record],
            "recovery fixture",
            allow_terminal_unavailable_session=True,
        )
        with self.assertRaisesRegex(
            runner["RunnerError"], "has no sessionId"
        ):
            validate([record], "ordinary fixture")

    def test_failed_round_report_binds_run_json_with_only_host_suffix(self) -> None:
        runner = runpy.run_path(str(RUNNER), run_name="runner_unit_test")
        validate = runner["validate_failed_round_run_record_binding"]
        run_record = {
            "round": 1,
            "success": False,
            "exitCode": 2,
            "error": "proof agent exited with status exit status: 2",
        }
        report_round = dict(run_record)
        report_round["error"] += (
            "; proof repair cannot continue because Codex did not report the "
            "expected valid session UUID"
        )
        validate(report_round, run_record, "fixture")

        report_round["exitCode"] = 0
        with self.assertRaisesRegex(runner["RunnerError"], "differs"):
            validate(report_round, run_record, "forged fixture")

    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.input_root = self.root / "generated"
        self.fake_bin = self.root / "bin"
        self.fake_bin.mkdir()
        self.fake_docker = self.fake_bin / "docker"
        self.write_fake_docker("d")
        self.fake_bwrap = self.fake_bin / "bwrap"
        shutil.copy2(shutil.which("true") or "/bin/true", self.fake_bwrap)
        self.fake_bwrap.chmod(0o755)
        self.fake_codex = self.fake_bin / "codex"
        self.fake_codex.write_text(
            "#!/bin/sh\n"
            'if [ "$1" = "--version" ]; then echo "codex-cli 0.145.0-test"; exit 0; fi\n'
            "exit 99\n",
            encoding="utf-8",
        )
        self.fake_codex.chmod(0o755)
        self.fake_codex_home = self.root / "codex-home"
        self.fake_codex_home.mkdir()
        (self.fake_codex_home / "config.toml").write_text(
            'model = "gpt-5.6-sol"\n'
            'model_reasoning_effort = "medium"\n'
            'preferred_auth_method = "apikey"\n'
            'model_provider = "test-provider"\n\n'
            "[model_providers.test-provider]\n"
            'name = "Test Provider"\n'
            'base_url = "http://127.0.0.1:2455/backend-api/codex"\n'
            'wire_api = "responses"\n'
            "supports_websockets = false\n"
            "requires_openai_auth = true\n\n"
            '[projects."/unrelated"]\ntrust_level = "trusted"\n',
            encoding="utf-8",
        )
        (self.fake_codex_home / "auth.json").write_text(
            json.dumps({"auth_mode": "apikey", "OPENAI_API_KEY": "test-secret"}),
            encoding="utf-8",
        )
        (self.fake_codex_home / "credentials.json").write_text(
            json.dumps({"disabled-plugin-token": "test-secret"}), encoding="utf-8"
        )
        self.fake_psql = self.fake_bin / "psql"
        self.fake_psql.write_text(
            "#!/bin/sh\n"
            'if [ "$1" = "--version" ]; then echo "psql (PostgreSQL) 17.4"; exit 0; fi\n'
            "printf '17.4\\t170004\\tC\\tC\\tlibc\\tUTF8\\tUTC\\t96\\n'\n",
            encoding="utf-8",
        )
        self.fake_psql.chmod(0o755)
        self.fake_rocq_switch = self.root / "fake-rocq-switch"
        fake_rocq_bin = self.fake_rocq_switch / "_opam/bin"
        fake_rocq_bin.mkdir(parents=True)
        self.fake_rocq_stdlib = self.fake_rocq_switch / "_opam/lib/coq"
        (self.fake_rocq_stdlib / "theories/Init").mkdir(parents=True)
        (self.fake_rocq_stdlib / "theories/Init/Prelude.vo").write_bytes(
            b"synthetic trusted stdlib object"
        )
        fake_rocq_lib = self.fake_rocq_switch / "_opam/lib"
        for runtime_directory in ("stublibs", "ocaml", "findlib", "zarith"):
            (fake_rocq_lib / runtime_directory).mkdir()
        (fake_rocq_lib / "findlib.conf").write_text(
            f'destdir="{fake_rocq_lib}"\n'
            f'path="{fake_rocq_lib / "ocaml"}:{fake_rocq_lib}"\n'
            'ocamlc="ocamlc.opt"\n'
            'ocamlopt="ocamlopt.opt"\n'
            'ocamldep="ocamldep.opt"\n'
            'ocamldoc="ocamldoc.opt"\n',
            encoding="utf-8",
        )
        fake_rocq_runtime = fake_rocq_lib / "rocq-runtime"
        fake_rocq_runtime.mkdir()
        (fake_rocq_runtime / "META").write_text(
            'version = "synthetic"\n', encoding="utf-8"
        )
        fake_rocq_source = self.root / "fake-rocq.c"
        fake_rocq_source.write_text(
            textwrap.dedent(
                r"""
                #include <stdio.h>
                #include <string.h>

                static int ends_with_v(const char *value) {
                    size_t length = strlen(value);
                    return length >= 2 && value[length - 2] == '.' && value[length - 1] == 'v';
                }

                int main(int argc, char **argv) {
                    int index;
                    if (argc >= 2 && strcmp(argv[1], "dep") == 0) {
                        for (index = 2; index < argc; ++index) {
                            if (ends_with_v(argv[index])) {
                                puts(argv[index]);
                            }
                        }
                        return 0;
                    }
                    if (argc >= 2 && strcmp(argv[1], "compile") == 0) {
                        for (index = 2; index + 1 < argc; ++index) {
                            if (strcmp(argv[index], "-o") == 0) {
                                FILE *output = fopen(argv[index + 1], "wb");
                                if (output == NULL) {
                                    return 2;
                                }
                                fputs("synthetic private Rocq object\n", output);
                                return fclose(output) == 0 ? 0 : 3;
                            }
                        }
                        return 4;
                    }
                    if (argc >= 2 && strcmp(argv[1], "--version") == 0) {
                        puts("Rocq synthetic-test");
                    }
                    return 0;
                }
                """
            ).lstrip(),
            encoding="utf-8",
        )
        cc = shutil.which("cc")
        if cc is None:
            self.fail("the runner integration fixture requires a C compiler")
        built = subprocess.run(
            [cc, "-O2", "-o", str(fake_rocq_bin / "rocq"), str(fake_rocq_source)],
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
        self.assertEqual(built.returncode, 0, built.stderr)
        for path in (
            fake_rocq_bin / "rocqchk",
            fake_rocq_runtime / "rocqworker",
            fake_rocq_runtime / "rocqnative",
            fake_rocq_runtime / "synthetic_plugin.cmxs",
        ):
            shutil.copy2(fake_rocq_bin / "rocq", path)
            path.chmod(0o755)
        self.fake_rocq_worker = fake_rocq_runtime / "rocqworker"
        self.fake_rocq_checker = fake_rocq_bin / "rocqchk"
        self.bash_env_marker = self.root / "hostile-bash-env-executed"
        self.hostile_bash_env = self.root / "hostile-bash-env.sh"
        self.hostile_bash_env.write_text(
            "readlink() { printf executed >>'"
            + str(self.bash_env_marker)
            + '\'; /usr/bin/readlink "$@"; }\n',
            encoding="utf-8",
        )
        self.environment = dict(os.environ)
        self.environment["PATH"] = (
            str(self.fake_bin) + os.pathsep + self.environment.get("PATH", "")
        )
        self.environment.update(
            {
                "LOGOS_PROOF_AGENT_MEMORY_LIMIT": "999m",
                "LOGOS_PROOF_AGENT_MEMORY_LIMIT_MIB": "999",
                "LOGOS_PROOF_CHECK_TIMEOUT": "999",
                "LOGOS_SOLVER_IMAGE": "wrong-image",
                "LOGOS_UNTRUSTED_AGENT_CHECK": "1",
                "LOGOS_TRUSTED_ENVIRONMENT_PREFLIGHT": "1",
                "LOGOS_HOST_DIAGNOSTIC_CHECK": "1",
                "LOGOS_CALCITE_IR_COMMAND": "/tmp/hostile-frontend",
                "LOGOS_CALCITE_RUNTIME_CLASSPATH_FILE": "/tmp/hostile-classpath",
                "CODEX_HOME": str(self.fake_codex_home),
                "LOGOS_SOLVER_CODEX_HOME": "/tmp/hostile-codex-home",
                "LOGOS_SOLVER_CODEX_CONFIG": "/tmp/hostile-codex-config.toml",
                "LOGOS_CASE_SUPERVISOR_PID": "999",
                "OPENAI_BASE_URL": "https://hostile.invalid/openai",
                "CODEX_BASE_URL": "https://hostile.invalid/codex",
                "OPENAI_API_BASE": "https://hostile.invalid/legacy",
                "AZURE_OPENAI_ENDPOINT": "https://hostile.invalid/azure",
                "OPENAI_API_KEY": "hostile-api-key",
                "CODEX_API_KEY": "hostile-codex-key",
                "HTTP_PROXY": "http://hostile.invalid:8080",
                "NO_PROXY": "hostile.invalid",
                "BASH_ENV": str(self.hostile_bash_env),
                "ENV": str(self.hostile_bash_env),
                "BASH_FUNC_readlink%%": "() { :; }",
                "LD_PRELOAD": "",
                "LD_LIBRARY_PATH": "/tmp/hostile-libraries",
                "OCAMLPATH": "/tmp/hostile-ocaml",
                "CAML_LD_LIBRARY_PATH": "/tmp/hostile-caml",
                "CDPATH": "/tmp/hostile-cdpath",
                "TMPDIR": "/tmp/hostile-tmpdir",
                "PYTHONHOME": "",
                "PYTHONPATH": "/tmp/hostile-python-path",
                "MAVEN_VERSION": "0.0-hostile",
                "JAVA_TOOL_OPTIONS": "-Dhostile=true",
            }
        )
        self.fake_solver = self.root / "fake-solver"
        fake_solver_source = textwrap.dedent(
            """\
                #!/usr/bin/env python3
                import hashlib
                import json
                import os
                import signal
                import subprocess
                import sys
                import time
                from pathlib import Path

                args = sys.argv[1:]
                log_dir = Path(args[args.index("--log-dir") + 1])
                log_dir.mkdir(parents=True, exist_ok=True)
                with Path(__file__).with_name("invocations.log").open(
                    "a", encoding="utf-8"
                ) as invocation_log:
                    invocation_log.write(log_dir.name + "\\n")
                (log_dir / "argv.json").write_text(json.dumps(args), encoding="utf-8")
                environment_record = dict(os.environ)
                runtime_home = Path(os.environ["CODEX_HOME"])
                environment_record["runtimeConfigSha256"] = hashlib.sha256(
                    (runtime_home / "config.toml").read_bytes()
                ).hexdigest()
                environment_record["runtimeAuthPresent"] = (runtime_home / "auth.json").is_file()
                environment_record["runtimeCredentialsPresent"] = (runtime_home / "credentials.json").is_file()
                (log_dir / "environment.json").write_text(
                    json.dumps(environment_record),
                    encoding="utf-8",
                )
                if "timeout" in log_dir.name:
                    def graceful_term(_signum, _frame):
                        (log_dir / "term-observed").write_text(
                            "SIGTERM\\n", encoding="utf-8"
                        )
                        raise SystemExit(143)
                    signal.signal(signal.SIGTERM, graceful_term)
                    child_token = "logos-fake-solver-child:" + str(log_dir.resolve())
                    child = subprocess.Popen(
                        [
                            sys.executable,
                            "-c",
                            "import time; time.sleep(60)",
                            child_token,
                        ],
                        start_new_session=True,
                    )
                    (log_dir / "child.token").write_text(
                        child_token, encoding="utf-8"
                    )
                    time.sleep(60)
                elif "nonzero" in log_dir.name:
                    sys.stderr.write("prefix:" + "x" * 9000 + "\\n")
                    sys.stderr.write("SQLSTATE 22012: division by zero — 除以零\\n")
                    raise SystemExit(7)
                else:
                    usage = {
                        "model": "gpt-5.6-sol",
                        "inputTokens": 100,
                        "cachedInputTokens": 20,
                        "outputTokens": 10,
                        "totalTokens": 110,
                        "estimatedCostUsd": 0.00071,
                    }
                    if "missingusage" in log_dir.name:
                        usage = None
                    elif "malformedusage" in log_dir.name:
                        usage["totalTokens"] = 999
                    def option(name):
                        for index, value in enumerate(args):
                            if value == name:
                                return args[index + 1]
                            if value.startswith(name + "="):
                                return value.split("=", 1)[1]
                        raise RuntimeError(name)

                    schema_path = Path(option("--schema"))
                    source_path = Path(option("--source"))
                    target_path = Path(option("--target"))
                    module_diagnostic = "modulediagnostic" in log_dir.name
                    module_source = b"Lemma CoreFacts : True. exact I. Qed.\\n"
                    proof_root = log_dir / "proof-stage/formal-sql"
                    proof_root.mkdir(parents=True, exist_ok=True)
                    (proof_root / "run-rocq-check.sh").write_bytes(
                        __RUN_ROCQ_CHECK_SCRIPT__
                    )
                    trusted_launcher_root = (
                        log_dir / "proof-stage/proof-agent/trusted-launcher"
                    )
                    trusted_launcher_root.mkdir(parents=True, exist_ok=True)
                    (trusted_launcher_root / "run-proof-agent-docker.sh").write_bytes(
                        __RUN_PROOF_AGENT_DOCKER_SCRIPT__
                    )
                    (trusted_launcher_root / "run-trusted-rocq-check.sh").write_bytes(
                        __RUN_TRUSTED_ROCQ_CHECK_SCRIPT__
                    )
                    (proof_root / "Schema.v").write_text(
                        "Definition synthetic_schema : True := I.\\n", encoding="utf-8"
                    )
                    (proof_root / "Queries.v").write_text(
                        "Definition synthetic_queries : True := I.\\n", encoding="utf-8"
                    )
                    (proof_root / "Witness.v").write_text(
                        "Definition synthetic_witness : True := I.\\n", encoding="utf-8"
                    )
                    if module_diagnostic:
                        final_modules = proof_root / "ProofModules"
                        final_modules.mkdir()
                        (final_modules / "CoreFacts.v").write_bytes(module_source)
                    cache_root = log_dir / "proof-stage/proof-agent/trusted-diagnostic-cache"
                    cache_root.mkdir(parents=True, exist_ok=True)
                    for cache_name in ("Schema.v", "Queries.v", "Witness.v"):
                        (cache_root / cache_name).write_bytes(
                            (proof_root / cache_name).read_bytes()
                        )
                    if "forgedwitnesscache" in log_dir.name:
                        (cache_root / "Witness.v").write_text(
                            "Definition forged_witness : True := I.\\n",
                            encoding="utf-8",
                        )
                    (cache_root / "Schema.vo").write_bytes(b"schema-object")
                    (cache_root / "Queries.vo").write_bytes(b"queries-object")
                    (cache_root / "Witness.vo").write_bytes(b"witness-object")
                    cache_module_root = cache_root / "ProofModules"
                    cache_module_root.mkdir()
                    if module_diagnostic:
                        (cache_module_root / "ORDER").write_bytes(b"CoreFacts.v\\n")
                        (cache_module_root / "CoreFacts.v").write_bytes(module_source)
                        (cache_module_root / "CoreFacts.vo").write_bytes(b"module-object")
                    else:
                        (cache_module_root / "ORDER").write_bytes(b"")
                    cache_entries = [
                        "Schema.v",
                        "Schema.vo",
                        "Queries.v",
                        "Queries.vo",
                        "Witness.v",
                        "Witness.vo",
                        "ProofModules/ORDER",
                    ]
                    if module_diagnostic:
                        cache_entries.extend(
                            ("ProofModules/CoreFacts.v", "ProofModules/CoreFacts.vo")
                        )
                    cache_manifest = "".join(
                        f"{hashlib.sha256((cache_root / name).read_bytes()).hexdigest()}  {name}\\n"
                        for name in cache_entries
                    )
                    (cache_root / "SHA256SUMS").write_text(
                        cache_manifest, encoding="utf-8"
                    )
                    initial_problem = (
                        b"Definition generated_verification_claim : "
                        b"Logos.FormalSQL.VerificationConditions.verification_claim_kind := "
                        b"Logos.FormalSQL.VerificationConditions.VerificationEquivalence.\\n"
                        b"Theorem generated_queries_verified : True. exact I. Qed.\\n"
                        if "duplicatecheckpoint" in log_dir.name
                        else b"Definition initial_problem : True := I.\\n"
                    )
                    case_metadata = json.loads(
                        (source_path.parent / "metadata.json").read_text()
                    )
                    case_relative_dir = case_metadata["flatCaseId"]
                    integrity_contract = {
                        "caseId": case_relative_dir,
                        "source": str(source_path.parent / "metadata.json"),
                        "tables": [],
                    }
                    sql_environment = {
                        "defaultCollation": option("--sql-default-collation"),
                        "characterClassification": option("--sql-character-classification"),
                        "localeProvider": option("--sql-locale-provider"),
                        "serverEncoding": option("--sql-server-encoding"),
                    }
                    verification_input = {
                        "sqlEnvironment": sql_environment,
                        "integrityContract": integrity_contract,
                        "schema": {"path": str(schema_path), "sql": schema_path.read_text()},
                        "sourceQuery": {"path": str(source_path), "sql": source_path.read_text()},
                        "targetQuery": {"path": str(target_path), "sql": target_path.read_text()},
                    }
                    input_artifact_root = log_dir / "input"
                    input_artifact_root.mkdir()
                    input_artifacts = {
                        "verification-input.json": verification_input,
                        "integrity-contract.json": integrity_contract,
                        "schema-ir.json": {"tables": []},
                        "source-ir.json": {},
                        "target-ir.json": {},
                    }
                    for input_name, input_value in input_artifacts.items():
                        (input_artifact_root / input_name).write_text(
                            json.dumps(input_value, indent=2) + "\\n",
                            encoding="utf-8",
                        )
                    goal_source = b"Definition synthetic_goal : True := I.\\n"
                    lowering_input_bindings = {
                        "schemaVersion": 1,
                        "caseId": case_relative_dir,
                        "schemaSqlSha256": hashlib.sha256(schema_path.read_bytes()).hexdigest(),
                        "sourceSqlSha256": hashlib.sha256(source_path.read_bytes()).hexdigest(),
                        "targetSqlSha256": hashlib.sha256(target_path.read_bytes()).hexdigest(),
                        "verificationInputSha256": hashlib.sha256(
                            (input_artifact_root / "verification-input.json").read_bytes()
                        ).hexdigest(),
                        "integrityContractSha256": hashlib.sha256(
                            (input_artifact_root / "integrity-contract.json").read_bytes()
                        ).hexdigest(),
                        "schemaIrSha256": hashlib.sha256(
                            (input_artifact_root / "schema-ir.json").read_bytes()
                        ).hexdigest(),
                        "sourceIrSha256": hashlib.sha256(
                            (input_artifact_root / "source-ir.json").read_bytes()
                        ).hexdigest(),
                        "targetIrSha256": hashlib.sha256(
                            (input_artifact_root / "target-ir.json").read_bytes()
                        ).hexdigest(),
                    }
                    lowering = {
                        "sqlEnvironment": sql_environment,
                        "inputBindings": lowering_input_bindings,
                        "schema": {"schema": {"rocqModule": (proof_root / "Schema.v").read_text()}},
                        "queryModule": {"rocqModule": (proof_root / "Queries.v").read_text()},
                        "proofModule": {"rocqModule": initial_problem.decode()},
                        "goalModule": {"rocqModule": goal_source.decode()},
                    }
                    (log_dir / "proof-stage/formal-sql-lowering.json").write_text(
                        json.dumps(lowering, indent=2) + "\\n", encoding="utf-8"
                    )
                    generation_root = (
                        log_dir
                        / "proof-stage/proof-agent/workspace-generations/0001"
                    )
                    initial_root = generation_root / "initial-problem-checkpoint"
                    initial_root.mkdir(parents=True, exist_ok=True)
                    (initial_root / "Problem.v").write_bytes(initial_problem)
                    (initial_root / "stdout.txt").write_bytes(b"")
                    (initial_root / "stderr.txt").write_bytes(b"")
                    initial_invocation = {
                        "sequence": 0,
                        "mode": "problem",
                        "candidateSha256": hashlib.sha256(initial_problem).hexdigest(),
                        "candidatePath": "Problem.v",
                        "purpose": "assembly",
                        "compilePassed": True,
                        "problemCompilePassed": True,
                        "compileCheckpointAdvanced": True,
                        "stdoutSha256": hashlib.sha256(b"").hexdigest(),
                        "stderrSha256": hashlib.sha256(b"").hexdigest(),
                        "requestedTimeoutSeconds": int(option("--proof-check-timeout-seconds")),
                        "effectiveTimeoutSeconds": int(option("--proof-check-timeout-seconds")),
                        "startedAtUnixMs": 900,
                        "elapsedMs": 1,
                        "exitCode": 0,
                        "timedOut": False,
                    }
                    if "initialelapsedwarning" in log_dir.name:
                        initial_invocation["elapsedMs"] = (
                            int(option("--proof-check-timeout-seconds")) * 1000 + 6_001
                        )
                    (initial_root / "invocation.json").write_text(
                        json.dumps(initial_invocation), encoding="utf-8"
                    )
                    preflight_invocation = {
                        "timeoutSeconds": int(option("--proof-check-timeout-seconds")),
                        "elapsedMs": 1,
                        "exitCode": 0,
                        "timedOut": False,
                    }
                    if "preflightelapsedwarning" in log_dir.name:
                        preflight_invocation["elapsedMs"] = (
                            int(option("--proof-check-timeout-seconds")) * 1000 + 6_001
                        )
                    preflight_root = generation_root / "trusted-environment-preflight"
                    preflight_root.mkdir()
                    (preflight_root / "stdout.txt").write_bytes(b"")
                    (preflight_root / "stderr.txt").write_bytes(b"")
                    (preflight_root / "invocation.json").write_text(
                        json.dumps(preflight_invocation), encoding="utf-8"
                    )
                    final_problem = (
                        "Definition generated_verification_claim : "
                        "Logos.FormalSQL.VerificationConditions.verification_claim_kind := "
                        "Logos.FormalSQL.VerificationConditions.VerificationEquivalence.\\n"
                        "Theorem generated_queries_verified : True. exact I. Qed.\\n"
                    )
                    (proof_root / "Problem.v").write_text(
                        final_problem,
                        encoding="utf-8",
                    )
                    context_contents = {
                        "source.sql": source_path.read_bytes(),
                        "target.sql": target_path.read_bytes(),
                        "query-shape.json": b"{}\\n",
                        "ordered-signatures.json": b"[]\\n",
                        "observation-certificates.json": b"[]\\n",
                        "semantic-primer.md": b"Synthetic semantic primer.\\n",
                        "search-rocq-declarations.py": b"#!/usr/bin/env python3\\n",
                        "Goal.v": goal_source,
                    }
                    for context_name, context_bytes in context_contents.items():
                        (proof_root / context_name).write_bytes(context_bytes)

                    def context_binding(name):
                        data = (proof_root / name).read_bytes()
                        return {
                            "path": name,
                            "bytes": len(data),
                            "sha256": hashlib.sha256(data).hexdigest(),
                        }

                    context_manifest = {
                        "schemaVersion": 8,
                        "authority": "navigation context only; exact SQL is pipeline input and generated Rocq plus FormalSQL and the Rocq kernel remain authoritative",
                        "verificationMode": option("--verification-mode").replace("-", "_"),
                        "staticPromptAndPrimerBytes": 100,
                        "sourceSql": context_binding("source.sql"),
                        "targetSql": context_binding("target.sql"),
                        "queryShape": context_binding("query-shape.json"),
                        "orderedSignatures": context_binding("ordered-signatures.json"),
                        "observationCertificates": context_binding("observation-certificates.json"),
                        "semanticPrimer": context_binding("semantic-primer.md"),
                        "declarationSearch": context_binding("search-rocq-declarations.py"),
                        "schemaModule": context_binding("Schema.v"),
                        "queriesModule": context_binding("Queries.v"),
                        "witnessModule": context_binding("Witness.v"),
                        "goalModule": context_binding("Goal.v"),
                    }
                    context_manifest_bytes = (
                        json.dumps(context_manifest, indent=2) + "\\n"
                    ).encode()
                    (proof_root / "context-manifest.json").write_bytes(
                        context_manifest_bytes
                    )
                    context_sha256 = hashlib.sha256(context_manifest_bytes).hexdigest()
                    context_report = {
                        "manifestPath": "proof-stage/formal-sql/context-manifest.json",
                        "manifestSha256": context_sha256,
                        "manifestBytes": len(context_manifest_bytes),
                        "sourceSqlSha256": context_manifest["sourceSql"]["sha256"],
                        "sourceSqlBytes": context_manifest["sourceSql"]["bytes"],
                        "targetSqlSha256": context_manifest["targetSql"]["sha256"],
                        "targetSqlBytes": context_manifest["targetSql"]["bytes"],
                        "queryShapeSha256": context_manifest["queryShape"]["sha256"],
                        "queryShapeBytes": context_manifest["queryShape"]["bytes"],
                        "orderedSignaturesSha256": context_manifest["orderedSignatures"]["sha256"],
                        "orderedSignaturesBytes": context_manifest["orderedSignatures"]["bytes"],
                        "observationCertificatesSha256": context_manifest["observationCertificates"]["sha256"],
                        "observationCertificatesBytes": context_manifest["observationCertificates"]["bytes"],
                        "schemaModuleSha256": context_manifest["schemaModule"]["sha256"],
                        "schemaModuleBytes": context_manifest["schemaModule"]["bytes"],
                        "queriesModuleSha256": context_manifest["queriesModule"]["sha256"],
                        "queriesModuleBytes": context_manifest["queriesModule"]["bytes"],
                        "witnessModuleSha256": context_manifest["witnessModule"]["sha256"],
                        "witnessModuleBytes": context_manifest["witnessModule"]["bytes"],
                        "problemModuleBytes": len(initial_problem),
                        "goalModuleBytes": context_manifest["goalModule"]["bytes"],
                        "semanticPrimerBytes": context_manifest["semanticPrimer"]["bytes"],
                        "declarationSearchSha256": context_manifest["declarationSearch"]["sha256"],
                        "declarationSearchBytes": context_manifest["declarationSearch"]["bytes"],
                        "generatedContextBytes": sum(
                            binding["bytes"]
                            for binding in context_manifest.values()
                            if isinstance(binding, dict) and "bytes" in binding
                        ) + len(initial_problem) + len(context_manifest_bytes) + (
                            100 - context_manifest["semanticPrimer"]["bytes"]
                        ),
                    }
                    round_root = log_dir / "proof-stage/proof-agent/rounds/01"
                    checked = round_root / "checked-workspace"
                    checked.mkdir(parents=True, exist_ok=True)
                    (checked / "Problem.v").write_text(final_problem, encoding="utf-8")
                    (checked / "context-manifest.json").write_bytes(
                        context_manifest_bytes
                    )
                    for checked_name in (
                        "Schema.v",
                        "Queries.v",
                        "Witness.v",
                        "Goal.v",
                        "source.sql",
                        "target.sql",
                        "query-shape.json",
                        "ordered-signatures.json",
                        "observation-certificates.json",
                        "semantic-primer.md",
                        "search-rocq-declarations.py",
                    ):
                        (checked / checked_name).write_bytes(
                            (proof_root / checked_name).read_bytes()
                        )
                    checked_modules = checked / "ProofModules"
                    checked_modules.mkdir()
                    if module_diagnostic:
                        (checked_modules / "CoreFacts.v").write_bytes(module_source)
                    closure = checked / "authority-closure.txt"
                    closure.write_text(
                        "# schemaVersion: 1\\n# synthetic source/object closure\\n",
                        encoding="utf-8",
                    )
                    candidate_sha256 = hashlib.sha256(final_problem.encode()).hexdigest()
                    diagnostic_root = round_root / "interactive-diagnostics/01"
                    diagnostic_checked = diagnostic_root / "checked-workspace"
                    diagnostic_checked.mkdir(parents=True, exist_ok=True)
                    (diagnostic_checked / "Problem.v").write_text(
                        final_problem, encoding="utf-8"
                    )
                    if module_diagnostic:
                        diagnostic_module_root = diagnostic_checked / "ProofModules"
                        diagnostic_module_root.mkdir()
                        (diagnostic_module_root / "CoreFacts.v").write_bytes(module_source)
                    (diagnostic_root / "stdout.txt").write_bytes(b"")
                    (diagnostic_root / "stderr.txt").write_bytes(b"")
                    diagnostic_audit = {
                        "passed": True,
                        "scannedFiles": [
                            "proof-stage/proof-agent/rounds/01/interactive-diagnostics/01/checked-workspace/Problem.v"
                        ],
                        "findings": [],
                    }
                    (diagnostic_root / "audit.json").write_text(
                        json.dumps(diagnostic_audit), encoding="utf-8"
                    )
                    diagnostic_mode = (
                        "module"
                        if module_diagnostic
                        else (
                            "scratch"
                            if any(
                                marker in log_dir.name
                                for marker in ("scratchcheckpoint", "elapsed124warning")
                            )
                            else "problem"
                        )
                    )
                    diagnostic_candidate_path = (
                        "ProofModules/CoreFacts.v"
                        if diagnostic_mode == "module"
                        else (
                            "scratch/core.v"
                            if diagnostic_mode == "scratch"
                            else "Problem.v"
                        )
                    )
                    diagnostic_purpose = (
                        "static-obligation"
                        if diagnostic_mode == "module"
                        else (
                            "semantic-equivalence"
                            if diagnostic_mode == "scratch"
                            else "assembly"
                        )
                    )
                    diagnostic_candidate_bytes = (
                        module_source if diagnostic_mode == "module" else final_problem.encode()
                    )
                    candidate_sha256 = hashlib.sha256(
                        diagnostic_candidate_bytes
                    ).hexdigest()
                    request = {
                        "schemaVersion": 1 if "legacyschema" in log_dir.name else 2,
                        "nonce": "a" * 64,
                        "mode": diagnostic_mode,
                        "candidatePath": diagnostic_candidate_path,
                        "purpose": diagnostic_purpose,
                        "candidateSha256": candidate_sha256,
                        "candidateBytes": len(diagnostic_candidate_bytes),
                        "requestedTimeoutSeconds": 5,
                    }
                    invocation = {
                        "sequence": 1,
                        "mode": diagnostic_mode,
                        "candidateSha256": candidate_sha256,
                        "candidatePath": diagnostic_candidate_path,
                        "purpose": diagnostic_purpose,
                        "compilePassed": True,
                        "problemCompilePassed": (
                            diagnostic_mode == "problem"
                            or "scratchcheckpoint" in log_dir.name
                        ),
                        "compileCheckpointAdvanced": (
                            diagnostic_mode == "problem"
                            or "scratchcheckpoint" in log_dir.name
                        ),
                        "stdoutSha256": hashlib.sha256(b"").hexdigest(),
                        "stderrSha256": hashlib.sha256(b"").hexdigest(),
                        "requestedTimeoutSeconds": 5,
                        "effectiveTimeoutSeconds": 5,
                        "startedAtUnixMs": 1000,
                        "elapsedMs": 1,
                        "exitCode": 0,
                        "timedOut": False,
                    }
                    if (
                        "elapsedwarning" in log_dir.name
                        and "finalelapsedwarning" not in log_dir.name
                    ):
                        invocation["elapsedMs"] = 12_001
                    elif "modulediagnosticlate2" in log_dir.name:
                        invocation["exitCode"] = 2
                    elif "modulediagnosticlate" in log_dir.name:
                        invocation["exitCode"] = 143
                    elif "elapsed124warning" in log_dir.name:
                        invocation.update(
                            {
                                "compilePassed": False,
                                "problemCompilePassed": False,
                                "compileCheckpointAdvanced": False,
                                "elapsedMs": 12_001,
                                "exitCode": 124,
                                "timedOut": True,
                            }
                        )
                    elif "elapsedmarginboundary" in log_dir.name:
                        invocation["elapsedMs"] = 11_000
                    if "backwardclock" in log_dir.name:
                        first_problem = (
                            final_problem + "\\n(* pre-clock-adjustment candidate *)\\n"
                        ).encode()
                        (diagnostic_checked / "Problem.v").write_bytes(first_problem)
                        candidate_sha256 = hashlib.sha256(first_problem).hexdigest()
                        request["candidateSha256"] = candidate_sha256
                        request["candidateBytes"] = len(first_problem)
                        invocation["candidateSha256"] = candidate_sha256
                        invocation["elapsedMs"] = 100
                    (diagnostic_root / "request.json").write_text(
                        json.dumps(request), encoding="utf-8"
                    )
                    (diagnostic_root / "invocation.json").write_text(
                        json.dumps(invocation), encoding="utf-8"
                    )
                    reported_invocations = [dict(invocation)]
                    second_diagnostic_root = None
                    second_request = None
                    second_invocation = None
                    second_audit = None
                    if "backwardclock" in log_dir.name:
                        second_diagnostic_root = (
                            round_root / "interactive-diagnostics/02"
                        )
                        second_checked = second_diagnostic_root / "checked-workspace"
                        second_checked.mkdir(parents=True)
                        (second_checked / "Problem.v").write_text(
                            final_problem, encoding="utf-8"
                        )
                        (second_diagnostic_root / "stdout.txt").write_bytes(b"")
                        (second_diagnostic_root / "stderr.txt").write_bytes(b"")
                        second_audit = {
                            "passed": True,
                            "scannedFiles": [
                                "proof-stage/proof-agent/rounds/01/interactive-diagnostics/02/checked-workspace/Problem.v"
                            ],
                            "findings": [],
                        }
                        (second_diagnostic_root / "audit.json").write_text(
                            json.dumps(second_audit), encoding="utf-8"
                        )
                        candidate_sha256 = hashlib.sha256(
                            final_problem.encode()
                        ).hexdigest()
                        second_request = {
                            **request,
                            "candidateSha256": candidate_sha256,
                            "candidateBytes": len(final_problem.encode()),
                        }
                        second_invocation = {
                            **invocation,
                            "sequence": 2,
                            "candidateSha256": candidate_sha256,
                            "startedAtUnixMs": 900,
                            "elapsedMs": 1,
                        }
                        (second_diagnostic_root / "request.json").write_text(
                            json.dumps(second_request), encoding="utf-8"
                        )
                        (second_diagnostic_root / "invocation.json").write_text(
                            json.dumps(second_invocation), encoding="utf-8"
                        )
                        reported_invocations.append(dict(second_invocation))
                    (round_root / "interactive-diagnostics.json").write_text(
                        json.dumps(reported_invocations), encoding="utf-8"
                    )
                    if "forgedtelemetry" in log_dir.name:
                        reported_invocations[0]["elapsedMs"] = 2
                    def artifact_binding(path):
                        return {
                            "path": path.relative_to(log_dir).as_posix(),
                            "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
                            "bytes": path.stat().st_size,
                        }

                    rejected_source_audits = []
                    accepted_request_ordinal = 1
                    diagnostic_requests_seen = 0 if "nodiagnostic" in log_dir.name else 1
                    diagnostic_reserved_timeout = 0 if "nodiagnostic" in log_dir.name else 5
                    diagnostic_other_rejected = 0
                    if any(name in log_dir.name for name in (
                        "rejecteddiagnostic",
                        "tamperrejectedaudit",
                        "rejectedinvoked",
                    )):
                        accepted_request_ordinal = 2
                        diagnostic_requests_seen = 2 if "rejectedinvoked" in log_dir.name else 3
                        diagnostic_reserved_timeout = 10 if "rejectedinvoked" in log_dir.name else 15
                        diagnostic_other_rejected = 0 if "rejectedinvoked" in log_dir.name else 1
                        rejected_root = round_root / "rejected-diagnostic-source-audits/01"
                        rejected_root.mkdir(parents=True)
                        rejected_problem = (
                            final_problem.encode()
                            if "rejectedinvoked" in log_dir.name
                            else b'Load "forbidden.vo".\\n'
                        )
                        rejected_candidate = hashlib.sha256(rejected_problem).hexdigest()
                        (rejected_root / "Problem.v").write_bytes(rejected_problem)
                        rejected_request = {
                            "schemaVersion": 2,
                            "nonce": "a" * 64,
                            "mode": "problem",
                            "candidatePath": "Problem.v",
                            "purpose": "semantic-equivalence",
                            "candidateSha256": rejected_candidate,
                            "candidateBytes": len(rejected_problem),
                            "requestedTimeoutSeconds": 5,
                        }
                        (rejected_root / "request.json").write_text(
                            json.dumps(rejected_request), encoding="utf-8"
                        )
                        rejected_audit = {
                            "passed": False,
                            "scannedFiles": [
                                "proof-stage/proof-agent/rounds/01/interactive-diagnostics/01/checked-workspace/Problem.v"
                            ],
                            "findings": [{
                                "path": "Problem.v",
                                "line": 1,
                                "token": "Load",
                                "excerpt": 'Load "forbidden.vo".',
                            }],
                        }
                        (rejected_root / "audit.json").write_text(
                            json.dumps(rejected_audit), encoding="utf-8"
                        )
                        (rejected_root / "feedback.txt").write_text(
                            f"candidate {rejected_candidate}: checker was not executed",
                            encoding="utf-8",
                        )
                        rejected_source_audits.append({
                            "requestOrdinal": 1,
                            "mode": "problem",
                            "candidatePath": "Problem.v",
                            "purpose": "semantic-equivalence",
                            "candidateSha256": rejected_candidate,
                            "requestedTimeoutSeconds": 5,
                            "problem": artifact_binding(rejected_root / "Problem.v"),
                            "request": artifact_binding(rejected_root / "request.json"),
                            "audit": artifact_binding(rejected_root / "audit.json"),
                            "feedback": artifact_binding(rejected_root / "feedback.txt"),
                        })
                    accepted_source_audits = [] if "nodiagnostic" in log_dir.name else [{
                        "requestOrdinal": accepted_request_ordinal,
                        "sequence": 1,
                        "mode": diagnostic_mode,
                        "candidatePath": diagnostic_candidate_path,
                        "purpose": diagnostic_purpose,
                        "candidateSha256": invocation["candidateSha256"],
                        "requestedTimeoutSeconds": 5,
                        "candidate": artifact_binding(
                            diagnostic_checked / diagnostic_candidate_path
                            if diagnostic_mode == "module"
                            else diagnostic_checked / "Problem.v"
                        ),
                        "audit": artifact_binding(diagnostic_root / "audit.json"),
                    }]
                    if second_diagnostic_root is not None:
                        accepted_source_audits.append({
                            "requestOrdinal": accepted_request_ordinal + 1,
                            "sequence": 2,
                            "mode": "problem",
                            "candidatePath": "Problem.v",
                            "purpose": "assembly",
                            "candidateSha256": second_invocation["candidateSha256"],
                            "requestedTimeoutSeconds": 5,
                            "candidate": artifact_binding(
                                second_diagnostic_root / "checked-workspace/Problem.v"
                            ),
                            "audit": artifact_binding(
                                second_diagnostic_root / "audit.json"
                            ),
                        })
                        diagnostic_requests_seen = 2
                        diagnostic_reserved_timeout = 10
                    proof_round = {
                        "round": 1,
                        "workspaceGeneration": 1,
                        "sessionGeneration": 1,
                        "sessionRestarted": False,
                        "checkpointTransition": "newWorkspaceInitial",
                        "sessionId": "019f8c94-8ab5-7762-8e73-ee0f4f3af9de",
                        "contextManifestSha256": context_sha256,
                        "authorityClosurePath": "proof-stage/proof-agent/rounds/01/checked-workspace/authority-closure.txt",
                        "authorityClosureSha256": hashlib.sha256(closure.read_bytes()).hexdigest(),
                        "authorityClosureBytes": closure.stat().st_size,
                        "candidateProblemSha256": hashlib.sha256(
                            final_problem.encode()
                        ).hexdigest(),
                        "candidateProblemCompilePassed": not any(
                            marker in log_dir.name
                            for marker in (
                                "nodiagnostic",
                                "elapsed124warning",
                                "modulediagnostic",
                            )
                        ),
                        "candidateHasFinalTheorem": True,
                        "candidateClaim": "equivalence",
                        "activeProblemCompileCheckpointSha256": hashlib.sha256(initial_problem).hexdigest(),
                        "updatedProblemCompileCheckpointSha256": (
                            None
                            if any(
                                marker in log_dir.name
                                for marker in (
                                    "nodiagnostic",
                                    "elapsed124warning",
                                    "modulediagnostic",
                                )
                            )
                            else candidate_sha256
                        ),
                        "compileCheckpointRestored": False,
                        "diagnosticCheckerInvocations": (
                            [] if "nodiagnostic" in log_dir.name
                            else reported_invocations
                        ),
                        "diagnosticRequestsSeen": diagnostic_requests_seen,
                        "diagnosticRequestedTimeoutSecondsReserved": diagnostic_reserved_timeout,
                        "diagnosticAcceptedCount": len(accepted_source_audits),
                        "diagnosticRejectedSourceAuditCount": len(rejected_source_audits),
                        "diagnosticOtherRejectedRequestCount": diagnostic_other_rejected,
                        "diagnosticAcceptedSourceAudits": accepted_source_audits,
                        "diagnosticRejectedSourceAudits": rejected_source_audits,
                        "scratchFileCount": 0,
                        "scratchBytes": 0,
                        "proofCheckExitCode": 0,
                        "proofCheckElapsedMs": 1,
                        "proofCheckTimeoutSeconds": int(option("--proof-check-timeout-seconds")),
                        "proofCheckTimedOut": False,
                        "exitCode": 0,
                        "success": not module_diagnostic,
                        "audit": {"passed": True, "scannedFiles": [], "findings": []},
                    }
                    if "nodiagnostic" not in log_dir.name:
                        proof_round["diagnosticCheckerTelemetryPath"] = (
                            "proof-stage/proof-agent/rounds/01/interactive-diagnostics.json"
                        )
                    if "dirtyaudit" in log_dir.name:
                        proof_round["audit"]["findings"] = ["synthetic unsafe file"]
                    if "finalelapsedwarning" in log_dir.name:
                        proof_round["proofCheckElapsedMs"] = (
                            int(option("--proof-check-timeout-seconds")) * 1000
                            + 6_001
                        )
                    if module_diagnostic:
                        proof_round["proofCheckExitCode"] = None
                        proof_round["proofCheckElapsedMs"] = None
                        proof_round.pop("proofCheckTimeoutSeconds")
                    if "elapsed124warning" in log_dir.name:
                        proof_round["success"] = False
                        proof_round["candidateClaim"] = None
                        proof_round["proofCheckExitCode"] = None
                        proof_round["proofCheckElapsedMs"] = None
                        proof_round.pop("proofCheckTimeoutSeconds")
                    report = {
                        "rounds": [],
                        "outcome": "outcome_unconditional",
                        "reason": "fake proof complete",
                        "counterexample": None,
                        "logDir": str(log_dir.resolve()),
                        "proof": {
                            "sqlEnvironment": {
                                "defaultCollation": option("--sql-default-collation"),
                                "characterClassification": option("--sql-character-classification"),
                                "localeProvider": option("--sql-locale-provider"),
                                "serverEncoding": option("--sql-server-encoding"),
                            },
                            "verificationMode": option("--verification-mode").replace("-", "_"),
                            "backendStatus": "proof_complete",
                            "certification": "OUTCOME-UNCONDITIONAL",
                            "proofSearchTimedOut": False,
                            "usageComplete": "partialusage" not in log_dir.name,
                            "proofWorkspace": {
                                "problemPath": "proof-stage/formal-sql/Problem.v",
                                "rocqCheckScriptPath": "proof-stage/formal-sql/run-rocq-check.sh",
                                "dockerAgentScriptPath": "proof-stage/proof-agent/trusted-launcher/run-proof-agent-docker.sh",
                            },
                            "proofAgentConfiguration": {
                                "enabled": True,
                                "command": __PROOF_AGENT_COMMAND__,
                                "resumeCommand": __PROOF_AGENT_RESUME_COMMAND__,
                                "timeoutSeconds": int(option("--proof-agent-timeout-seconds")),
                                "trustedCheckTimeoutSeconds": int(option("--proof-check-timeout-seconds")),
                                "memoryLimitMib": int(option("--proof-agent-memory-limit-mib")),
                                "writableStorageLimitBytes": int(option("--proof-agent-storage-limit-mib")) * 1024 * 1024,
                                "writableStoragePolicy": "single_kernel_tmpfs_all_agent_writes_with_read_only_root_v1",
                                "sessionRestartAfterFailedRounds": 16,
                                "sessionHomePolicy": "isolated_per_generation",
                                "diagnosticTransport": "host_unix_broker",
                                "diagnosticCachePolicy": "preflight_built_source_digest_bound_host_only",
                                "diagnosticTimeoutPolicy": "positive_request_bounded_only_by_current_invocation_deadline",
                                "diagnosticBudgetPolicy": "bounded_by_invocation_deadline",
                                "diagnosticCheckerParallelismMax": 1,
                                "diagnosticCheckerSchedulingPolicy": "sequential_host_broker_invocation_deadline_bounded",
                                "compileCheckpointPolicy": "latest_host_problem_compile_pass_over_immutable_checked_module_cache_digest_deduplicated",
                                "scratchPersistencePolicy": "regular_nonsymlink_allowed_extension_round_replacement_drop_other_extensions_with_warning_exact_digest_checked_promotion",
                                "scratchAllowedExtensions": ["v", "md", "txt"],
                                "trustedCheckerEnvironmentPolicy": __TRUSTED_CHECKER_ENVIRONMENT_POLICY__,
                                "proofAgentLauncherEnvironmentPolicy": __PROOF_AGENT_LAUNCHER_ENVIRONMENT_POLICY__,
                                "diagnosticCacheManifestPath": "proof-stage/proof-agent/trusted-diagnostic-cache/SHA256SUMS",
                                "diagnosticCacheManifestSha256": hashlib.sha256(cache_manifest.encode()).hexdigest(),
                                "dockerImage": option("--proof-docker-image"),
                                "staticPromptAndPrimerBytes": 100,
                                "trustedEnvironmentPreflight": preflight_invocation,
                                "context": context_report,
                            },
                            "proofAgent": proof_round,
                            "proofAgentRounds": [proof_round],
                        },
                    }
                    if usage is not None:
                        report["llmUsage"] = usage
                    if "forgedenvpolicy" in log_dir.name:
                        report["proof"]["proofAgentConfiguration"]["trustedCheckerEnvironmentPolicy"]["fixedVariables"][0] = "PATH=/tmp/hostile"
                    if module_diagnostic:
                        report["outcome"] = "equivalence_verification_incomplete"
                        report["reason"] = "fake module diagnostic completed"
                        report["proof"]["backendStatus"] = "proof_agent_run_completed"
                        report["proof"]["certification"] = None
                    if "elapsed124warning" in log_dir.name:
                        report["outcome"] = "equivalence_verification_incomplete"
                        report["reason"] = "fake diagnostic timeout completed"
                        report["proof"]["backendStatus"] = "proof_agent_run_completed"
                        report["proof"]["certification"] = None
                    (log_dir / "report.json").write_text(
                        json.dumps(report), encoding="utf-8"
                    )
                    if "mutategoalcontext" in log_dir.name:
                        (proof_root / "Goal.v").write_text(
                            "Definition forged_goal : False.\\n", encoding="utf-8"
                        )
                    elif "mutatecontextmanifest" in log_dir.name:
                        (proof_root / "context-manifest.json").write_bytes(
                            context_manifest_bytes + b" "
                        )
                    elif "symlinkcontextancestor" in log_dir.name:
                        moved = log_dir / "moved-formal-sql"
                        proof_root.rename(moved)
                        proof_root.symlink_to(moved, target_is_directory=True)
                    elif "mutateloweringgoal" in log_dir.name:
                        lowering["goalModule"]["rocqModule"] = (
                            "Definition forged_lowering_goal : False.\\n"
                        )
                        (log_dir / "proof-stage/formal-sql-lowering.json").write_text(
                            json.dumps(lowering, indent=2) + "\\n", encoding="utf-8"
                        )
                    elif "tamperrejectedaudit" in log_dir.name:
                        rejected_feedback = round_root / "rejected-diagnostic-source-audits/01/feedback.txt"
                        rejected_feedback.write_text("tampered", encoding="utf-8")
                    elif "mutateinput" in log_dir.name:
                        source_path.write_text("SELECT 999;\\n", encoding="utf-8")
                    elif "mutatesolver" in log_dir.name:
                        solver_path = Path(__file__)
                        solver_path.chmod(0o700)
                        solver_path.write_text(
                            solver_path.read_text(encoding="utf-8") + "# drift\\n",
                            encoding="utf-8",
                        )
                    elif "mutatestack" in log_dir.name:
                        runtime = Path(option("--proof-rocq-opam-switch")) / "_opam/lib/rocq-runtime/synthetic_plugin.cmxs"
                        runtime.chmod(0o644)
                        runtime.write_bytes(b"mutated runtime plugin")
                    elif "mutatematerializedchecker" in log_dir.name:
                        (trusted_launcher_root / "run-trusted-rocq-check.sh").write_bytes(
                            b"#!/bin/sh\\nexit 0\\n# stale embedded checker\\n"
                        )
                    elif "mutatematerializedlauncher" in log_dir.name:
                        (trusted_launcher_root / "run-proof-agent-docker.sh").write_bytes(
                            b"#!/bin/sh\\nexit 0\\n# stale embedded launcher\\n"
                        )
                    elif "mutateworker" in log_dir.name:
                        worker = Path(option("--proof-rocq-opam-switch")) / "_opam/lib/rocq-runtime/rocqworker"
                        worker.chmod(0o755)
                        worker.write_bytes(worker.read_bytes() + b"worker drift")
                    elif "mutatechecker" in log_dir.name:
                        checker = Path(option("--proof-rocq-opam-switch")) / "_opam/bin/rocqchk"
                        checker.chmod(0o755)
                        checker.write_bytes(checker.read_bytes() + b"checker drift")
                    elif "mutatecodex" in log_dir.name:
                        codex = Path(os.environ["PATH"].split(os.pathsep)[0]) / "codex"
                        codex.write_text(codex.read_text(encoding="utf-8") + "# drift\\n", encoding="utf-8")
                    elif "tamperfrontend" in log_dir.name:
                        manifest = log_dir.parents[1] / "frontend-stack-manifest.json"
                        manifest.write_text(
                            manifest.read_text(encoding="utf-8") + " ", encoding="utf-8"
                        )
                """
        )
        fake_solver_source = (
            fake_solver_source.replace(
                "__PROOF_AGENT_COMMAND__", repr(DEFAULT_PROOF_AGENT_COMMAND)
            )
            .replace(
                "__PROOF_AGENT_RESUME_COMMAND__",
                repr(DEFAULT_PROOF_AGENT_RESUME_COMMAND),
            )
            .replace(
                "__TRUSTED_CHECKER_ENVIRONMENT_POLICY__",
                repr(TRUSTED_CHECKER_ENVIRONMENT_POLICY),
            )
            .replace(
                "__PROOF_AGENT_LAUNCHER_ENVIRONMENT_POLICY__",
                repr(PROOF_AGENT_LAUNCHER_ENVIRONMENT_POLICY),
            )
            .replace(
                "__RUN_ROCQ_CHECK_SCRIPT__",
                repr(
                    (
                        RUNNER.parents[2]
                        / "crates/logos-solver/scripts/run-rocq-check.sh"
                    ).read_bytes()
                ),
            )
            .replace(
                "__RUN_PROOF_AGENT_DOCKER_SCRIPT__",
                repr(
                    (
                        RUNNER.parents[2]
                        / "crates/logos-solver/scripts/run-proof-agent-docker.sh"
                    ).read_bytes()
                ),
            )
            .replace(
                "__RUN_TRUSTED_ROCQ_CHECK_SCRIPT__",
                repr(
                    (
                        RUNNER.parents[2]
                        / "crates/logos-solver/scripts/run-trusted-rocq-check.sh"
                    ).read_bytes()
                ),
            )
        )
        self.fake_solver.write_text(
            fake_solver_source,
            encoding="utf-8",
        )
        self.fake_solver.chmod(0o755)

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def write_fake_docker(self, image_character: str) -> None:
        image_id = "sha256:" + image_character * 64
        self.fake_docker.write_text(
            textwrap.dedent(
                f"""\
                #!/usr/bin/env python3
                import json
                import sys

                if sys.argv[1:3] != ["image", "inspect"] or len(sys.argv) != 4:
                    raise SystemExit(2)
                print(json.dumps([{{
                    "Id": {image_id!r},
                    "RepoDigests": ["logos-solver@{image_id}"],
                    "Created": "2026-07-23T00:00:00Z",
                    "Os": "linux",
                    "Architecture": "amd64"
                }}]))
                """
            ),
            encoding="utf-8",
        )
        self.fake_docker.chmod(0o755)

    def make_case(
        self,
        cohort: str,
        directory: str,
        benchmark: str,
        source_case: str,
        flat_case_id: str,
    ) -> Path:
        case_dir = self.input_root / cohort / directory
        case_dir.mkdir(parents=True)
        for name, text in (
            ("schema.sql", "CREATE TABLE t (a INTEGER);\n"),
            ("sql1.sql", "SELECT a FROM t;\n"),
            ("sql2.sql", "SELECT a FROM t;\n"),
        ):
            (case_dir / name).write_text(text, encoding="utf-8")
        metadata = {
            "flatCaseId": flat_case_id,
            "sourceBenchmark": benchmark,
            "sourceCase": source_case,
        }
        (case_dir / "metadata.json").write_text(json.dumps(metadata), encoding="utf-8")
        return case_dir

    def copy_rbot_authority_input(self, runner: dict, name: str) -> Path:
        root = self.root / name
        destination = root / "nonwetune-flat"
        destination.mkdir(parents=True)
        source = runner["DEFAULT_INPUT_ROOT"] / "nonwetune-flat"
        for case_dir in sorted(source.glob("rbot-*")):
            shutil.copytree(case_dir, destination / case_dir.name)
        return root

    def test_rbot_authority_binds_all_59_native_cases_and_exact_selection(self) -> None:
        runner = runpy.run_path(str(RUNNER), run_name="runner_rbot_authority_test")
        root = self.copy_rbot_authority_input(runner, "rbot-authority-pass")
        cases = runner["discover_cases"](root)
        record = runner["validate_rbot_input_authority"](
            root, cases, cases, require_exact_selection=True
        )
        self.assertEqual(record["manifestSha256"], runner["FROZEN_RBOT_MANIFEST_SHA256"])
        self.assertEqual(record["caseCount"], 59)
        self.assertEqual(record["selectedRbotCaseCount"], 59)
        self.assertEqual(
            record["schemas"]["dsb"]["sha256"],
            runner["FROZEN_RBOT_SCHEMA_SHA256"]["dsb"],
        )
        filtered = runner["validate_rbot_input_authority"](
            root, cases, cases[:1], require_exact_selection=False
        )
        self.assertEqual(filtered["caseCount"], 59)
        self.assertEqual(filtered["selectedRbotCaseCount"], 1)
        with self.assertRaisesRegex(
            runner["RunnerError"], "must contain exactly 59 cases"
        ):
            runner["validate_rbot_input_authority"](
                root, cases, cases[:1], require_exact_selection=True
            )

    def test_rbot_authority_rejects_stale_borrowed_and_fabricated_inputs(self) -> None:
        runner = runpy.run_path(str(RUNNER), run_name="runner_rbot_mutation_test")
        runner_error = runner["RunnerError"]

        def mutate_schema(root: Path) -> None:
            path = root / "nonwetune-flat/rbot-dsb__query001/schema.sql"
            path.write_text(path.read_text() + "-- forged\n", encoding="utf-8")

        def co_mutate_source_and_metadata(root: Path) -> None:
            case = root / "nonwetune-flat/rbot-dsb__query001"
            source = case / "sql1.sql"
            source.write_text(source.read_text() + "-- forged\n", encoding="utf-8")
            digest = hashlib.sha256(source.read_bytes()).hexdigest()
            metadata_path = case / "metadata.json"
            metadata = json.loads(metadata_path.read_text())
            binding = metadata["materializationContract"]["inputs"]["source"]
            binding["inputSha256"] = digest
            binding["outputSha256"] = digest
            metadata["calciteAuthorityInputs"]["source"]["sha256"] = digest
            metadata_path.write_text(json.dumps(metadata), encoding="utf-8")

        def borrow_cross_case_source_identity(root: Path) -> None:
            first = root / "nonwetune-flat/rbot-dsb__query001/metadata.json"
            second = root / "nonwetune-flat/rbot-dsb__query010/metadata.json"
            first_metadata = json.loads(first.read_text())
            second_metadata = json.loads(second.read_text())
            second_metadata["source"] = first_metadata["source"]
            second.write_text(json.dumps(second_metadata), encoding="utf-8")

        def fabricate_repairs(root: Path) -> None:
            path = root / "nonwetune-flat/rbot-dsb__query075/metadata.json"
            metadata = json.loads(path.read_text())
            metadata["materializationContract"]["semanticPreservation"][
                "repairs"
            ] = ["unchecked"]
            path.write_text(json.dumps(metadata), encoding="utf-8")

        def borrow_materialization_binding(root: Path) -> None:
            first = root / "nonwetune-flat/rbot-dsb__query001/metadata.json"
            second = root / "nonwetune-flat/rbot-dsb__query010/metadata.json"
            first_metadata = json.loads(first.read_text())
            second_metadata = json.loads(second.read_text())
            first_metadata["materializationContract"]["inputs"]["source"] = (
                second_metadata["materializationContract"]["inputs"]["source"]
            )
            first.write_text(json.dumps(first_metadata), encoding="utf-8")

        def forge_calcite_authority(root: Path) -> None:
            path = root / "nonwetune-flat/rbot-dsb__query001/metadata.json"
            metadata = json.loads(path.read_text())
            metadata["calciteAuthorityInputs"]["source"]["sha256"] = "0" * 64
            path.write_text(json.dumps(metadata), encoding="utf-8")

        def downgrade_to_legacy_shape(root: Path) -> None:
            path = root / "nonwetune-flat/rbot-dsb__query001/metadata.json"
            metadata = json.loads(path.read_text())
            metadata["profile"] = "sqlsolver"
            metadata.pop("materializationContract")
            metadata.pop("calciteAuthorityInputs")
            metadata["integrityContract"] = {
                "authoritativeForLogos": True,
                "silentDrops": 0,
                "sources": [{"kind": "parser_facing_ddl", "path": "schema.sql"}],
                "sqlsolverDdlComplete": True,
                "sqlsolverDdlLimitation": None,
            }
            path.write_text(json.dumps(metadata), encoding="utf-8")

        def omit_case(root: Path) -> None:
            shutil.rmtree(root / "nonwetune-flat/rbot-tpch__query9")

        def add_case(root: Path) -> None:
            source = root / "nonwetune-flat/rbot-tpch__query9"
            shutil.copytree(source, root / "nonwetune-flat/rbot-forged__query9")

        for index, mutation in enumerate(
            (
                mutate_schema,
                co_mutate_source_and_metadata,
                borrow_cross_case_source_identity,
                fabricate_repairs,
                borrow_materialization_binding,
                forge_calcite_authority,
                downgrade_to_legacy_shape,
                omit_case,
                add_case,
            )
        ):
            with self.subTest(mutation=mutation.__name__):
                root = self.copy_rbot_authority_input(
                    runner, f"rbot-authority-mutation-{index}"
                )
                cases = runner["discover_cases"](root)
                mutation(root)
                with self.assertRaises(runner_error):
                    current_cases = runner["discover_cases"](root)
                    runner["validate_rbot_input_authority"](
                        root,
                        current_cases,
                        current_cases,
                        require_exact_selection=False,
                    )

    def invoke(
        self, *args: str, timeout: float = 60
    ) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [sys.executable, str(RUNNER), *args],
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout,
            check=False,
            env=self.environment,
        )

    def common_args(self, run_dir: Path) -> list[str]:
        return [
            "--input-root",
            str(self.input_root),
            "--run-dir",
            str(run_dir),
            "--solver-bin",
            str(self.fake_solver),
            "--no-build",
            "--no-rocq-build",
            "--proof-rocq-opam-switch",
            str(self.fake_rocq_switch),
            "--trusted-rocq-cache-dir",
            str(self.root / "trusted-rocq-cache"),
            "--postgres-url",
            "postgresql://logos@127.0.0.1:55489/postgres",
        ]

    def mark_interrupted(self, run_dir: Path) -> dict:
        path = run_dir / "runner-summary.json"
        summary = json.loads(path.read_text())
        summary["status"] = "interrupted"
        path.write_text(json.dumps(summary), encoding="utf-8")
        return summary

    def invocation_case_ids(self) -> list[str]:
        paths = sorted(self.root.rglob("invocations.log"))
        return [
            case_id
            for path in paths
            for case_id in path.read_text().splitlines()
        ]

    def usage(self, input_tokens: int, cached_tokens: int, output_tokens: int) -> dict:
        return {
            "model": "gpt-5.6-sol",
            "inputTokens": input_tokens,
            "cachedInputTokens": cached_tokens,
            "outputTokens": output_tokens,
            "totalTokens": input_tokens + output_tokens,
            "estimatedCostUsd": (
                (input_tokens - cached_tokens) * 5.0
                + cached_tokens * 0.5
                + output_tokens * 30.0
            )
            / 1_000_000,
        }

    def test_exact_case_and_benchmark_selection(self) -> None:
        self.make_case("cohort", "one", "bench-a", "one", "bench-a__one")
        self.make_case("cohort", "two", "bench-b", "two", "bench-b__two")

        listed = self.invoke(
            "--input-root",
            str(self.input_root),
            "--benchmark",
            "bench-b",
            "--list",
        )
        self.assertEqual(listed.returncode, 0, listed.stderr)
        self.assertIn("cohort__bench-b__two", listed.stdout)
        self.assertNotIn("bench-a__one", listed.stdout)

        run_dir = self.root / "single-run"
        completed = self.invoke(
            *self.common_args(run_dir),
            "--case",
            "bench-a__one",
        )
        self.assertEqual(completed.returncode, 0, completed.stderr)
        summary = json.loads((run_dir / "runner-summary.json").read_text())
        self.assertEqual(summary["counts"]["selected"], 1)
        self.assertEqual(summary["results"][0]["caseId"], "cohort__bench-a__one")
        self.assertEqual(summary["results"][0]["outcome"], "outcome_unconditional")
        self.assertEqual(
            summary["results"][0]["llmUsage"],
            {
                "model": "gpt-5.6-sol",
                "inputTokens": 100,
                "cachedInputTokens": 20,
                "outputTokens": 10,
                "totalTokens": 110,
                "estimatedCostUsd": 0.00071,
            },
        )
        self.assertTrue(summary["usageComplete"])
        usage_path = run_dir / "cases/cohort__bench-a__one/usage.json"
        self.assertEqual(
            json.loads(usage_path.read_text()), summary["results"][0]["llmUsage"]
        )
        case_output = run_dir / "cases/cohort__bench-a__one"
        report = json.loads((case_output / "report.json").read_text())
        context = report["proof"]["proofAgentConfiguration"]["context"]
        lowering = json.loads(
            (case_output / "proof-stage/formal-sql-lowering.json").read_text()
        )
        self.assertEqual(
            context["problemModuleBytes"],
            len(lowering["proofModule"]["rocqModule"].encode()),
        )
        self.assertNotEqual(
            context["problemModuleBytes"],
            (case_output / "proof-stage/formal-sql/Problem.v").stat().st_size,
        )

        argv_path = run_dir / "cases/cohort__bench-a__one/argv.json"
        solver_argv = json.loads(argv_path.read_text())
        self.assertEqual(solver_argv.count("--schema"), 1)
        self.assertEqual(
            solver_argv[solver_argv.index("--schema") + 1],
            str(self.input_root / "cohort/one/schema.sql"),
        )
        solver_environment = json.loads(
            (run_dir / "cases/cohort__bench-a__one/environment.json").read_text()
        )
        for hostile in (
            *TRUSTED_LAUNCH_EXCLUDED_VARIABLES,
            "JAVA_TOOL_OPTIONS",
            "_JAVA_OPTIONS",
            "JDK_JAVA_OPTIONS",
            "CLASSPATH",
            "MAVEN_OPTS",
            "MAVEN_ARGS",
            "PYTHONHOME",
            "PYTHONPATH",
            "VIRTUAL_ENV",
            "OPENAI_API_KEY",
            "CODEX_API_KEY",
            "OPENAI_BASE_URL",
            "CODEX_BASE_URL",
            "OPENAI_API_BASE",
            "AZURE_OPENAI_ENDPOINT",
            "HTTP_PROXY",
            "NO_PROXY",
            "LOGOS_CALCITE_IR_COMMAND",
        ):
            self.assertNotIn(hostile, solver_environment)
        self.assertFalse(
            any(name.startswith("BASH_FUNC_") for name in solver_environment)
        )
        self.assertFalse(self.bash_env_marker.exists())
        self.assertEqual(solver_environment["HOME"], "/nonexistent")
        self.assertEqual(solver_environment["TMPDIR"], "/tmp")
        self.assertEqual(solver_environment["LC_ALL"], "C")
        self.assertEqual(solver_environment["LANG"], "C")
        self.assertEqual(solver_environment["TZ"], "UTC")
        self.assertRegex(solver_environment["LOGOS_CASE_SUPERVISOR_PID"], r"^[1-9][0-9]*$")
        self.assertNotEqual(solver_environment["LOGOS_CASE_SUPERVISOR_PID"], "999")
        self.assertEqual(solver_environment["MAVEN_VERSION"], "3.9.11")
        self.assertEqual(
            Path(solver_environment["LOGOS_CALCITE_RUNTIME_CLASSPATH_FILE"]).resolve(),
            (
                RUNNER.parents[2]
                / "frontend/calcite-wrapper/target/logos-runtime-classpath.txt"
            ).resolve(),
        )
        self.assertEqual(
            solver_environment["CODEX_HOME"],
            solver_environment["LOGOS_SOLVER_CODEX_HOME"],
        )
        self.assertEqual(
            solver_environment["LOGOS_SOLVER_CODEX_CONFIG"],
            str(Path(solver_environment["CODEX_HOME"]) / "config.toml"),
        )
        self.assertTrue(solver_environment["runtimeAuthPresent"])
        self.assertTrue(solver_environment["runtimeCredentialsPresent"])
        self.assertFalse(Path(solver_environment["CODEX_HOME"]).exists())
        self.assertNotIn("resume", solver_argv)
        self.assertNotIn("--proof-agent-resume-command", solver_argv)
        self.assertIn("--force-llm-assessment", solver_argv)
        frontend_index = solver_argv.index("--calcite-ir-command")
        self.assertEqual(
            solver_argv[frontend_index + 1],
            summary["configuration"]["frontendStack"]["canonicalCommand"],
        )
        timeout_index = solver_argv.index("--proof-agent-timeout-seconds")
        self.assertEqual(solver_argv[timeout_index + 1], "3900")
        self.assertFalse(
            any(value.startswith("--proof-agent-catalog-guidance") for value in solver_argv)
        )
        memory_index = solver_argv.index("--proof-agent-memory-limit-mib")
        self.assertEqual(solver_argv[memory_index + 1], "6144")
        storage_index = solver_argv.index("--proof-agent-storage-limit-mib")
        self.assertEqual(solver_argv[storage_index + 1], "2048")
        statement_index = solver_argv.index("--statement-timeout-ms")
        self.assertEqual(solver_argv[statement_index + 1], "600000")
        counterexample_round_index = solver_argv.index("--max-counterexample-rounds")
        self.assertEqual(solver_argv[counterexample_round_index + 1], "3")
        check_timeout_index = solver_argv.index("--proof-check-timeout-seconds")
        self.assertEqual(solver_argv[check_timeout_index + 1], "420")
        image_index = solver_argv.index("--proof-docker-image")
        self.assertEqual(solver_argv[image_index + 1], "sha256:" + "d" * 64)
        self.assertEqual(summary["model"], "gpt-5.6-sol")
        self.assertEqual(summary["reasoningEffort"], "medium")
        self.assertNotIn("proofAgentCatalogGuidanceEnabled", summary)
        self.assertEqual(summary["solverArgs"], [])
        self.assertEqual(summary["effectiveSolverArgs"], ["--force-llm-assessment"])
        self.assertEqual(
            Path(summary["configuration"]["solverBin"]).resolve(),
            (run_dir / "runtime/logos-solver").resolve(),
        )
        authority_index = solver_argv.index("--logos-repo-root")
        authority = summary["configuration"]["rocqAuthoritySnapshot"]
        authority_root = (RUNNER.parents[3] / authority["root"]).resolve()
        self.assertEqual(
            Path(solver_argv[authority_index + 1]).resolve(),
            authority_root.resolve(),
        )
        self.assertEqual(
            summary["configuration"]["solverBinarySnapshotPolicy"],
            "run-private-immutable-copy-v1",
        )
        isolation = summary["configuration"]["caseProcessIsolation"]
        self.assertEqual(
            isolation["policy"],
            "user-pid-namespace-pid1-kernel-reclamation-v1",
        )
        self.assertTrue(isolation["preflightValidated"])
        self.assertEqual(
            isolation["hostSupervisorPidChannel"]["environmentVariable"],
            "LOGOS_CASE_SUPERVISOR_PID",
        )
        for binding_name in ("bootstrap", "supervisor"):
            binding = isolation[binding_name]
            snapshot = run_dir / binding["relativePath"]
            self.assertTrue(snapshot.is_file())
            self.assertFalse(snapshot.is_symlink())
            self.assertEqual(stat.S_IMODE(snapshot.stat().st_mode), 0o555)
            self.assertEqual(hashlib.sha256(snapshot.read_bytes()).hexdigest(), binding["sha256"])
        isolation_digest = hashlib.sha256(
            (
                json.dumps(
                    isolation,
                    sort_keys=True,
                    separators=(",", ":"),
                    ensure_ascii=False,
                )
                + "\n"
            ).encode("utf-8")
        ).hexdigest()
        self.assertEqual(
            summary["integrityVerification"]["caseProcessIsolationSha256"],
            isolation_digest,
        )
        self.assertEqual(
            summary["results"][0]["effectiveConfiguration"][
                "caseProcessIsolation"
            ],
            isolation,
        )
        self.assertEqual(
            authority["policy"],
            "content-addressed-forced-source-build-closure-v3",
        )
        self.assertEqual(
            (RUNNER.parents[3] / authority["root"]).resolve(),
            authority_root.resolve(),
        )
        self.assertEqual(
            summary["results"][0]["effectiveConfiguration"][
                "rocqAuthoritySnapshotManifestSha256"
            ],
            authority["manifestSha256"],
        )
        self.assertEqual(
            summary["configuration"]["frameworkSourceTreeDigestPolicy"],
            "required",
        )
        self.assertEqual(
            summary["configuration"]["sqlEnvironment"],
            {
                "timeZone": "UTC",
                "defaultCollation": "C",
                "characterClassification": "C",
                "localeProvider": "libc",
                "serverEncoding": "UTF8",
            },
        )
        proof_agent = summary["configuration"]["proofAgent"]
        self.assertNotIn("catalogGuidanceEnabled", proof_agent)
        self.assertEqual(proof_agent["reasoningEffort"], "medium")
        self.assertEqual(proof_agent["resourcePolicy"]["memoryLimitMiB"], 6144)
        self.assertIsNone(proof_agent["resourcePolicy"]["cpuLimit"])
        self.assertEqual(proof_agent["trustedCheckTimeoutSeconds"], 420)
        self.assertEqual(
            proof_agent["trustedCheckerEnvironmentPolicy"],
            TRUSTED_CHECKER_ENVIRONMENT_POLICY,
        )
        self.assertEqual(
            proof_agent["proofAgentLauncherEnvironmentPolicy"],
            PROOF_AGENT_LAUNCHER_ENVIRONMENT_POLICY,
        )
        self.assertEqual(proof_agent["dockerImage"]["reference"], "logos-solver:latest")
        self.assertEqual(
            proof_agent["dockerImage"]["effectiveReference"],
            "sha256:" + "d" * 64,
        )
        self.assertEqual(summary["proofDockerImageRequested"], "logos-solver:latest")
        self.assertEqual(summary["proofDockerImageEffective"], "sha256:" + "d" * 64)
        source_tree = summary["configuration"]["frameworkSourceTree"]
        source_manifest = Path(source_tree["manifestPath"])
        self.assertTrue(source_manifest.is_file())
        self.assertEqual(
            hashlib.sha256(source_manifest.read_bytes()).hexdigest(),
            source_tree["manifestSha256"],
        )
        self.assertRegex(source_tree["logosHead"], r"^[0-9a-f]{40}$")
        self.assertRegex(source_tree["formalSqlHead"], r"^[0-9a-f]{40}$")
        self.assertEqual(
            source_tree["sourceTreeDigestHelper"],
            {
                "path": "scripts/logos_source_tree_digest.py",
                "sha256": (
                    "a2b651399e0103adac71a11822803979c535ac8bc897479a54c4366bd5e44b81"
                ),
                "bytes": 8009,
                "executionPolicy": "exact-bytes-loaded-before-module-execution-v1",
            },
        )
        source_document = json.loads(source_manifest.read_text(encoding="utf-8"))
        self.assertIn(
            "vendor/FormalSQL",
            {
                submodule["path"]
                for submodule in source_document["repository"]["submodules"]
            },
        )
        configuration = summary["configuration"]
        self.assertEqual(summary["statementTimeoutSeconds"], 600)
        self.assertEqual(configuration["statementTimeoutSeconds"], 600)
        self.assertEqual(summary["maxCounterexampleRounds"], 3)
        self.assertEqual(configuration["maxCounterexampleRounds"], 3)
        self.assertEqual(summary["proofAgentStorageLimitMiB"], 2048)
        self.assertEqual(
            proof_agent["resourcePolicy"]["storageLimitMiB"], 2048
        )
        self.assertEqual(
            summary["results"][0]["effectiveConfiguration"][
                "statementTimeoutSeconds"
            ],
            600,
        )
        self.assertEqual(
            summary["results"][0]["effectiveConfiguration"][
                "proofAgentWritableStorageLimitBytes"
            ],
            2048 * 1024 * 1024,
        )
        self.assertEqual(
            summary["results"][0]["effectiveConfiguration"][
                "maxCounterexampleRounds"
            ],
            3,
        )

        self.assertEqual(
            configuration["solverBinary"]["sha256"],
            hashlib.sha256(self.fake_solver.read_bytes()).hexdigest(),
        )
        input_manifest = configuration["inputManifest"]
        self.assertEqual(input_manifest["algorithm"], "logos-input-manifest-v2")
        self.assertEqual(input_manifest["manifestSchemaVersion"], 2)
        self.assertTrue(Path(input_manifest["path"]).is_file())
        self.assertEqual(
            hashlib.sha256(Path(input_manifest["path"]).read_bytes()).hexdigest(),
            input_manifest["sha256"],
        )
        manifest_document = json.loads(Path(input_manifest["path"]).read_text())
        self.assertEqual(manifest_document["schemaVersion"], 2)
        self.assertIn("metadataSha256", manifest_document["cases"][0])
        self.assertIn("metadata", summary["results"][0]["inputFiles"])
        trusted_stack = configuration["trustedStack"]
        self.assertGreater(trusted_stack["sourceObjectPairCount"], 0)
        self.assertEqual(trusted_stack["rocqStdlibObjectCount"], 1)
        self.assertEqual(trusted_stack["rocqRuntimeComponentCount"], 1)
        self.assertEqual(trusted_stack["rocqRuntimeConfigurationCount"], 2)
        self.assertEqual(trusted_stack["trustedExecutableCount"], 5)
        self.assertGreater(trusted_stack["dynamicRuntimeFileCount"], 0)
        self.assertEqual(trusted_stack["trustedHostToolCount"], 26)
        self.assertGreater(trusted_stack["trustedHostDynamicRuntimeFileCount"], 0)
        self.assertEqual(
            trusted_stack["trustedInspectionEnvironmentPolicy"],
            "clear-then-fixed-allowlist-v1",
        )
        self.assertEqual(trusted_stack["manifestSchemaVersion"], 7)
        self.assertEqual(
            trusted_stack["dynamicLinkingAlgorithm"],
            "logos-elf-runtime-closure-v2",
        )
        self.assertEqual(trusted_stack["trustedInspectionEnvironmentVariableCount"], 3)
        self.assertEqual(trusted_stack["lddRuntimeLoaderCandidateCount"], 3)
        self.assertEqual(trusted_stack["lddRuntimeLoaderPresentCandidateCount"], 2)
        self.assertEqual(trusted_stack["lddRuntimeLoaderAbsentCandidateCount"], 1)
        self.assertEqual(trusted_stack["systemResolverConfigurationPathCount"], 2)
        self.assertEqual(
            trusted_stack["systemResolverConfigurationPresentPathCount"], 1
        )
        self.assertEqual(trusted_stack["systemResolverConfigurationAbsentPathCount"], 1)
        self.assertEqual(
            trusted_stack["systemIdentityConfigurationAlgorithm"],
            "logos-system-identity-config-closure-v1",
        )
        self.assertEqual(trusted_stack["systemIdentityConfigurationPathCount"], 2)
        self.assertEqual(
            trusted_stack["systemIdentityConfigurationPresentPathCount"], 2
        )
        self.assertEqual(trusted_stack["systemIdentityConfigurationAbsentPathCount"], 0)
        self.assertEqual(
            hashlib.sha256(
                Path(trusted_stack["manifestPath"]).read_bytes()
            ).hexdigest(),
            trusted_stack["manifestSha256"],
        )
        trusted_document = json.loads(
            Path(trusted_stack["manifestPath"]).read_text(encoding="utf-8")
        )
        self.assertEqual(trusted_document["schemaVersion"], 7)
        trusted_script_paths = [
            row["path"] for row in trusted_document["trustedScripts"]
        ]
        self.assertEqual(trusted_script_paths, sorted(trusted_script_paths))
        self.assertEqual(
            trusted_document["algorithm"], "logos-trusted-proof-stack-manifest-v7"
        )
        self.assertEqual(
            set(trusted_document["executables"]),
            {"rocq", "rocqchk", "rocqworker", "rocqnative", "bwrap"},
        )
        self.assertEqual(
            trusted_document["executables"]["bwrap"]["selectedPath"],
            str(
                (
                    RUNNER.parents[3]
                    / summary["configuration"]["rocqRuntimeSnapshot"]["root"]
                    / "_opam/bin/bwrap"
                ).resolve()
            ),
        )
        self.assertEqual(
            trusted_document["executables"]["bwrap"]["selectionPolicy"],
            "exact-content-addressed-switch-path-v1",
        )
        self.assertEqual(
            trusted_document["executables"]["bwrap"][
                "runtimeSnapshotManifestSha256"
            ],
            summary["configuration"]["rocqRuntimeSnapshot"]["manifestSha256"],
        )
        self.assertEqual(
            [row["name"] for row in trusted_document["dynamicLinking"]["consumers"]],
            ["rocq", "rocqchk", "rocqworker", "rocqnative", "bwrap"],
        )
        self.assertEqual(
            trusted_stack["rocqWorkerExecutable"],
            trusted_document["executables"]["rocqworker"],
        )
        self.assertEqual(
            trusted_stack["rocqCheckExecutable"],
            trusted_document["executables"]["rocqchk"],
        )
        self.assertEqual(
            [row["name"] for row in trusted_document["trustedHostTools"]["tools"]],
            [
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
                "mv",
                "readlink",
                "stat",
                "id",
                "flock",
            ],
        )
        host_tools = trusted_document["trustedHostTools"]
        ldd_tool = next(row for row in host_tools["tools"] if row["name"] == "ldd")
        self.assertEqual(
            ldd_tool["sha256"],
            "ab2b0110ee2b8725a08deec886d57d84a37c31d1225aceb7321faf1b583c46f1",
        )
        self.assertFalse(
            host_tools["inspectionEnvironment"]["parentEnvironmentInherited"]
        )
        self.assertEqual(host_tools["inspectionEnvironment"]["workingDirectory"], "/")
        self.assertEqual(
            host_tools["inspectionEnvironment"]["allowedVariables"],
            [
                {"name": "LANG", "value": "C"},
                {"name": "LC_ALL", "value": "C"},
                {"name": "PATH", "value": "/usr/bin:/bin"},
            ],
        )
        ldd_candidates = {
            row["selectedPath"]: row
            for row in host_tools["lddRuntimeLoaders"]["candidates"]
        }
        self.assertEqual(
            ldd_candidates["/lib/ld-linux.so.2"]["sha256"],
            "8bfac642322e3e03bbf5cb7f8ffed50ee8a8119f0ce7d9da9dd54cb961436abf",
        )
        self.assertEqual(ldd_candidates["/libx32/ld-linux-x32.so.2"]["state"], "absent")
        resolver_paths = {
            row["selectedPath"]: row
            for row in host_tools["systemResolverConfiguration"]["paths"]
        }
        self.assertEqual(resolver_paths["/etc/ld.so.cache"]["state"], "present")
        self.assertEqual(resolver_paths["/etc/ld.so.preload"]["state"], "absent")
        identity = host_tools["systemIdentityConfiguration"]
        self.assertEqual(
            [row["path"] for row in identity["paths"]],
            ["/etc/nsswitch.conf", "/etc/passwd"],
        )
        self.assertTrue(all(row["present"] for row in identity["paths"]))
        frontend_stack = configuration["frontendStack"]
        self.assertEqual(frontend_stack["manifestSchemaVersion"], 2)
        self.assertEqual(
            frontend_stack["algorithm"], "logos-sql-frontend-stack-manifest-v2"
        )
        self.assertEqual(frontend_stack["sourceSqlTransport"], "exact-input-bytes-v1")
        self.assertEqual(frontend_stack["normalizationLayer"], "none")
        self.assertGreater(frontend_stack["calciteClassCount"], 0)
        self.assertGreater(frontend_stack["dependencyCount"], 0)
        self.assertEqual(frontend_stack["launchToolCount"], 8)
        self.assertEqual(
            hashlib.sha256(
                Path(frontend_stack["manifestPath"]).read_bytes()
            ).hexdigest(),
            frontend_stack["manifestSha256"],
        )
        frontend_document = json.loads(
            Path(frontend_stack["manifestPath"]).read_text(encoding="utf-8")
        )
        self.assertEqual(
            frontend_document["launchEnvironment"],
            FRONTEND_LAUNCH_ENVIRONMENT_POLICY,
        )
        self.assertEqual(frontend_document["launchTools"]["toolCount"], 8)
        self.assertEqual(
            [row["name"] for row in frontend_document["launchTools"]["tools"]],
            ["bash", "sh", "dirname", "readlink", "uname", "mkdir", "curl", "tar"],
        )
        self.assertEqual(
            frontend_document["launchTools"]["shellExecutable"], "/usr/bin/bash"
        )
        self.assertEqual(
            frontend_document["launchTools"]["shellArguments"],
            ["--noprofile", "--norc", "-c"],
        )
        self.assertEqual(
            frontend_document["maven"]["settings"]["path"],
            "/nonexistent/.m2/settings.xml",
        )
        codex_provider = configuration["codexProvider"]
        self.assertEqual(codex_provider["model"], "gpt-5.6-sol")
        self.assertEqual(codex_provider["reasoningEffort"], "medium")
        self.assertEqual(
            solver_environment["runtimeConfigSha256"],
            codex_provider["configSha256"],
        )
        self.assertEqual(
            solver_environment["PATH"], codex_provider["solverPath"]["value"]
        )
        self.assertEqual(
            codex_provider["commandEnvironmentPolicy"],
            COMMAND_PROVIDER_ENVIRONMENT_POLICY,
        )
        self.assertEqual(
            configuration["frontendLaunchEnvironmentPolicy"],
            FRONTEND_LAUNCH_ENVIRONMENT_POLICY,
        )
        self.assertEqual(
            configuration["commandProviderEnvironmentPolicy"],
            COMMAND_PROVIDER_ENVIRONMENT_POLICY,
        )
        solver_policy = configuration["solverLaunchEnvironmentPolicy"]
        self.assertTrue(solver_policy["inheritedEnvironmentCleared"])
        self.assertEqual(solver_policy["hostEnvironmentAllowlist"], [])
        self.assertEqual(
            solver_policy["fixedVariables"][0],
            f"PATH={codex_provider['solverPath']['value']}",
        )
        self.assertEqual(
            solver_policy["explicitlyExcludedVariables"],
            SOLVER_LAUNCH_EXCLUDED_VARIABLES,
        )
        self.assertEqual(
            solver_policy["codexInvocationPath"],
            codex_provider["hostCodexInvocationPath"],
        )
        solver_environment_names = set(solver_environment) - {
            "runtimeConfigSha256",
            "runtimeAuthPresent",
            "runtimeCredentialsPresent",
        }
        self.assertEqual(
            solver_environment_names,
            set(configuration["solverEnvironment"]["variableNames"]),
        )
        self.assertEqual(
            configuration["solverEnvironment"]["normalization"],
            "isolated-codex-runtime-home-symbolic-v1",
        )
        sanitized_config = Path(codex_provider["configPath"]).read_text()
        self.assertNotIn("test-secret", sanitized_config)
        self.assertNotIn("unrelated", sanitized_config)
        self.assertEqual(
            codex_provider["commands"]["counterexample"],
            DEFAULT_COUNTEREXAMPLE_COMMAND,
        )
        self.assertEqual(
            codex_provider["commands"]["counterexampleResume"],
            DEFAULT_COUNTEREXAMPLE_RESUME_COMMAND,
        )
        postgres_profile = configuration["postgresServerProfile"]
        self.assertTrue(postgres_profile["configured"])
        self.assertEqual(
            postgres_profile["profile"],
            {
                "serverVersion": "17.4",
                "serverVersionNum": "170004",
                "databaseCollation": "C",
                "databaseCharacterClassification": "C",
                "localeProvider": "libc",
                "serverEncoding": "UTF8",
                "timeZone": "UTC",
                "maxConnections": "96",
            },
        )
        result = summary["results"][0]
        self.assertEqual(
            result["inputFiles"]["source"]["sha256"],
            hashlib.sha256(
                (self.input_root / "cohort/one/sql1.sql").read_bytes()
            ).hexdigest(),
        )
        self.assertTrue(result["reportEvidence"]["present"])
        self.assertEqual(
            result["reportEvidence"]["sha256"],
            hashlib.sha256(
                (run_dir / "cases/cohort__bench-a__one/report.json").read_bytes()
            ).hexdigest(),
        )
        effective = result["effectiveConfiguration"]
        self.assertEqual(effective["terminationGraceSeconds"], 10.0)
        self.assertEqual(effective["proofAgentTotalTimeoutSeconds"], 3900)
        self.assertEqual(
            effective["proofAgentSessionRestartAfterFailedRounds"], 16
        )
        self.assertEqual(
            effective["proofAgentDiagnosticBudgetPolicy"],
            "bounded_by_invocation_deadline",
        )
        self.assertEqual(
            effective["proofAgentDiagnosticCheckerSchedulingPolicy"],
            "sequential_host_broker_invocation_deadline_bounded",
        )
        self.assertEqual(
            effective["proofAgentCompileCheckpointPolicy"],
            "latest_host_problem_compile_pass_over_immutable_checked_module_cache_digest_deduplicated",
        )
        self.assertEqual(
            effective["proofAgentScratchPersistencePolicy"],
            "regular_nonsymlink_allowed_extension_round_replacement_drop_other_extensions_with_warning_exact_digest_checked_promotion",
        )
        self.assertEqual(
            effective["resourcePolicy"],
            {"memoryLimitMiB": 6144, "storageLimitMiB": 2048, "cpuLimit": None},
        )
        self.assertEqual(
            effective["postgresUrl"],
            {
                "configured": True,
                "sha256": hashlib.sha256(
                    b"postgresql://logos@127.0.0.1:55489/postgres"
                ).hexdigest(),
            },
        )
        self.assertEqual(
            effective["frontendStackManifestSha256"],
            frontend_stack["manifestSha256"],
        )
        self.assertEqual(
            effective["codexProviderManifestSha256"],
            codex_provider["manifestSha256"],
        )
        self.assertEqual(
            effective["postgresServerProfileSha256"],
            postgres_profile["manifestSha256"],
        )
        metrics = result["proofMetrics"]
        self.assertEqual(metrics["proofRoundCount"], 1)
        self.assertEqual(metrics["diagnosticInvocationCount"], 1)
        self.assertEqual(metrics["diagnosticElapsedMs"], 1)
        self.assertEqual(metrics["diagnosticRequestCount"], 1)
        self.assertEqual(metrics["diagnosticRequestedTimeoutSecondsReserved"], 5)
        self.assertEqual(metrics["diagnosticAcceptedRequestCount"], 1)
        self.assertEqual(metrics["diagnosticRejectedSourceAuditCount"], 0)
        self.assertEqual(metrics["diagnosticOtherRejectedRequestCount"], 0)
        self.assertEqual(metrics["diagnosticAcceptedAuditArtifactCount"], 1)
        self.assertEqual(metrics["diagnosticRejectedSourceAuditArtifactCount"], 0)
        self.assertEqual(metrics["diagnosticPreservedArtifactCount"], 1)
        self.assertEqual(metrics["requestedTimeoutSeconds"], [5])
        self.assertEqual(metrics["effectiveTimeoutSeconds"], [5])
        self.assertEqual(metrics["preflightInvocationCount"], 1)
        self.assertEqual(metrics["preflightElapsedMs"], 1)
        self.assertEqual(metrics["initialProblemCompileElapsedMs"], 1)
        self.assertEqual(metrics["initialProblemCompileTimeoutSeconds"], 420)
        self.assertEqual(metrics["finalProofCheckInvocationCount"], 1)
        self.assertEqual(metrics["finalProofCheckElapsedTotalMs"], 1)
        self.assertEqual(metrics["checkerInvocationCount"], 4)
        self.assertEqual(metrics["checkerElapsedMs"], 4)
        self.assertEqual(metrics["finalProofCheckElapsedMs"], 1)
        self.assertTrue(metrics["proofSource"]["present"])
        self.assertTrue(summary["integrityVerification"]["verified"])

    def test_fresh_runs_reuse_content_addressed_rocq_runtime_and_authority(self) -> None:
        self.make_case("cohort", "cache", "bench-a", "cache", "bench-a__cache")
        first_run = self.root / "cache-run-one"
        second_run = self.root / "cache-run-two"
        first = self.invoke(*self.common_args(first_run))
        self.assertEqual(first.returncode, 0, first.stderr)
        first_summary = json.loads((first_run / "runner-summary.json").read_text())
        runtime = first_summary["configuration"]["rocqRuntimeSnapshot"]
        authority = first_summary["configuration"]["rocqAuthoritySnapshot"]
        build_log = (
            Path(authority["root"]).parent.parent
            / "trusted-rocq-authority-build.log"
        )
        build_log_mtime = build_log.stat().st_mtime_ns

        second = self.invoke(*self.common_args(second_run))
        self.assertEqual(second.returncode, 0, second.stderr)
        second_summary = json.loads((second_run / "runner-summary.json").read_text())
        self.assertEqual(
            second_summary["configuration"]["rocqRuntimeSnapshot"]["root"],
            runtime["root"],
        )
        self.assertEqual(
            second_summary["configuration"]["rocqAuthoritySnapshot"]["root"],
            authority["root"],
        )
        self.assertEqual(build_log.stat().st_mtime_ns, build_log_mtime)
        self.assertTrue((first_run / "trusted-rocq-runtime-ref.json").is_file())
        self.assertTrue((second_run / "trusted-rocq-authority-ref.json").is_file())

    def test_execution_requires_postgres_before_creating_run_directory(self) -> None:
        self.make_case("cohort", "one", "bench-a", "one", "bench-a__one")
        run_dir = self.root / "missing-postgres"
        args = self.common_args(run_dir)
        postgres_index = args.index("--postgres-url")
        del args[postgres_index : postgres_index + 2]
        inherited = self.environment.get("LOGOS_POSTGRES_URL")
        inherited_present = "LOGOS_POSTGRES_URL" in self.environment
        # An explicit empty value must shadow the repository-local .env value so
        # this subprocess genuinely exercises the missing-PostgreSQL preflight.
        self.environment["LOGOS_POSTGRES_URL"] = ""
        try:
            completed = self.invoke(*args)
        finally:
            if inherited_present:
                self.environment["LOGOS_POSTGRES_URL"] = inherited
            else:
                self.environment.pop("LOGOS_POSTGRES_URL", None)
        self.assertNotEqual(completed.returncode, 0)
        self.assertIn("PostgreSQL validation is required", completed.stderr)
        self.assertFalse(run_dir.exists())

    def test_codex_treatment_is_validated_before_creating_run_directory(self) -> None:
        self.make_case("cohort", "one", "bench-a", "one", "bench-a__one")
        config = self.fake_codex_home / "config.toml"
        config.write_text(
            config.read_text(encoding="utf-8").replace(
                'model_reasoning_effort = "medium"',
                'model_reasoning_effort = "low"',
            ),
            encoding="utf-8",
        )
        run_dir = self.root / "wrong-codex-treatment"
        completed = self.invoke(*self.common_args(run_dir))
        self.assertNotEqual(completed.returncode, 0)
        self.assertIn("frozen model/provider treatment", completed.stderr)
        self.assertFalse(run_dir.exists())

    def test_codex_cli_is_validated_before_creating_run_directory(self) -> None:
        self.make_case("cohort", "one", "bench-a", "one", "bench-a__one")
        self.fake_codex.unlink()
        run_dir = self.root / "missing-codex-cli"
        original_path = self.environment["PATH"]
        self.environment["PATH"] = str(self.fake_bin)
        try:
            completed = self.invoke(*self.common_args(run_dir))
        finally:
            self.environment["PATH"] = original_path
        self.assertNotEqual(completed.returncode, 0)
        self.assertIn("host Codex CLI is unavailable", completed.stderr)
        self.assertFalse(run_dir.exists())

    def test_postgres_profile_is_validated_before_creating_run_directory(self) -> None:
        self.make_case("cohort", "one", "bench-a", "one", "bench-a__one")
        self.fake_psql.write_text("#!/bin/sh\nexit 2\n", encoding="utf-8")
        run_dir = self.root / "invalid-postgres-profile"
        completed = self.invoke(*self.common_args(run_dir))
        self.assertNotEqual(completed.returncode, 0)
        self.assertIn("PostgreSQL server-profile probe", completed.stderr)
        self.assertFalse(run_dir.exists())

    def test_catalog_guidance_option_is_not_exposed(self) -> None:
        namespace = runpy.run_path(str(RUNNER))
        parser = namespace["argument_parser"]()
        with self.assertRaises(SystemExit):
            parser.parse_args(["--proof-agent-catalog-guidance", "off"])

    def test_framework_source_drift_option_is_explicit_and_default_strict(self) -> None:
        namespace = runpy.run_path(str(RUNNER))
        parser = namespace["argument_parser"]()
        self.assertFalse(parser.parse_args([]).allow_framework_source_drift)
        self.assertTrue(
            parser.parse_args(
                ["--allow-framework-source-drift"]
            ).allow_framework_source_drift
        )

    def test_framework_source_precedes_build_and_binds_loaded_runner_bytes(self) -> None:
        namespace = runpy.run_path(str(RUNNER), run_name="runner_launch_binding_test")
        manifest = namespace["build_source_tree_manifest"](namespace["LOGOS_ROOT"])
        manifest_path = self.root / "launch-framework-source-tree-manifest.json"
        manifest_path.write_bytes(namespace["source_tree_manifest_bytes"](manifest))
        digest = namespace["source_tree_manifest_sha256"](manifest)
        summary = namespace["framework_source_tree_summary"](
            manifest, manifest_path, digest
        )
        self.assertEqual(
            summary["runnerScriptSha256"],
            namespace["RUNNER_LAUNCH_RECORD"]["sha256"],
        )

        tampered = json.loads(json.dumps(manifest))
        runner_entry = next(
            entry
            for entry in tampered["repository"]["entries"]
            if entry.get("path") == "benchmarks/scripts/run-logos"
        )
        runner_entry["sha256"] = "0" * 64
        with self.assertRaisesRegex(
            namespace["RunnerError"], "runner differs from the launch runner bytes"
        ):
            namespace["framework_source_tree_summary"](
                tampered, manifest_path, "0" * 64
            )

        module = ast.parse(RUNNER.read_text(encoding="utf-8"))
        main_node = next(
            node
            for node in module.body
            if isinstance(node, ast.FunctionDef) and node.name == "main"
        )
        call_lines = {
            call.func.id: call.lineno
            for call in ast.walk(main_node)
            if isinstance(call, ast.Call)
            and isinstance(call.func, ast.Name)
            and call.func.id
            in {
                "required_postgres_url",
                "validate_frozen_full_launch_request",
                "capture_codex_provider_environment",
                "postgres_profile_document",
                "prepare_run_dir",
                "framework_source_tree_record",
                "build_solver",
                "prepare_frontend_stack",
            }
        }
        for preflight in (
            "required_postgres_url",
            "validate_frozen_full_launch_request",
            "capture_codex_provider_environment",
            "postgres_profile_document",
        ):
            self.assertLess(call_lines[preflight], call_lines["prepare_run_dir"])
            self.assertLess(call_lines[preflight], call_lines["build_solver"])
        self.assertLess(
            call_lines["framework_source_tree_record"], call_lines["build_solver"]
        )
        self.assertLess(
            call_lines["framework_source_tree_record"],
            call_lines["prepare_frontend_stack"],
        )

    def test_record_only_resume_rejects_mutable_digest_helper_before_execution(
        self,
    ) -> None:
        sandbox_root = self.root / "digest-helper-bootstrap/Logos"
        copied_runner = sandbox_root / "benchmarks/scripts/run-logos"
        copied_helper = sandbox_root / "scripts/logos_source_tree_digest.py"
        copied_env = sandbox_root / "scripts/logos_env.py"
        copied_runner.parent.mkdir(parents=True)
        copied_helper.parent.mkdir(parents=True)
        shutil.copy2(RUNNER, copied_runner)
        source_helper = RUNNER.parents[2] / "scripts/logos_source_tree_digest.py"
        shutil.copy2(source_helper, copied_helper)
        shutil.copy2(RUNNER.parents[2] / "scripts/logos_env.py", copied_env)
        safe = subprocess.run(
            [sys.executable, str(copied_runner), "--help"],
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
        self.assertEqual(safe.returncode, 0, safe.stderr)

        execution_marker = self.root / "mutable-helper-executed"
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
            [
                sys.executable,
                str(copied_runner),
                "--resume",
                "--allow-framework-source-drift",
                "--run-dir",
                str(self.root / "nonexistent-run"),
            ],
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
        self.assertNotEqual(rejected.returncode, 0)
        self.assertIn(
            "source-tree digest helper differs from the immutable runner binding",
            rejected.stderr,
        )
        self.assertFalse(execution_marker.exists())

        namespace = runpy.run_path(str(RUNNER), run_name="helper_manifest_binding_test")
        with self.assertRaisesRegex(
            namespace["RunnerError"], "source digest helper binding drifted"
        ):
            namespace["validate_framework_source_tree_helper_binding"](
                {
                    "repository": {
                        "entries": [
                            {
                                "path": "scripts/logos_source_tree_digest.py",
                                "kind": "file",
                                "sha256": "0" * 64,
                                "bytes": 8009,
                            }
                        ]
                    }
                }
            )
        for entries in ([], [namespace["source_tree_digest_helper_record"]()] * 2):
            with self.assertRaisesRegex(
                namespace["RunnerError"], "source digest helper exactly once"
            ):
                namespace["validate_framework_source_tree_helper_binding"](
                    {"repository": {"entries": entries}}
                )

    def test_runner_rejects_mutable_environment_helper_before_execution(self) -> None:
        sandbox_root = self.root / "environment-helper-bootstrap/Logos"
        copied_runner = sandbox_root / "benchmarks/scripts/run-logos"
        scripts = sandbox_root / "scripts"
        scripts.mkdir(parents=True)
        copied_runner.parent.mkdir(parents=True)
        copied_env = scripts / "logos_env.py"
        shutil.copy2(RUNNER, copied_runner)
        shutil.copy2(
            RUNNER.parents[2] / "scripts/logos_source_tree_digest.py",
            scripts / "logos_source_tree_digest.py",
        )
        shutil.copy2(RUNNER.parents[2] / "scripts/logos_env.py", copied_env)
        marker = self.root / "mutable-runner-environment-helper-executed"
        payload = copied_env.read_bytes()
        prefix = (
            "from pathlib import Path\n"
            f"Path({str(marker)!r}).write_text('unsafe', encoding='utf-8')\n"
        ).encode()
        copied_env.write_bytes(
            prefix + b"#" + b"x" * (len(payload) - len(prefix) - 2) + b"\n"
        )
        rejected = subprocess.run(
            [sys.executable, str(copied_runner), "--help"],
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
        self.assertNotEqual(rejected.returncode, 0)
        self.assertIn(
            "environment helper differs from the immutable runner binding",
            rejected.stderr,
        )
        self.assertFalse(marker.exists())

    def test_solver_binary_is_pinned_to_run_private_snapshot(self) -> None:
        namespace = runpy.run_path(str(RUNNER))
        source = self.root / "source-logos-solver"
        original = b"#!/bin/sh\nexit 0\n"
        source.write_bytes(original)
        source.chmod(0o755)
        run_dir = self.root / "pin-run"
        run_dir.mkdir()

        pinned = namespace["pin_solver_binary"](source, run_dir, resume=False)
        self.assertEqual(pinned, (run_dir / "runtime/logos-solver").resolve())
        self.assertEqual(pinned.read_bytes(), original)
        self.assertEqual(stat.S_IMODE(pinned.stat().st_mode), 0o555)

        source.write_bytes(b"#!/bin/sh\nexit 99\n")
        self.assertEqual(pinned.read_bytes(), original)
        self.assertEqual(
            namespace["pin_solver_binary"](source, run_dir, resume=True), pinned
        )

    def test_record_only_source_policy_reports_drift_without_accepting_tampering(
        self,
    ) -> None:
        namespace = runpy.run_path(str(RUNNER))
        manifest = namespace["build_source_tree_manifest"](namespace["LOGOS_ROOT"])
        manifest_path = self.root / "framework-source-tree-manifest.json"
        manifest_path.write_bytes(namespace["source_tree_manifest_bytes"](manifest))
        starting_digest = namespace["source_tree_manifest_sha256"](manifest)
        changed = json.loads(json.dumps(manifest))
        changed["repository"]["dirty"] = not changed["repository"]["dirty"]
        config = mock.Mock(
            framework_source_tree={
                "manifestPath": str(manifest_path),
                "manifestSha256": starting_digest,
            },
            allow_framework_source_drift=True,
        )
        verify = namespace["verify_framework_source_tree_integrity"]
        with mock.patch.dict(
            verify.__globals__,
            {"build_source_tree_manifest": lambda _root: changed},
        ):
            record = verify(config)
        self.assertTrue(record["frameworkSourceTreeDriftDetected"])
        self.assertEqual(
            record["frameworkSourceTreeDigestPolicy"], "record-only"
        )
        self.assertEqual(
            record["frameworkSourceTreeManifestSha256"], starting_digest
        )
        self.assertNotEqual(
            record["frameworkSourceTreeObservedManifestSha256"], starting_digest
        )

        with mock.patch.dict(
            verify.__globals__,
            {
                "build_source_tree_manifest": mock.Mock(
                    side_effect=FileNotFoundError("concurrent source removal")
                )
            },
        ):
            observation_failure = verify(config)
        self.assertTrue(
            observation_failure["frameworkSourceTreeDriftDetected"]
        )
        self.assertIn(
            "concurrent source removal",
            observation_failure["frameworkSourceTreeObservationError"],
        )

        config.allow_framework_source_drift = False
        with mock.patch.dict(
            verify.__globals__,
            {"build_source_tree_manifest": lambda _root: changed},
        ), self.assertRaisesRegex(
            namespace["RunnerError"], "framework source tree changed"
        ):
            verify(config)

        manifest_path.write_bytes(b"{}\n")
        config.allow_framework_source_drift = True
        with self.assertRaisesRegex(
            namespace["RunnerError"], "preserved framework source-tree manifest"
        ):
            verify(config)

    def test_workspace_artifact_paths_are_relative_to_logos_root(self) -> None:
        namespace = runpy.run_path(str(RUNNER))
        logos_root = RUNNER.parents[2]
        value = namespace["workspace_display_path"](
            logos_root / "var/logos-solver/example/cases/case/report.json"
        )
        self.assertEqual(
            value,
            "var/logos-solver/example/cases/case/report.json",
        )

    def test_default_input_manifest_is_metadata_bound(self) -> None:
        namespace = runpy.run_path(str(RUNNER))
        self.assertEqual(namespace["DEFAULT_INPUT_ROOT"].name, "logos")
        self.assertEqual(namespace["LEGACY_FROZEN_INPUT_ROOT"].name, "sqlsolver")
        case_dir = self.make_case(
            "cohort", "manifest", "bench-a", "manifest", "bench-a__manifest"
        )
        cases = namespace["discover_cases"](self.input_root)
        manifest = namespace["build_input_manifest"](cases)
        self.assertEqual(manifest["schemaVersion"], 2)
        self.assertEqual(manifest["algorithm"], "logos-input-manifest-v2")
        self.assertEqual(manifest["caseCount"], 1)
        self.assertEqual(
            manifest["cases"][0]["metadataSha256"],
            hashlib.sha256((case_dir / "metadata.json").read_bytes()).hexdigest(),
        )
        original_digest = namespace["input_manifest_sha256"](manifest)
        metadata = json.loads((case_dir / "metadata.json").read_text())
        metadata["manifestMutation"] = True
        (case_dir / "metadata.json").write_text(json.dumps(metadata), encoding="utf-8")
        mutated = namespace["build_input_manifest"](
            namespace["discover_cases"](self.input_root)
        )
        self.assertNotEqual(
            namespace["input_manifest_sha256"](mutated), original_digest
        )
        (case_dir / "metadata.json").unlink()
        with self.assertRaises(namespace["RunnerError"]):
            namespace["build_input_manifest"](cases)

    def test_legacy_frozen_input_manifest_remains_sqlsolver_v1_and_fails_closed_on_drift(
        self,
    ) -> None:
        namespace = runpy.run_path(str(RUNNER))
        legacy_root = namespace["LEGACY_FROZEN_INPUT_ROOT"]
        cases = namespace["discover_cases"](legacy_root)
        manifest = namespace["build_input_manifest"](cases, legacy=True)
        self.assertEqual(manifest["caseCount"], 389)
        self.assertEqual(manifest["schemaVersion"], 1)
        self.assertEqual(
            manifest["algorithm"], "logos-frozen-input-manifest-v1"
        )
        self.assertTrue(
            all("metadataSha256" not in row for row in manifest["cases"])
        )
        digest = namespace["input_manifest_sha256"](manifest)
        if digest == namespace["FROZEN_INPUT_MANIFEST_SHA256"]:
            record, files = namespace["input_manifest_record"](
                self.root / "legacy-manifest",
                cases,
                cases,
                frozen=True,
                resume=False,
            )
            self.assertTrue(record["frozenVerified"])
            self.assertTrue(record["frozenSemanticAuthorityVerified"])
            self.assertEqual(
                record["semanticAuthoritySha256"],
                namespace["FROZEN_SEMANTIC_INPUT_AUTHORITY_SHA256"],
            )
            self.assertTrue(all("metadata" in value for value in files.values()))
            self.assertEqual(record["manifestSchemaVersion"], 1)
        else:
            with self.assertRaises(namespace["RunnerError"]):
                namespace["input_manifest_record"](
                    self.root / "legacy-manifest",
                    cases,
                    cases,
                    frozen=True,
                    resume=False,
                )
        self.assertEqual(
            namespace["FROZEN_INPUT_MANIFEST_SHA256"],
            "d34443e927c3e68a28c6d216334c624e1b50d0b37d60c9c937d21202b9f3162e",
        )
        self.assertEqual(
            namespace["FROZEN_SEMANTIC_INPUT_AUTHORITY_SHA256"],
            "8ee79987c8f77cb88bc637196931010b7da88e8f4fb3303392527f1e156587a4",
        )
        self.assertEqual(
            hashlib.sha256(namespace["FROZEN_SCOPE"].read_bytes()).hexdigest(),
            namespace["FROZEN_SCOPE_SHA256"],
        )
        cohort = json.loads(namespace["FROZEN_COHORT"].read_text())
        self.assertEqual(cohort["caseCount"], 389)
        self.assertEqual(len(cohort["cases"]), 389)
        self.assertEqual(len(set(cohort["cases"])), 389)
        self.assertEqual(
            hashlib.sha256(namespace["FROZEN_COHORT"].read_bytes()).hexdigest(),
            namespace["FROZEN_COHORT_SHA256"],
        )

    def test_forged_or_incomplete_proof_telemetry_fails_closed(self) -> None:
        for name in (
            "forgedtelemetry",
            "nodiagnostic",
            "dirtyaudit",
            "rejectedinvoked",
            "forgedenvpolicy",
            "forgedwitnesscache",
            "legacyschema",
            "scratchcheckpoint",
            "duplicatecheckpoint",
        ):
            self.make_case("cohort", name, "bench-a", name, f"bench-a__{name}")
        run_dir = self.root / "bad-proof-telemetry"
        completed = self.invoke(*self.common_args(run_dir), "--jobs", "9")
        self.assertEqual(completed.returncode, 0, completed.stderr)
        summary = json.loads((run_dir / "runner-summary.json").read_text())
        self.assertEqual(summary["status"], "complete")
        self.assertEqual(summary["counts"]["failed"], 9)
        by_case = {row["caseId"]: row for row in summary["results"]}
        self.assertIn(
            "telemetry differs",
            by_case["cohort__bench-a__forgedtelemetry"]["reportCoherenceError"],
        )
        self.assertIn(
            "complete proof-agent",
            by_case["cohort__bench-a__nodiagnostic"]["reportCoherenceError"],
        )
        self.assertIn(
            "deterministic audit",
            by_case["cohort__bench-a__dirtyaudit"]["reportCoherenceError"],
        )
        self.assertIn(
            "identity or ordinal",
            by_case["cohort__bench-a__rejectedinvoked"]["reportCoherenceError"],
        )
        self.assertIn(
            "trustedCheckerEnvironmentPolicy",
            by_case["cohort__bench-a__forgedenvpolicy"]["reportCoherenceError"],
        )
        self.assertIn(
            "cache-bound generated source differs from trusted cache",
            by_case["cohort__bench-a__forgedwitnesscache"][
                "reportCoherenceError"
            ],
        )
        self.assertIn(
            "schemaVersion 2",
            by_case["cohort__bench-a__legacyschema"]["reportCoherenceError"],
        )
        self.assertIn(
            "compile/checkpoint status",
            by_case["cohort__bench-a__scratchcheckpoint"]["reportCoherenceError"],
        )
        self.assertIn(
            "duplicates the active compile checkpoint",
            by_case["cohort__bench-a__duplicatecheckpoint"][
                "reportCoherenceError"
            ],
        )

    def test_diagnostic_elapsed_overrun_is_a_structured_warning(self) -> None:
        self.make_case(
            "cohort",
            "elapsedwarning",
            "bench-a",
            "elapsedwarning",
            "bench-a__elapsedwarning",
        )
        self.make_case(
            "cohort",
            "elapsedmarginboundary",
            "bench-a",
            "elapsedmarginboundary",
            "bench-a__elapsedmarginboundary",
        )
        self.make_case(
            "cohort",
            "elapsed124warning",
            "bench-a",
            "elapsed124warning",
            "bench-a__elapsed124warning",
        )
        run_dir = self.root / "diagnostic-elapsed-warning"
        completed = self.invoke(*self.common_args(run_dir), "--jobs", "3")
        self.assertEqual(completed.returncode, 0, completed.stderr)
        summary = json.loads((run_dir / "runner-summary.json").read_text())
        self.assertEqual(summary["counts"]["completed"], 3)
        self.assertEqual(summary["counts"]["failed"], 0)
        by_case = {row["caseId"]: row for row in summary["results"]}

        warning_result = by_case["cohort__bench-a__elapsedwarning"]
        self.assertNotIn("reportCoherenceError", warning_result)
        warning_metrics = warning_result["proofMetrics"]
        self.assertEqual(warning_metrics["diagnosticElapsedMs"], 12_001)
        self.assertEqual(warning_metrics["checkerElapsedMs"], 12_004)
        self.assertEqual(
            warning_metrics["diagnosticElapsedWarnings"],
            [
                {
                    "code": "diagnostic_elapsed_exceeded_timeout_plus_kill_margin",
                    "round": 1,
                    "sequence": 1,
                    "requestedTimeoutSeconds": 5,
                    "effectiveTimeoutSeconds": 5,
                    "elapsedMs": 12_001,
                    "timeoutPlusKillMarginMs": 11_000,
                    "overrunMs": 1_001,
                }
            ],
        )

        boundary_result = by_case["cohort__bench-a__elapsedmarginboundary"]
        self.assertNotIn("reportCoherenceError", boundary_result)
        boundary_metrics = boundary_result["proofMetrics"]
        self.assertEqual(boundary_metrics["diagnosticElapsedMs"], 11_000)
        self.assertNotIn("diagnosticElapsedWarnings", boundary_metrics)

        timeout_result = by_case["cohort__bench-a__elapsed124warning"]
        self.assertNotIn("reportCoherenceError", timeout_result)
        timeout_metrics = timeout_result["proofMetrics"]
        self.assertEqual(
            timeout_metrics["diagnosticElapsedWarnings"],
            warning_metrics["diagnosticElapsedWarnings"],
        )

    def test_backward_wall_clock_diagnostic_is_warning_only(self) -> None:
        self.make_case(
            "cohort",
            "backwardclock",
            "bench-a",
            "backwardclock",
            "bench-a__backwardclock",
        )
        run_dir = self.root / "diagnostic-backward-clock"
        completed = self.invoke(*self.common_args(run_dir))
        self.assertEqual(completed.returncode, 0, completed.stderr)
        summary = json.loads((run_dir / "runner-summary.json").read_text())
        result = summary["results"][0]
        self.assertEqual(result["status"], "completed")
        self.assertNotIn("reportCoherenceError", result)
        metrics = result["proofMetrics"]
        self.assertEqual(metrics["diagnosticInvocationCount"], 2)
        self.assertEqual(
            metrics["diagnosticClockWarnings"],
            [
                {
                    "code": "diagnostic_wall_clock_regressed_or_overlapped",
                    "round": 1,
                    "sequence": 2,
                    "startedAtUnixMs": 900,
                    "priorEstimatedEndUnixMs": 1100,
                    "apparentRegressionMs": 200,
                }
            ],
        )

    def test_module_diagnostic_binds_multifile_cache_and_late_publication(self) -> None:
        for name in (
            "modulediagnostic",
            "modulediagnosticlate",
            "modulediagnosticlate2",
        ):
            self.make_case("cohort", name, "bench-a", name, f"bench-a__{name}")
        run_dir = self.root / "module-diagnostic"
        completed = self.invoke(*self.common_args(run_dir), "--jobs", "2")
        self.assertEqual(completed.returncode, 0, completed.stderr)
        summary = json.loads((run_dir / "runner-summary.json").read_text())
        self.assertEqual(summary["counts"]["completed"], 3)
        self.assertEqual(summary["counts"]["failed"], 0)
        for result in summary["results"]:
            with self.subTest(case=result["caseId"]):
                self.assertEqual(
                    result["outcome"], "equivalence_verification_incomplete"
                )
                self.assertNotIn("reportCoherenceError", result)
                self.assertEqual(result["proofMetrics"]["diagnosticInvocationCount"], 1)
                case_dir = run_dir / "cases" / result["caseId"]
                report = json.loads((case_dir / "report.json").read_text())
                invocation = report["proof"]["proofAgentRounds"][0][
                    "diagnosticCheckerInvocations"
                ][0]
                self.assertEqual(invocation["mode"], "module")
                self.assertEqual(
                    invocation["candidatePath"], "ProofModules/CoreFacts.v"
                )
                self.assertTrue(invocation["compilePassed"])
                self.assertFalse(invocation["problemCompilePassed"])
                self.assertEqual(
                    hashlib.sha256(
                        (
                            case_dir
                            / "proof-stage/formal-sql/ProofModules/CoreFacts.v"
                        ).read_bytes()
                    ).hexdigest(),
                    invocation["candidateSha256"],
                )
                if result["caseId"].endswith("modulediagnosticlate"):
                    self.assertEqual(invocation["exitCode"], 143)
                elif result["caseId"].endswith("modulediagnosticlate2"):
                    self.assertEqual(invocation["exitCode"], 2)

    def test_context_goal_manifest_lowering_and_ancestor_drift_fail_closed(
        self,
    ) -> None:
        names = (
            "mutategoalcontext",
            "mutatecontextmanifest",
            "mutateloweringgoal",
            "symlinkcontextancestor",
        )
        for name in names:
            self.make_case("cohort", name, "bench-a", name, f"bench-a__{name}")
        run_dir = self.root / "context-authority-mutations"
        completed = self.invoke(*self.common_args(run_dir), "--jobs", "4")
        self.assertEqual(completed.returncode, 0, completed.stderr)
        summary = json.loads((run_dir / "runner-summary.json").read_text())
        self.assertEqual(summary["counts"]["failed"], 4)
        for result in summary["results"]:
            with self.subTest(case=result["caseId"]):
                self.assertIn("reportCoherenceError", result)
                self.assertEqual(result["status"], "failed")

    def test_initial_and_preflight_elapsed_overruns_are_warnings(self) -> None:
        for name in (
            "initialelapsedwarning",
            "preflightelapsedwarning",
            "finalelapsedwarning",
        ):
            self.make_case("cohort", name, "bench-a", name, f"bench-a__{name}")
        run_dir = self.root / "trusted-elapsed-warning"
        completed = self.invoke(*self.common_args(run_dir), "--jobs", "2")
        self.assertEqual(completed.returncode, 0, completed.stderr)
        summary = json.loads((run_dir / "runner-summary.json").read_text())
        self.assertEqual(summary["counts"]["completed"], 3)
        self.assertEqual(summary["counts"]["failed"], 0)
        by_case = {row["caseId"]: row for row in summary["results"]}
        expected_phases = {
            "cohort__bench-a__initialelapsedwarning": "initial_problem_compile",
            "cohort__bench-a__preflightelapsedwarning": (
                "trusted_environment_preflight"
            ),
            "cohort__bench-a__finalelapsedwarning": "final_trusted_check",
        }
        for case_id, phase in expected_phases.items():
            warnings = by_case[case_id]["proofMetrics"]["trustedElapsedWarnings"]
            self.assertEqual(len(warnings), 1)
            self.assertEqual(warnings[0]["phase"], phase)
            if phase == "final_trusted_check":
                self.assertEqual(warnings[0]["round"], 1)
            else:
                self.assertEqual(warnings[0]["workspaceGeneration"], 1)
            self.assertEqual(warnings[0]["overrunMs"], 1)

    def test_rejected_diagnostic_audit_is_preserved_without_checker_inflation(
        self,
    ) -> None:
        self.make_case(
            "cohort",
            "rejecteddiagnostic",
            "bench-a",
            "rejecteddiagnostic",
            "bench-a__rejecteddiagnostic",
        )
        run_dir = self.root / "rejected-diagnostic"
        completed = self.invoke(*self.common_args(run_dir))
        self.assertEqual(completed.returncode, 0, completed.stderr)
        result = json.loads((run_dir / "runner-summary.json").read_text())["results"][0]
        self.assertEqual(result["status"], "completed")
        metrics = result["proofMetrics"]
        self.assertEqual(metrics["diagnosticRequestCount"], 3)
        self.assertEqual(metrics["diagnosticRequestedTimeoutSecondsReserved"], 15)
        self.assertEqual(metrics["diagnosticAcceptedRequestCount"], 1)
        self.assertEqual(metrics["diagnosticRejectedSourceAuditCount"], 1)
        self.assertEqual(metrics["diagnosticOtherRejectedRequestCount"], 1)
        self.assertEqual(metrics["diagnosticAcceptedAuditArtifactCount"], 1)
        self.assertEqual(metrics["diagnosticRejectedSourceAuditArtifactCount"], 4)
        self.assertEqual(metrics["diagnosticPreservedArtifactCount"], 5)
        self.assertEqual(metrics["diagnosticInvocationCount"], 1)
        self.assertEqual(metrics["diagnosticElapsedMs"], 1)
        self.assertEqual(metrics["checkerInvocationCount"], 4)
        self.assertEqual(metrics["checkerElapsedMs"], 4)

    def test_rejected_diagnostic_artifact_drift_fails_closed(self) -> None:
        self.make_case(
            "cohort",
            "tamperrejectedaudit",
            "bench-a",
            "tamperrejectedaudit",
            "bench-a__tamperrejectedaudit",
        )
        run_dir = self.root / "tampered-rejected-diagnostic"
        completed = self.invoke(*self.common_args(run_dir))
        self.assertEqual(completed.returncode, 0, completed.stderr)
        result = json.loads((run_dir / "runner-summary.json").read_text())["results"][0]
        self.assertEqual(result["status"], "failed")
        self.assertIn("binding drifted", result["reportCoherenceError"])

    def test_pipeline_short_circuit_solver_args_are_rejected(self) -> None:
        namespace = runpy.run_path(str(RUNNER))
        error = namespace["RunnerError"]
        for value in (
            "--disable-counterexample-search",
            "--disable-proof-agent=true",
            "--transform-only",
            "--typed-witness-empty-audit",
            "--llm-assessment-only",
            "--reuse-llm-assessment",
            "--calcite-ir-command=/tmp/forged-frontend",
            "--max-counterexample-rounds=0",
            "--proposal-resume-command=codex exec resume forged",
            "--help",
            "--version",
            "0",
        ):
            with self.subTest(value=value), self.assertRaises(error):
                namespace["validate_solver_args"]((value,))
        namespace["validate_solver_args"](("--force-llm-assessment",))

    def test_frozen_full_launch_requires_exact_scope_configuration_and_gate(
        self,
    ) -> None:
        namespace = runpy.run_path(str(RUNNER))
        legacy_root = namespace["LEGACY_FROZEN_INPUT_ROOT"]
        cases = namespace["discover_cases"](legacy_root)
        parser = namespace["argument_parser"]()
        bad = parser.parse_args([])
        with self.assertRaises(namespace["RunnerError"]):
            namespace["validate_frozen_full_launch_request"](
                legacy_root, cases, cases, bad
            )
        good = parser.parse_args(
            [
                "--jobs",
                "32",
                "--case-timeout",
                "3600",
                "--postgres-url",
                "postgresql://logos@127.0.0.1:55490/postgres",
                "--cohort16-gate-summary",
                "gate.json",
            ]
        )
        namespace["validate_frozen_full_launch_request"](
            legacy_root, cases, cases, good
        )
        source_drift = parser.parse_args(
            [
                "--jobs",
                "32",
                "--case-timeout",
                "3600",
                "--postgres-url",
                "postgresql://logos@127.0.0.1:55490/postgres",
                "--cohort16-gate-summary",
                "gate.json",
                "--allow-framework-source-drift",
            ]
        )
        with self.assertRaisesRegex(
            namespace["RunnerError"], "framework-source-drift"
        ):
            namespace["validate_frozen_full_launch_request"](
                legacy_root, cases, cases, source_drift
            )
        explicit_four_hour = parser.parse_args(
            [
                "--jobs",
                "32",
                "--case-timeout",
                "4h",
                "--postgres-url",
                "postgresql://logos@127.0.0.1:55490/postgres",
                "--allow-ungated-full-run",
            ]
        )
        namespace["validate_frozen_full_launch_request"](
            legacy_root, cases, cases, explicit_four_hour
        )
        explicit_four_hour.case_timeout = 3600
        with self.assertRaises(namespace["RunnerError"]):
            namespace["validate_frozen_full_launch_request"](
                legacy_root, cases, cases, explicit_four_hour
            )

    def test_cohort16_gate_rejects_unverified_summary(self) -> None:
        namespace = runpy.run_path(str(RUNNER))
        scope = json.loads(namespace["FROZEN_SCOPE"].read_text())
        case_ids = sorted(scope["ablationCases"] + scope["extensionCases"])
        benchmark_case = namespace["BenchmarkCase"]
        cases = []
        for index, case_id in enumerate(case_ids):
            case_dir = self.root / f"gate-input-{index}"
            case_dir.mkdir()
            for name in ("schema.sql", "sql1.sql", "sql2.sql"):
                (case_dir / name).write_text(f"-- {case_id} {name}\n")
            cases.append(
                benchmark_case(
                    case_id=case_id,
                    cohort="gate",
                    input_dir=case_dir,
                    relative_dir=case_dir.name,
                    schema=case_dir / "schema.sql",
                    source=case_dir / "sql1.sql",
                    target=case_dir / "sql2.sql",
                    source_benchmark=None,
                    source_case=None,
                    flat_case_id=None,
                )
            )
        gate_path = self.root / "unverified-gate.json"
        gate_path.write_text(
            json.dumps(
                {
                    "schemaVersion": 1,
                    "status": "complete",
                    "cases": case_ids,
                    "counts": {
                        "selected": 16,
                        "pending": 0,
                        "completed": 16,
                        "timedOut": 0,
                        "failed": 0,
                        "cancelled": 0,
                    },
                    "verificationMode": "outcome-unconditional",
                    "model": "gpt-5.6-sol",
                    "reasoningEffort": "medium",
                    "usageComplete": True,
                    "integrityVerification": {"verified": False},
                }
            )
        )
        args = namespace["argument_parser"]().parse_args([])
        with self.assertRaisesRegex(namespace["RunnerError"], "integrity verification"):
            namespace["cohort16_gate_record"](
                str(gate_path),
                self.input_root,
                cases,
                cases,
                {},
                {},
                {"manifestSha256": "f" * 64},
                {"sha256": "s" * 64},
                Path("/usr/bin/bash"),
                Path("/usr/bin/unshare"),
                {},
                {
                    "manifestSha256": "r" * 64,
                    "policy": "content-addressed-forced-source-build-closure-v3",
                },
                {"manifestSha256": "t" * 64},
                {"manifestSha256": "u" * 64},
                {"manifestSha256": "v" * 64},
                {"manifestSha256": "w" * 64},
                args,
                {"effectiveReference": "sha256:" + "d" * 64},
                None,
            )

    def test_input_drift_prevents_terminal_complete(self) -> None:
        self.make_case(
            "cohort", "mutateinput", "bench-a", "mutateinput", "bench-a__mutateinput"
        )
        run_dir = self.root / "input-drift"
        completed = self.invoke(*self.common_args(run_dir))
        self.assertNotEqual(completed.returncode, 0)
        summary = json.loads((run_dir / "runner-summary.json").read_text())
        self.assertEqual(summary["status"], "interrupted")
        self.assertFalse(summary["integrityVerification"]["verified"])
        self.assertIn("inputs changed", summary["integrityError"])

    def test_solver_executable_drift_prevents_terminal_complete(self) -> None:
        self.make_case(
            "cohort", "mutatesolver", "bench-a", "mutatesolver", "bench-a__mutatesolver"
        )
        run_dir = self.root / "solver-drift"
        completed = self.invoke(*self.common_args(run_dir))
        self.assertNotEqual(completed.returncode, 0)
        summary = json.loads((run_dir / "runner-summary.json").read_text())
        self.assertEqual(summary["status"], "interrupted")
        self.assertIn("solver executable changed", summary["integrityError"])

    def test_trusted_stack_drift_prevents_terminal_complete(self) -> None:
        self.make_case(
            "cohort", "mutatestack", "bench-a", "mutatestack", "bench-a__mutatestack"
        )
        run_dir = self.root / "stack-drift"
        completed = self.invoke(*self.common_args(run_dir))
        self.assertNotEqual(completed.returncode, 0)
        summary = json.loads((run_dir / "runner-summary.json").read_text())
        self.assertEqual(summary["status"], "interrupted")
        self.assertIn(
            "trusted Rocq runtime snapshot file is invalid",
            summary["integrityError"],
        )

    def test_stale_binary_materialized_proof_scripts_fail_closed(self) -> None:
        self.make_case(
            "cohort",
            "mutatematerializedchecker",
            "bench-a",
            "mutatematerializedchecker",
            "bench-a__mutatematerializedchecker",
        )
        self.make_case(
            "cohort",
            "mutatematerializedlauncher",
            "bench-a",
            "mutatematerializedlauncher",
            "bench-a__mutatematerializedlauncher",
        )
        run_dir = self.root / "materialized-script-drift"
        completed = self.invoke(*self.common_args(run_dir), "--jobs", "2")
        self.assertEqual(completed.returncode, 0, completed.stderr)
        summary = json.loads((run_dir / "runner-summary.json").read_text())
        self.assertEqual(summary["counts"]["failed"], 2)
        for result in summary["results"]:
            self.assertEqual(result["status"], "failed")
            self.assertIn(
                "materialized trusted script differs from frozen stack",
                result["reportCoherenceError"],
            )

    def test_rocq_worker_drift_prevents_terminal_complete(self) -> None:
        self.make_case(
            "cohort", "mutateworker", "bench-a", "mutateworker", "bench-a__mutateworker"
        )
        run_dir = self.root / "worker-drift"
        completed = self.invoke(*self.common_args(run_dir))
        self.assertNotEqual(completed.returncode, 0)
        summary = json.loads((run_dir / "runner-summary.json").read_text())
        self.assertEqual(summary["status"], "interrupted")
        self.assertIn(
            "trusted Rocq runtime snapshot file is invalid",
            summary["integrityError"],
        )

    def test_rocq_checker_drift_prevents_terminal_complete(self) -> None:
        self.make_case(
            "cohort",
            "mutatechecker",
            "bench-a",
            "mutatechecker",
            "bench-a__mutatechecker",
        )
        run_dir = self.root / "checker-drift"
        completed = self.invoke(*self.common_args(run_dir))
        self.assertNotEqual(completed.returncode, 0)
        summary = json.loads((run_dir / "runner-summary.json").read_text())
        self.assertEqual(summary["status"], "interrupted")
        self.assertIn(
            "trusted Rocq runtime snapshot file is invalid",
            summary["integrityError"],
        )

    def test_codex_cli_drift_prevents_terminal_complete(self) -> None:
        self.make_case(
            "cohort", "mutatecodex", "bench-a", "mutatecodex", "bench-a__mutatecodex"
        )
        run_dir = self.root / "codex-drift"
        completed = self.invoke(*self.common_args(run_dir))
        self.assertNotEqual(completed.returncode, 0)
        summary = json.loads((run_dir / "runner-summary.json").read_text())
        self.assertEqual(summary["status"], "interrupted")
        self.assertIn("Codex command launch policy changed", summary["integrityError"])

    def test_frontend_manifest_drift_prevents_terminal_complete(self) -> None:
        self.make_case(
            "cohort",
            "tamperfrontend",
            "bench-a",
            "tamperfrontend",
            "bench-a__tamperfrontend",
        )
        run_dir = self.root / "frontend-drift"
        completed = self.invoke(*self.common_args(run_dir))
        self.assertNotEqual(completed.returncode, 0)
        summary = json.loads((run_dir / "runner-summary.json").read_text())
        self.assertEqual(summary["status"], "interrupted")
        self.assertIn(
            "preserved SQL frontend-stack manifest changed",
            summary["integrityError"],
        )

    def test_postgres_profile_is_attested_without_publishing_url(self) -> None:
        self.make_case("cohort", "one", "bench-a", "one", "bench-a__one")
        run_dir = self.root / "postgres-profile"
        url = "postgresql://logos:do-not-publish@127.0.0.1:55489/postgres"
        completed = self.invoke(*self.common_args(run_dir), "--postgres-url", url)
        self.assertEqual(completed.returncode, 0, completed.stderr)
        summary_text = (run_dir / "runner-summary.json").read_text()
        self.assertNotIn(url, summary_text)
        self.assertNotIn("do-not-publish", summary_text)
        summary = json.loads(summary_text)
        profile = summary["configuration"]["postgresServerProfile"]
        self.assertTrue(profile["configured"])
        self.assertEqual(profile["urlSha256"], hashlib.sha256(url.encode()).hexdigest())
        self.assertEqual(
            profile["profile"],
            {
                "serverVersion": "17.4",
                "serverVersionNum": "170004",
                "databaseCollation": "C",
                "databaseCharacterClassification": "C",
                "localeProvider": "libc",
                "serverEncoding": "UTF8",
                "timeZone": "UTC",
                "maxConnections": "96",
            },
        )

    def test_case_file_selects_a_batch(self) -> None:
        self.make_case("cohort", "one", "bench-a", "one", "bench-a__one")
        self.make_case("cohort", "two", "bench-a", "two", "bench-a__two")
        self.make_case("cohort", "three", "bench-a", "three", "bench-a__three")
        case_file = self.root / "cases.txt"
        case_file.write_text(
            "# deliberately non-lexicographic batch\n"
            "bench-a__three\n"
            "bench-a__one\n"
            "bench-a__three\n"
        )
        run_dir = self.root / "batch-run"

        completed = self.invoke(
            *self.common_args(run_dir),
            "--case-file",
            str(case_file),
            "--jobs",
            "2",
        )
        self.assertEqual(completed.returncode, 0, completed.stderr)
        summary = json.loads((run_dir / "runner-summary.json").read_text())
        self.assertEqual(summary["counts"]["selected"], 2)
        self.assertEqual(summary["counts"]["completed"], 2)
        self.assertEqual(
            summary["cases"],
            ["cohort__bench-a__three", "cohort__bench-a__one"],
        )
        self.assertEqual(
            [result["caseId"] for result in summary["results"]],
            ["cohort__bench-a__three", "cohort__bench-a__one"],
        )

        listed = self.invoke(
            "--input-root",
            str(self.input_root),
            "--match",
            "bench-a",
            "--list",
        )
        self.assertEqual(listed.returncode, 0, listed.stderr)
        self.assertEqual(
            [line.split("\t", 1)[0] for line in listed.stdout.splitlines()],
            [
                "cohort__bench-a__one",
                "cohort__bench-a__three",
                "cohort__bench-a__two",
            ],
        )

        bad_case_file = self.root / "bad-cases.txt"
        bad_case_file.write_text("bench-a__missing\n")
        rejected = self.invoke(
            "--input-root",
            str(self.input_root),
            "--case-file",
            str(bad_case_file),
            "--list",
        )
        self.assertNotEqual(rejected.returncode, 0)
        self.assertIn("unknown case selector: bench-a__missing", rejected.stderr)

    def test_timeout_kills_descendant_and_continues_batch(self) -> None:
        self.make_case("cohort", "ok", "bench-a", "ok", "bench-a__ok")
        self.make_case("cohort", "timeout", "bench-a", "timeout", "bench-a__timeout")
        run_dir = self.root / "timeout-run"

        completed = self.invoke(
            *self.common_args(run_dir),
            "--jobs",
            "2",
            "--case-timeout",
            "0.4s",
            "--termination-grace",
            "0.1s",
        )
        self.assertEqual(completed.returncode, 0, completed.stderr)
        summary = json.loads((run_dir / "runner-summary.json").read_text())
        self.assertEqual(summary["status"], "complete")
        self.assertEqual(summary["counts"]["completed"], 1)
        self.assertEqual(summary["counts"]["timedOut"], 1)

        timeout_dir = run_dir / "cases/cohort__bench-a__timeout"
        self.assertEqual((timeout_dir / "term-observed").read_text(), "SIGTERM\n")
        child_token = (timeout_dir / "child.token").read_text()
        deadline = time.monotonic() + 3
        while processes_with_argument(child_token) and time.monotonic() < deadline:
            time.sleep(0.05)
        self.assertEqual(processes_with_argument(child_token), [])

    def test_missing_or_malformed_usage_fails_closed(self) -> None:
        self.make_case(
            "cohort", "missingusage", "bench-a", "missingusage", "bench-a__missingusage"
        )
        self.make_case(
            "cohort",
            "malformedusage",
            "bench-a",
            "malformedusage",
            "bench-a__malformedusage",
        )
        run_dir = self.root / "usage-failures"

        completed = self.invoke(*self.common_args(run_dir), "--jobs", "2")
        self.assertEqual(completed.returncode, 0, completed.stderr)
        summary = json.loads((run_dir / "runner-summary.json").read_text())
        self.assertEqual(summary["counts"]["failed"], 2)
        self.assertFalse(summary["usageComplete"])
        for result in summary["results"]:
            self.assertEqual(result["status"], "failed")
            self.assertIn("usageError", result)
            self.assertNotIn("llmUsage", result)

    def test_incomplete_accounting_does_not_mask_a_certified_result(self) -> None:
        self.make_case(
            "cohort",
            "partialusage",
            "bench-a",
            "partialusage",
            "bench-a__partialusage",
        )
        run_dir = self.root / "partial-usage"

        completed = self.invoke(*self.common_args(run_dir))
        self.assertEqual(completed.returncode, 0, completed.stderr)
        summary = json.loads((run_dir / "runner-summary.json").read_text())
        result = summary["results"][0]
        self.assertEqual(result["status"], "completed")
        self.assertEqual(result["backendStatus"], "proof_complete")
        self.assertIn("llmUsage", result)
        self.assertFalse(result["usageComplete"])
        self.assertFalse(summary["usageComplete"])

    def test_nonzero_without_report_preserves_complete_utf8_stderr(self) -> None:
        self.make_case("cohort", "nonzero", "bench-a", "nonzero", "bench-a__nonzero")
        run_dir = self.root / "nonzero-diagnostic"

        completed = self.invoke(*self.common_args(run_dir))
        self.assertEqual(completed.returncode, 0, completed.stderr)
        result = json.loads(
            (run_dir / "cases/cohort__bench-a__nonzero/runner-result.json").read_text()
        )
        self.assertEqual(result["status"], "failed")
        self.assertEqual(result["returnCode"], 7)
        self.assertIn("SQLSTATE 22012", result["runnerError"])
        self.assertIn("除以零", result["runnerError"])
        self.assertEqual(result["reason"], result["runnerError"])
        self.assertIn("prefix:" + "x" * 9000, result["runnerError"])
        self.assertGreater(len(result["runnerError"]), 9_000)

    def test_resume_rejects_configuration_mismatch(self) -> None:
        self.make_case("cohort", "one", "bench-a", "one", "bench-a__one")
        run_dir = self.root / "config-mismatch"
        initial = self.invoke(*self.common_args(run_dir))
        self.assertEqual(initial.returncode, 0, initial.stderr)
        self.mark_interrupted(run_dir)

        resumed = self.invoke(*self.common_args(run_dir), "--resume", "--jobs", "2")
        self.assertNotEqual(resumed.returncode, 0)
        self.assertIn("resume configuration mismatch", resumed.stderr)
        self.assertIn("jobs", resumed.stderr)
        self.assertEqual(len(self.invocation_case_ids()), 1)
        self.assertEqual(
            json.loads((run_dir / "runner-summary.json").read_text())["status"],
            "interrupted",
        )

    def test_resume_rejects_docker_image_identity_drift(self) -> None:
        self.make_case("cohort", "one", "bench-a", "one", "bench-a__one")
        run_dir = self.root / "docker-image-drift"
        initial = self.invoke(*self.common_args(run_dir))
        self.assertEqual(initial.returncode, 0, initial.stderr)
        self.mark_interrupted(run_dir)
        self.write_fake_docker("e")

        resumed = self.invoke(*self.common_args(run_dir), "--resume")
        self.assertNotEqual(resumed.returncode, 0)
        self.assertIn("resume configuration mismatch", resumed.stderr)
        self.assertIn("proofAgent", resumed.stderr)
        self.assertEqual(len(self.invocation_case_ids()), 1)

    def test_resume_rejects_frontend_launch_manifest_tamper(self) -> None:
        self.make_case("cohort", "one", "bench-a", "one", "bench-a__one")
        run_dir = self.root / "frontend-manifest-tamper"
        initial = self.invoke(*self.common_args(run_dir))
        self.assertEqual(initial.returncode, 0, initial.stderr)
        self.mark_interrupted(run_dir)
        path = run_dir / "frontend-stack-manifest.json"
        document = json.loads(path.read_text(encoding="utf-8"))
        document["launchEnvironment"]["fixedVariables"][0] = "PATH=/hostile"
        path.write_text(json.dumps(document), encoding="utf-8")

        resumed = self.invoke(*self.common_args(run_dir), "--resume")
        self.assertNotEqual(resumed.returncode, 0)
        self.assertIn("resume SQL frontend-stack manifest differs", resumed.stderr)
        self.assertEqual(len(self.invocation_case_ids()), 1)

    def test_resume_rejects_system_identity_manifest_tamper(self) -> None:
        self.make_case("cohort", "one", "bench-a", "one", "bench-a__one")
        run_dir = self.root / "identity-manifest-tamper"
        initial = self.invoke(*self.common_args(run_dir))
        self.assertEqual(initial.returncode, 0, initial.stderr)
        self.mark_interrupted(run_dir)
        path = run_dir / "trusted-proof-stack-manifest.json"
        document = json.loads(path.read_text(encoding="utf-8"))
        document["trustedHostTools"]["systemIdentityConfiguration"]["paths"][0][
            "sha256"
        ] = "0" * 64
        path.write_text(json.dumps(document), encoding="utf-8")

        resumed = self.invoke(*self.common_args(run_dir), "--resume")
        self.assertNotEqual(resumed.returncode, 0)
        self.assertIn("resume trusted proof-stack manifest differs", resumed.stderr)
        self.assertEqual(len(self.invocation_case_ids()), 1)

    def test_resume_reuses_existing_terminal_result(self) -> None:
        self.make_case("cohort", "one", "bench-a", "one", "bench-a__one")
        run_dir = self.root / "reuse-terminal"
        initial = self.invoke(*self.common_args(run_dir))
        self.assertEqual(initial.returncode, 0, initial.stderr)
        before = self.mark_interrupted(run_dir)
        result_path = run_dir / "cases/cohort__bench-a__one/runner-result.json"
        preserved_result = json.loads(result_path.read_text())

        resumed = self.invoke(*self.common_args(run_dir), "--resume")
        self.assertEqual(resumed.returncode, 0, resumed.stderr)
        summary = json.loads((run_dir / "runner-summary.json").read_text())
        self.assertEqual(self.invocation_case_ids(), ["cohort__bench-a__one"])
        self.assertEqual(summary["status"], "complete")
        self.assertEqual(summary["startedAt"], before["startedAt"])
        self.assertGreaterEqual(summary["elapsedMs"], before["elapsedMs"])
        self.assertEqual(summary["results"], [preserved_result])
        self.assertEqual(summary["continuations"][0]["reusedTerminalCases"], 1)
        self.assertEqual(summary["continuations"][0]["scheduledNeverStartedCases"], 0)

    def test_resume_reconciles_crash_window_case_sidecars_without_rerun(
        self,
    ) -> None:
        self.make_case("cohort", "one", "bench-a", "one", "bench-a__one")
        self.make_case(
            "cohort",
            "missingusage",
            "bench-a",
            "missingusage",
            "bench-a__missingusage",
        )
        run_dir = self.root / "crash-window-sidecar-reconciliation"
        initial = self.invoke(*self.common_args(run_dir), "--jobs", "2")
        self.assertEqual(initial.returncode, 0, initial.stderr)
        self.mark_interrupted(run_dir)

        completed_dir = run_dir / "cases/cohort__bench-a__one"
        failed_dir = run_dir / "cases/cohort__bench-a__missingusage"
        completed_result = json.loads(
            (completed_dir / "runner-result.json").read_text(encoding="utf-8")
        )
        failed_result = json.loads(
            (failed_dir / "runner-result.json").read_text(encoding="utf-8")
        )
        (completed_dir / "status.json").unlink()
        (completed_dir / "time.txt").write_text(
            "elapsed_ms=forged\n", encoding="utf-8"
        )
        (completed_dir / "usage.json").unlink()
        (failed_dir / "status.json").write_text("{}\n", encoding="utf-8")
        (failed_dir / "time.txt").unlink()
        (failed_dir / "usage.json").write_text(
            json.dumps(self.usage(999, 0, 999)), encoding="utf-8"
        )

        resumed = self.invoke(*self.common_args(run_dir), "--resume", "--jobs", "2")
        self.assertEqual(resumed.returncode, 0, resumed.stderr)
        self.assertEqual(
            sorted(self.invocation_case_ids()),
            ["cohort__bench-a__missingusage", "cohort__bench-a__one"],
        )
        self.assertEqual(
            json.loads((completed_dir / "runner-result.json").read_text()),
            completed_result,
        )
        self.assertEqual(
            json.loads((completed_dir / "usage.json").read_text()),
            completed_result["llmUsage"],
        )
        self.assertEqual(
            (completed_dir / "time.txt").read_text(encoding="utf-8"),
            f"elapsed_ms={completed_result['elapsedMs']}\n",
        )
        self.assertEqual(
            (failed_dir / "time.txt").read_text(encoding="utf-8"),
            f"elapsed_ms={failed_result['elapsedMs']}\n",
        )
        self.assertFalse((failed_dir / "usage.json").exists())
        for case_dir, result in (
            (completed_dir, completed_result),
            (failed_dir, failed_result),
        ):
            status = json.loads((case_dir / "status.json").read_text())
            self.assertEqual(status["caseId"], result["caseId"])
            self.assertEqual(status["status"], result["status"])
            self.assertEqual(status["returnCode"], result.get("returnCode"))
            self.assertEqual(status["outcome"], result.get("outcome"))
            self.assertEqual(
                status["usageComplete"],
                result.get("usageComplete", "llmUsage" in result),
            )

    def test_resume_recovers_valid_terminal_report_without_rerun(self) -> None:
        self.make_case("cohort", "one", "bench-a", "one", "bench-a__one")
        self.make_case("cohort", "two", "bench-a", "two", "bench-a__two")
        run_dir = self.root / "partial-terminalization"
        initial = self.invoke(*self.common_args(run_dir), "--jobs", "2")
        self.assertEqual(initial.returncode, 0, initial.stderr)
        self.mark_interrupted(run_dir)
        partial_dir = run_dir / "cases/cohort__bench-a__two"
        (partial_dir / "runner-result.json").unlink()

        resumed = self.invoke(*self.common_args(run_dir), "--resume", "--jobs", "2")
        self.assertEqual(resumed.returncode, 0, resumed.stderr)
        self.assertEqual(len(self.invocation_case_ids()), 2)
        result = json.loads((partial_dir / "runner-result.json").read_text())
        self.assertEqual(result["status"], "completed")
        self.assertTrue(result["elapsedIncomplete"])
        self.assertTrue(result["recoveredFromTerminalReport"])
        self.assertNotIn("interruptionReason", result)
        self.assertIn("llmUsage", result)
        summary = json.loads((run_dir / "runner-summary.json").read_text())
        self.assertEqual(summary["counts"]["completed"], 2)
        self.assertEqual(summary["counts"]["failed"], 0)
        self.assertEqual(
            summary["continuations"][0]["finalizedInterruptedCaseIds"],
            ["cohort__bench-a__two"],
        )

    def test_resume_terminal_report_recovery_rejects_malformed_and_partial(
        self,
    ) -> None:
        for name in ("malformed", "partial"):
            self.make_case("cohort", name, "bench-a", name, f"bench-a__{name}")
        run_dir = self.root / "terminal-report-recovery-reject"
        initial = self.invoke(*self.common_args(run_dir), "--jobs", "2")
        self.assertEqual(initial.returncode, 0, initial.stderr)
        self.mark_interrupted(run_dir)
        malformed_dir = run_dir / "cases/cohort__bench-a__malformed"
        partial_dir = run_dir / "cases/cohort__bench-a__partial"
        (malformed_dir / "runner-result.json").unlink()
        (partial_dir / "runner-result.json").unlink()
        malformed_report = json.loads((malformed_dir / "report.json").read_text())
        malformed_report["outcome"] = "forged_terminal_outcome"
        (malformed_dir / "report.json").write_text(
            json.dumps(malformed_report), encoding="utf-8"
        )
        (partial_dir / "report.json").write_text("{", encoding="utf-8")

        resumed = self.invoke(*self.common_args(run_dir), "--resume", "--jobs", "2")
        self.assertEqual(resumed.returncode, 0, resumed.stderr)
        self.assertEqual(len(self.invocation_case_ids()), 2)
        summary = json.loads((run_dir / "runner-summary.json").read_text())
        self.assertEqual(summary["counts"]["completed"], 0)
        self.assertEqual(summary["counts"]["failed"], 2)
        for result in summary["results"]:
            self.assertEqual(result["status"], "failed")
            self.assertIn("interruptionReason", result)
            self.assertFalse(result.get("recoveredFromTerminalReport", False))

    def test_resume_schedules_only_cases_without_directories(self) -> None:
        for name in ("one", "two", "three"):
            self.make_case("cohort", name, "bench-a", name, f"bench-a__{name}")
        run_dir = self.root / "pending-only"
        initial = self.invoke(*self.common_args(run_dir), "--jobs", "2")
        self.assertEqual(initial.returncode, 0, initial.stderr)
        self.mark_interrupted(run_dir)
        shutil.rmtree(run_dir / "cases/cohort__bench-a__two")

        resumed = self.invoke(*self.common_args(run_dir), "--resume", "--jobs", "2")
        self.assertEqual(resumed.returncode, 0, resumed.stderr)
        invocations = self.invocation_case_ids()
        self.assertEqual(invocations.count("cohort__bench-a__one"), 1)
        self.assertEqual(invocations.count("cohort__bench-a__two"), 2)
        self.assertEqual(invocations.count("cohort__bench-a__three"), 1)
        summary = json.loads((run_dir / "runner-summary.json").read_text())
        self.assertEqual(summary["continuations"][0]["scheduledNeverStartedCases"], 1)

    def test_resume_completes_summary_with_reused_partial_and_pending_cases(
        self,
    ) -> None:
        for name in ("one", "two", "three"):
            self.make_case("cohort", name, "bench-a", name, f"bench-a__{name}")
        run_dir = self.root / "reconciled-summary"
        initial = self.invoke(*self.common_args(run_dir), "--jobs", "2")
        self.assertEqual(initial.returncode, 0, initial.stderr)
        self.mark_interrupted(run_dir)
        (run_dir / "cases/cohort__bench-a__two/runner-result.json").unlink()
        shutil.rmtree(run_dir / "cases/cohort__bench-a__three")

        resumed = self.invoke(*self.common_args(run_dir), "--resume", "--jobs", "2")
        self.assertEqual(resumed.returncode, 0, resumed.stderr)
        summary = json.loads((run_dir / "runner-summary.json").read_text())
        self.assertEqual(summary["status"], "complete")
        self.assertEqual(summary["counts"]["selected"], 3)
        self.assertEqual(summary["counts"]["pending"], 0)
        self.assertEqual(summary["counts"]["completed"], 3)
        self.assertEqual(summary["counts"]["failed"], 0)
        self.assertEqual(len(summary["results"]), 3)
        self.assertEqual(len({value["caseId"] for value in summary["results"]}), 3)
        continuation = summary["continuations"][0]
        self.assertEqual(continuation["reusedTerminalCases"], 1)
        self.assertEqual(continuation["finalizedInterruptedCases"], 1)
        self.assertEqual(continuation["scheduledNeverStartedCases"], 1)
        self.assertEqual(continuation["status"], "complete")

    def test_partial_usage_recovery_counts_latest_cumulative_proof_snapshot(
        self,
    ) -> None:
        self.make_case("cohort", "one", "bench-a", "one", "bench-a__one")
        run_dir = self.root / "cumulative-proof-usage"
        initial = self.invoke(*self.common_args(run_dir))
        self.assertEqual(initial.returncode, 0, initial.stderr)
        self.mark_interrupted(run_dir)
        case_dir = run_dir / "cases/cohort__bench-a__one"
        (case_dir / "runner-result.json").unlink()
        (case_dir / "report.json").unlink()
        shutil.rmtree(case_dir / "proof-stage")

        counter_dir = case_dir / "rounds/01"
        counter_dir.mkdir(parents=True)
        (counter_dir / "prompt.md").write_text("counterexample prompt")
        (counter_dir / "round-report.json").write_text(
            json.dumps({"assessment": {"provider": {"usage": self.usage(100, 20, 10)}}})
        )
        proof_root = case_dir / "proof-stage/proof-agent/rounds"
        for round_index, round_name, usage in (
            (1, "01", self.usage(50, 10, 5)),
            (2, "02", self.usage(120, 60, 15)),
        ):
            proof_dir = proof_root / round_name
            proof_dir.mkdir(parents=True)
            (proof_dir / "run.json").write_text(
                json.dumps(
                    {
                        "round": round_index,
                        "sessionGeneration": 1,
                        "sessionRestarted": False,
                        "sessionId": "stable-session",
                        "usage": usage,
                    }
                )
            )

        resumed = self.invoke(*self.common_args(run_dir), "--resume")
        self.assertEqual(resumed.returncode, 0, resumed.stderr)
        result = json.loads((case_dir / "runner-result.json").read_text())
        self.assertEqual(result["status"], "failed")
        self.assertEqual(result["llmUsage"], self.usage(220, 80, 25))
        self.assertEqual(len(self.invocation_case_ids()), 1)

    def test_partial_usage_recovery_validates_incremental_resumed_rounds(self) -> None:
        self.make_case("cohort", "one", "bench-a", "one", "bench-a__one")
        run_dir = self.root / "incremental-proof-usage"
        initial = self.invoke(*self.common_args(run_dir))
        self.assertEqual(initial.returncode, 0, initial.stderr)
        self.mark_interrupted(run_dir)
        case_dir = run_dir / "cases/cohort__bench-a__one"
        (case_dir / "runner-result.json").unlink()
        (case_dir / "report.json").unlink()
        shutil.rmtree(case_dir / "proof-stage")

        proof_root = case_dir / "proof-stage/proof-agent/rounds"
        for (
            round_index,
            round_name,
            generation,
            restarted,
            session_id,
            cumulative,
            incremental,
        ) in (
            (
                1,
                "01",
                1,
                False,
                "session-a",
                self.usage(50, 10, 5),
                self.usage(50, 10, 5),
            ),
            (
                2,
                "02",
                1,
                False,
                "session-a",
                self.usage(120, 60, 15),
                self.usage(70, 50, 10),
            ),
            (
                3,
                "03",
                1,
                False,
                "session-a",
                self.usage(150, 80, 20),
                self.usage(30, 20, 5),
            ),
            (
                4,
                "04",
                1,
                False,
                "session-a",
                self.usage(190, 90, 25),
                self.usage(40, 10, 5),
            ),
        ):
            proof_dir = proof_root / round_name
            proof_dir.mkdir(parents=True)
            (proof_dir / "run.json").write_text(
                json.dumps(
                    {
                        "round": round_index,
                        "sessionGeneration": generation,
                        "sessionRestarted": restarted,
                        "sessionId": session_id,
                        "usage": incremental,
                        "cumulativeUsage": cumulative,
                    }
                )
            )

        resumed = self.invoke(*self.common_args(run_dir), "--resume")
        self.assertEqual(resumed.returncode, 0, resumed.stderr)
        result = json.loads((case_dir / "runner-result.json").read_text())
        self.assertEqual(result["status"], "failed")
        self.assertEqual(result["llmUsage"], self.usage(190, 90, 25))

    def test_partial_usage_recovery_rejects_incorrect_incremental_delta(self) -> None:
        self.make_case("cohort", "one", "bench-a", "one", "bench-a__one")
        run_dir = self.root / "invalid-incremental-proof-usage"
        initial = self.invoke(*self.common_args(run_dir))
        self.assertEqual(initial.returncode, 0, initial.stderr)
        self.mark_interrupted(run_dir)
        case_dir = run_dir / "cases/cohort__bench-a__one"
        (case_dir / "runner-result.json").unlink()
        (case_dir / "report.json").unlink()
        shutil.rmtree(case_dir / "proof-stage")

        proof_dir = case_dir / "proof-stage/proof-agent/rounds/01"
        proof_dir.mkdir(parents=True)
        (proof_dir / "run.json").write_text(
            json.dumps(
                {
                    "round": 1,
                    "sessionGeneration": 1,
                    "sessionRestarted": False,
                    "sessionId": "stable-session",
                    "usage": self.usage(49, 10, 5),
                    "cumulativeUsage": self.usage(50, 10, 5),
                }
            )
        )

        resumed = self.invoke(*self.common_args(run_dir), "--resume")
        self.assertEqual(resumed.returncode, 0, resumed.stderr)
        result = json.loads((case_dir / "runner-result.json").read_text())
        self.assertEqual(result["status"], "failed")
        self.assertIn("delta disagrees", result["usageError"])
        self.assertNotIn("llmUsage", result)

    def test_partial_usage_recovery_rejects_proof_session_mismatch(self) -> None:
        self.make_case("cohort", "one", "bench-a", "one", "bench-a__one")
        run_dir = self.root / "proof-session-mismatch"
        initial = self.invoke(*self.common_args(run_dir))
        self.assertEqual(initial.returncode, 0, initial.stderr)
        self.mark_interrupted(run_dir)
        case_dir = run_dir / "cases/cohort__bench-a__one"
        (case_dir / "runner-result.json").unlink()
        (case_dir / "report.json").unlink()
        shutil.rmtree(case_dir / "proof-stage")
        proof_root = case_dir / "proof-stage/proof-agent/rounds"
        for round_index, round_name, session_id, usage in (
            (1, "01", "session-a", self.usage(50, 10, 5)),
            (2, "02", "session-b", self.usage(120, 60, 15)),
        ):
            proof_dir = proof_root / round_name
            proof_dir.mkdir(parents=True)
            (proof_dir / "run.json").write_text(
                json.dumps(
                    {
                        "round": round_index,
                        "sessionGeneration": 1,
                        "sessionRestarted": False,
                        "sessionId": session_id,
                        "usage": usage,
                    }
                )
            )

        resumed = self.invoke(*self.common_args(run_dir), "--resume")
        self.assertEqual(resumed.returncode, 0, resumed.stderr)
        result = json.loads((case_dir / "runner-result.json").read_text())
        self.assertEqual(result["status"], "failed")
        self.assertIn("changed inside generation", result["usageError"])
        self.assertNotIn("llmUsage", result)

    def test_interrupt_kills_active_case_process_group(self) -> None:
        self.make_case("cohort", "timeout", "bench-a", "timeout", "bench-a__timeout")
        run_dir = self.root / "interrupted-run"
        process = subprocess.Popen(
            [
                sys.executable,
                str(RUNNER),
                *self.common_args(run_dir),
                "--case-timeout",
                "60s",
                "--termination-grace",
                "0.1s",
            ],
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env=self.environment,
        )
        child_token_path = run_dir / "cases/cohort__bench-a__timeout/child.token"
        deadline = time.monotonic() + 5
        while not child_token_path.is_file() and time.monotonic() < deadline:
            time.sleep(0.05)
        self.assertTrue(child_token_path.is_file(), "fake solver did not start")
        child_token = child_token_path.read_text()

        process.send_signal(signal.SIGTERM)
        # A second signal can arrive while the terminator owns a managed-process
        # lock.  The main-thread handler must remain lock-free and idempotent.
        time.sleep(0.01)
        if process.poll() is None:
            process.send_signal(signal.SIGTERM)
        _, stderr = process.communicate(timeout=5)
        self.assertEqual(process.returncode, 128 + signal.SIGTERM, stderr)
        summary = json.loads((run_dir / "runner-summary.json").read_text())
        self.assertEqual(summary["status"], "interrupted")
        self.assertEqual(summary["counts"]["cancelled"], 1)
        self.assertEqual(
            (run_dir / "cases/cohort__bench-a__timeout/term-observed").read_text(),
            "SIGTERM\n",
        )

        deadline = time.monotonic() + 3
        while processes_with_argument(child_token) and time.monotonic() < deadline:
            time.sleep(0.05)
        self.assertEqual(processes_with_argument(child_token), [])


def processes_with_argument(token: str) -> list[int]:
    encoded = token.encode("utf-8")
    matches: list[int] = []
    try:
        entries = list(Path("/proc").iterdir())
    except OSError:
        return matches
    for entry in entries:
        if not entry.name.isdigit():
            continue
        process_id = int(entry.name)
        try:
            arguments = (entry / "cmdline").read_bytes().split(b"\0")
        except (FileNotFoundError, ProcessLookupError, PermissionError, OSError):
            continue
        if encoded in arguments and process_is_live(process_id):
            matches.append(process_id)
    return sorted(matches)


def process_is_live(pid: int) -> bool:
    stat_path = Path(f"/proc/{pid}/stat")
    try:
        fields = stat_path.read_text().split()
    except FileNotFoundError:
        return False
    return len(fields) < 3 or fields[2] != "Z"


if __name__ == "__main__":
    unittest.main()
