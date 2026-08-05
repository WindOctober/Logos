from __future__ import annotations

import copy
import hashlib
import json
from pathlib import Path
import runpy
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock


SCRIPT = Path(__file__).with_name("recover-logos-proof-tail")


class RecoveryAuthorityTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.recovery = runpy.run_path(
            str(SCRIPT), run_name="recover_logos_proof_tail_test"
        )
        cls.error = cls.recovery["RecoveryError"]

    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.run_dir = self.root / "run"
        self.run_dir.mkdir()
        self.authority_root = self.run_dir / "runtime/trusted-rocq-authority"
        self.authority_root.mkdir(parents=True)
        self.snapshot_manifest = self.run_dir / "trusted-rocq-authority-manifest.json"
        self.snapshot_manifest.write_text("{}\n", encoding="utf-8")
        self.snapshot = {
            "root": str(self.authority_root),
            "manifestPath": str(self.snapshot_manifest),
            "manifestSha256": hashlib.sha256(
                self.snapshot_manifest.read_bytes()
            ).hexdigest(),
            "schemaVersion": 2,
            "algorithm": "logos-trusted-rocq-authority-snapshot-v2",
            "policy": "run-private-forced-source-build-closure-v2",
            "sourceObjectPairCount": 0,
            "fileCount": 0,
            "totalBytes": 0,
        }
        self.switch = self.run_dir / "runtime/trusted-rocq-switch"
        self.switch.mkdir()
        self.runtime_marker = self.switch / "rocq-runtime.marker"
        self.runtime_marker.write_bytes(b"immutable runtime fixture\n")
        self.runtime_manifest = self.run_dir / "trusted-rocq-runtime-manifest.json"
        self.runtime_manifest.write_text("{}\n", encoding="utf-8")
        self.runtime_document = {
            "markerSha256": hashlib.sha256(
                self.runtime_marker.read_bytes()
            ).hexdigest()
        }
        self.runtime_snapshot = {
            "root": str(self.switch),
            "manifestPath": str(self.runtime_manifest),
            "manifestSha256": hashlib.sha256(
                self.runtime_manifest.read_bytes()
            ).hexdigest(),
            "schemaVersion": 1,
            "algorithm": "logos-trusted-rocq-runtime-snapshot-v1",
            "policy": "run-private-immutable-rocq-runtime-bwrap-closure-v1",
            "fileCount": 1,
            "directoryCount": 1,
            "totalBytes": self.runtime_marker.stat().st_size,
        }
        self.authority_build_log = self.run_dir / "trusted-rocq-authority-build.log"
        self.authority_build_log.write_bytes(b"private authority build fixture\n")
        self.authority_build_log_sha256 = hashlib.sha256(
            self.authority_build_log.read_bytes()
        ).hexdigest()
        self.authority_build_log_bytes = self.authority_build_log.stat().st_size
        bootstrap = self.recovery["RUNNER"]["pin_case_process_bootstrap"](
            self.run_dir, resume=False
        )
        supervisor = self.recovery["RUNNER"]["pin_case_process_supervisor"](
            self.run_dir, resume=False
        )
        self.case_process_isolation = self.recovery["RUNNER"][
            "case_process_isolation_record"
        ](bootstrap, supervisor, self.run_dir)
        self.checker_bytes = b"#!/bin/bash\nexit 0\n"
        checker_record = {
            "path": self.recovery["TRUSTED_CHECKER_SOURCE"],
            "sha256": hashlib.sha256(self.checker_bytes).hexdigest(),
            "bytes": len(self.checker_bytes),
        }
        executable = {"path": "/fake", "sha256": "1" * 64, "bytes": 1}
        zero_configuration = {
            "algorithm": "configuration-v1",
            "pathCount": 0,
            "presentPathCount": 0,
            "absentPathCount": 0,
        }
        self.stack_document = {
            "schemaVersion": 1,
            "algorithm": "trusted-stack-v1",
            "rocqOpamSwitch": str(self.switch),
            "rocqRuntimeSnapshot": copy.deepcopy(self.runtime_snapshot),
            "rocqAuthoritySnapshot": copy.deepcopy(self.snapshot),
            "executables": {
                "rocq": executable,
                "rocqchk": executable,
                "rocqworker": executable,
                "rocqnative": executable,
                "bwrap": executable,
            },
            "dynamicLinking": {"algorithm": "dynamic-v1", "fileCount": 0},
            "trustedHostTools": {
                "toolCount": 0,
                "dynamicLinking": {"fileCount": 0},
                "inspectionEnvironment": {
                    "policy": "empty-fixed-v1",
                    "allowedVariableCount": 0,
                },
                "lddRuntimeLoaders": {
                    "candidateCount": 0,
                    "algorithm": "loaders-v1",
                    "presentCandidateCount": 0,
                    "absentCandidateCount": 0,
                },
                "systemResolverConfiguration": zero_configuration,
                "systemIdentityConfiguration": zero_configuration,
            },
            "trustedScripts": [checker_record],
            "sourceObjects": [],
            "rocqStdlib": {"objectCount": 0},
            "rocqRuntime": {"componentCount": 0, "configurationCount": 0},
        }
        self.stack_manifest = self.run_dir / "trusted-proof-stack-manifest.json"
        self.stack_manifest.write_bytes(
            self.recovery["RUNNER"]["canonical_json_bytes"](self.stack_document)
        )
        checker_policy = copy.deepcopy(
            self.recovery["RUNNER"]["trusted_checker_environment_policy_record"]()
        )
        launcher_policy = copy.deepcopy(
            self.recovery["RUNNER"][
                "proof_agent_launcher_environment_policy_record"
            ]()
        )
        proof_agent = {
            "model": "gpt-5.6-sol",
            "reasoningEffort": "medium",
            "sessionRestartAfterFailedRounds": 16,
            "sessionHomePolicy": "isolated_per_generation",
            "diagnosticTransport": "host_unix_broker",
            "diagnosticCachePolicy": "host-cache",
            "diagnosticTimeoutPolicy": "positive",
            "diagnosticBudgetPolicy": "deadline",
            "diagnosticCheckerParallelismMax": 1,
            "diagnosticCheckerSchedulingPolicy": "sequential",
            "compileCheckpointPolicy": "checkpoint",
            "scratchPersistencePolicy": "scratch",
            "writableStorageLimitBytes": 2048 * 1024 * 1024,
            "writableStoragePolicy": "tmpfs",
            "scratchAllowedExtensions": ["v", "md", "txt"],
            "trustedCheckerEnvironmentPolicy": checker_policy,
            "proofAgentLauncherEnvironmentPolicy": launcher_policy,
            "totalTimeoutSeconds": 14100,
            "trustedCheckTimeoutSeconds": 1200,
            "resourcePolicy": {
                "memoryLimitMiB": 6144,
                "storageLimitMiB": 2048,
                "cpuLimit": None,
            },
            "dockerImage": {
                "reference": "image:requested",
                "effectiveReference": "sha256:image",
            },
            "rocqOpamSwitch": str(self.switch),
        }
        trusted_stack = self.recovery["expected_trusted_stack_summary"](
            self.stack_manifest,
            hashlib.sha256(self.stack_manifest.read_bytes()).hexdigest(),
            self.stack_document,
            proof_agent,
        )
        sql = {
            "timeZone": "UTC",
            "defaultCollation": "C",
            "characterClassification": "C",
            "localeProvider": "libc",
            "serverEncoding": "UTF8",
        }
        self.configuration = {
            "inputRoot": str(self.root / "inputs"),
            "solverBin": str(self.run_dir / "runtime/logos-solver"),
            "solverBinary": {"sha256": "2" * 64},
            "solverBinarySnapshotPolicy": "snapshot-v1",
            "caseProcessIsolation": copy.deepcopy(self.case_process_isolation),
            "rocqRuntimeSnapshot": copy.deepcopy(self.runtime_snapshot),
            "rocqAuthoritySnapshot": copy.deepcopy(self.snapshot),
            "rocqAuthoritySnapshotPolicy": self.snapshot["policy"],
            "jobs": 8,
            "caseTimeoutSeconds": 14400.0,
            "statementTimeoutSeconds": 600,
            "maxCounterexampleRounds": 3,
            "terminationGraceSeconds": 10.0,
            "verificationMode": "outcome-unconditional",
            "model": "gpt-5.6-sol",
            "reasoningEffort": "medium",
            "solverArgs": [],
            "effectiveSolverArgs": ["--force-llm-assessment"],
            "counterexampleAssessmentPolicy": "force-fresh",
            "postgresUrl": {"configured": True, "sha256": "3" * 64},
            "sqlEnvironment": sql,
            "solverLaunchEnvironmentPolicy": {},
            "solverEnvironment": {},
            "frontendLaunchEnvironmentPolicy": {},
            "commandProviderEnvironmentPolicy": {},
            "frameworkSourceTree": {
                "manifestSha256": "4" * 64,
                "sourceTreeDigestHelper": copy.deepcopy(
                    self.recovery["RUNNER"]["source_tree_digest_helper_record"]()
                ),
            },
            "frameworkSourceTreeDigestPolicy": "record-only",
            "inputManifest": {"sha256": "5" * 64, "selectedSha256": "6" * 64},
            "trustedStack": trusted_stack,
            "frontendStack": {"manifestSha256": "7" * 64},
            "codexProvider": {
                "manifestSha256": "8" * 64,
                "configSha256": "9" * 64,
                "endpointSha256": "b" * 64,
            },
            "postgresServerProfile": {"manifestSha256": "c" * 64},
            "cohort16Gate": None,
            "frozenBenchmark": None,
            "rbotAuthority": None,
            "proofAgent": proof_agent,
        }
        self.summary = {
            "schemaVersion": 1,
            "status": "interrupted",
            "runDir": str(self.run_dir),
            "inputRoot": self.configuration["inputRoot"],
            "solverBin": self.configuration["solverBin"],
            "jobs": 8,
            "caseTimeoutSeconds": 14400.0,
            "terminationGraceSeconds": 10.0,
            "verificationMode": "outcome-unconditional",
            "model": "gpt-5.6-sol",
            "reasoningEffort": "medium",
            "proofAgentMemoryLimitMiB": 6144,
            "proofAgentStorageLimitMiB": 2048,
            "statementTimeoutSeconds": 600,
            "maxCounterexampleRounds": 3,
            "proofCheckTimeoutSeconds": 1200,
            "proofDockerImage": "sha256:image",
            "proofDockerImageRequested": "image:requested",
            "proofDockerImageEffective": "sha256:image",
            "solverArgs": [],
            "effectiveSolverArgs": ["--force-llm-assessment"],
            "sqlEnvironment": sql,
            "cases": ["cohort__case"],
            "configuration": self.configuration,
            "provenance": {
                "rocqRuntimeSnapshotManifestSha256": self.runtime_snapshot[
                    "manifestSha256"
                ],
                "rocqRuntimeSnapshotRoot": self.runtime_snapshot["root"],
                "rocqAuthoritySnapshotManifestSha256": self.snapshot[
                    "manifestSha256"
                ],
                "rocqAuthoritySnapshotRoot": self.snapshot["root"],
                "trustedStackManifestSha256": trusted_stack["manifestSha256"],
            },
        }
        (self.run_dir / "runner-summary.json").write_text(
            json.dumps(self.summary), encoding="utf-8"
        )

    def test_recovery_rejects_mutable_digest_helper_before_execution(self) -> None:
        sandbox_root = self.root / "recovery-helper-pin/Logos"
        copied_recovery = sandbox_root / "benchmarks/scripts/recover-logos-proof-tail"
        copied_runner = sandbox_root / "benchmarks/scripts/run-logos"
        copied_helper = sandbox_root / "scripts/logos_source_tree_digest.py"
        copied_env = sandbox_root / "scripts/logos_env.py"
        copied_recovery.parent.mkdir(parents=True)
        copied_helper.parent.mkdir(parents=True)
        shutil.copy2(SCRIPT, copied_recovery)
        shutil.copy2(SCRIPT.with_name("run-logos"), copied_runner)
        shutil.copy2(
            SCRIPT.parents[2] / "scripts/logos_source_tree_digest.py",
            copied_helper,
        )
        shutil.copy2(SCRIPT.parents[2] / "scripts/logos_env.py", copied_env)
        safe = subprocess.run(
            [sys.executable, str(copied_recovery), "--help"],
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
        self.assertEqual(safe.returncode, 0, safe.stderr)

        execution_marker = self.root / "mutable-recovery-helper-executed"
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
            [sys.executable, str(copied_recovery), "--help"],
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

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def load_authority(self, current_stack=None):
        observed = {}
        authority_document = {
            "sourceObjects": [],
            "buildLog": {
                "path": str(self.authority_build_log),
                "sha256": self.authority_build_log_sha256,
                "bytes": self.authority_build_log_bytes,
            },
        }

        def build(switch, root):
            observed["switch"] = switch
            observed["root"] = root
            return copy.deepcopy(current_stack or self.stack_document)

        def verify_runtime(root, document):
            observed["verifiedRuntimeRoot"] = root
            marker = root / "rocq-runtime.marker"
            if (
                not marker.is_file()
                or hashlib.sha256(marker.read_bytes()).hexdigest()
                != document["markerSha256"]
            ):
                raise self.recovery["RUNNER"]["RunnerError"](
                    "trusted Rocq runtime snapshot file drifted"
                )

        def validate_external(document, _runtime, _framework):
            observed["externalBindingsValidated"] = True
            binding = document["buildLog"]
            if (
                hashlib.sha256(self.authority_build_log.read_bytes()).hexdigest()
                != binding["sha256"]
                or self.authority_build_log.stat().st_size != binding["bytes"]
            ):
                raise self.recovery["RUNNER"]["RunnerError"](
                    "trusted Rocq authority build log binding drifted"
                )

        replacements = {
            "read_trusted_rocq_runtime_snapshot_manifest": lambda _path: (
                self.runtime_document,
                self.runtime_snapshot["manifestSha256"],
            ),
            "verify_trusted_rocq_runtime_snapshot_tree": verify_runtime,
            "trusted_rocq_runtime_snapshot_summary": lambda *_args: self.runtime_snapshot,
            "read_rocq_authority_snapshot_manifest": lambda _path: (
                authority_document,
                self.snapshot["manifestSha256"],
            ),
            "rocq_authority_snapshot_summary": lambda *_args: self.snapshot,
            "verify_rocq_authority_snapshot_tree": lambda root, _document: observed.setdefault(
                "verifiedRoot", root
            ),
            "validate_rocq_authority_external_bindings": validate_external,
            "build_trusted_stack_manifest": build,
        }
        with mock.patch.dict(self.recovery["RUNNER"], replacements, clear=False):
            authority = self.recovery["load_recovery_authority"](
                self.run_dir, self.summary
            )
        return authority, observed

    def test_frozen_authority_is_used_and_runtime_drift_is_rejected(self) -> None:
        authority, observed = self.load_authority()
        self.assertEqual(authority.proof_authority_root, self.authority_root)
        self.assertEqual(observed["root"], self.authority_root)
        self.assertEqual(observed["verifiedRoot"], self.authority_root)
        self.assertEqual(observed["verifiedRuntimeRoot"], self.switch)
        self.assertTrue(observed["externalBindingsValidated"])
        self.assertEqual(observed["switch"], self.switch)

        drifted = copy.deepcopy(self.stack_document)
        drifted["rocqRuntime"]["componentCount"] = 1
        with self.assertRaisesRegex(self.error, "runtime or trusted host stack changed"):
            self.load_authority(drifted)

    def test_runtime_tree_and_authority_build_log_tampering_are_rejected(self) -> None:
        self.runtime_marker.write_bytes(b"tampered runtime\n")
        with self.assertRaisesRegex(
            self.recovery["RUNNER"]["RunnerError"], "runtime snapshot file drifted"
        ):
            self.load_authority()

        self.runtime_marker.write_bytes(b"immutable runtime fixture\n")
        self.authority_build_log.write_bytes(b"tampered build log\n")
        with self.assertRaisesRegex(
            self.recovery["RUNNER"]["RunnerError"], "build log binding drifted"
        ):
            self.load_authority()

    def test_runtime_summary_and_proof_switch_drift_are_rejected(self) -> None:
        self.configuration["rocqRuntimeSnapshot"]["manifestSha256"] = "f" * 64
        (self.run_dir / "runner-summary.json").write_text(
            json.dumps(self.summary), encoding="utf-8"
        )
        with self.assertRaisesRegex(self.error, "runtime snapshot summary drifted"):
            self.load_authority()

        self.configuration["rocqRuntimeSnapshot"] = copy.deepcopy(
            self.runtime_snapshot
        )
        self.configuration["proofAgent"]["rocqOpamSwitch"] = str(
            self.root / "other-switch"
        )
        (self.run_dir / "runner-summary.json").write_text(
            json.dumps(self.summary), encoding="utf-8"
        )
        with self.assertRaisesRegex(
            self.error, "configured Rocq switch differs from the trusted stack"
        ):
            self.load_authority()

    def test_framework_digest_helper_summary_drift_is_rejected(self) -> None:
        self.configuration["frameworkSourceTree"]["sourceTreeDigestHelper"][
            "sha256"
        ] = "0" * 64
        (self.run_dir / "runner-summary.json").write_text(
            json.dumps(self.summary), encoding="utf-8"
        )
        with self.assertRaisesRegex(
            self.error, "source-tree digest helper binding drifted"
        ):
            self.load_authority()

    def test_trusted_stack_manifest_digest_tampering_is_rejected(self) -> None:
        tampered = copy.deepcopy(self.stack_document)
        tampered["unexpected"] = "digest drift"
        self.stack_manifest.write_bytes(
            self.recovery["RUNNER"]["canonical_json_bytes"](tampered)
        )
        with self.assertRaisesRegex(
            self.error, "trusted proof-stack summary or manifest digest drifted"
        ):
            self.load_authority()

    def test_case_checker_must_match_preserved_trusted_script(self) -> None:
        authority, _ = self.load_authority()
        case_dir = self.run_dir / "cases/cohort__case"
        checker = (
            case_dir
            / "proof-stage/proof-agent/trusted-launcher/run-trusted-rocq-check.sh"
        )
        checker.parent.mkdir(parents=True)
        checker.write_bytes(self.checker_bytes)
        self.assertEqual(
            self.recovery["validate_case_trusted_checker"](case_dir, authority),
            checker,
        )
        checker.write_bytes(self.checker_bytes + b"# drift\n")
        with self.assertRaisesRegex(self.error, "differs from the preserved trusted stack"):
            self.recovery["validate_case_trusted_checker"](case_dir, authority)

    def test_run_config_construction_populates_every_required_authority_field(self) -> None:
        authority, _ = self.load_authority()
        input_dir = self.root / "inputs/cohort__case"
        input_dir.mkdir(parents=True)
        bindings = {}
        for field, name in (
            ("schema", "schema.sql"),
            ("source", "sql1.sql"),
            ("target", "sql2.sql"),
        ):
            path = input_dir / name
            path.write_text("SELECT 1;\n", encoding="utf-8")
            bindings[field] = {"path": str(path), "sha256": "d" * 64, "bytes": 10}
        metadata_path = input_dir / "metadata.json"
        metadata_path.write_text(
            json.dumps(
                {
                    "flatCaseId": "cohort__case",
                    "sourceBenchmark": "cohort",
                    "sourceCase": "case",
                }
            ),
            encoding="utf-8",
        )
        bindings["metadata"] = {
            "path": str(metadata_path),
            "sha256": hashlib.sha256(metadata_path.read_bytes()).hexdigest(),
            "bytes": metadata_path.stat().st_size,
        }
        old_result = {
            "caseId": "cohort__case",
            "benchmark": "cohort",
            "inputDir": str(input_dir),
            "inputFiles": bindings,
        }
        config, case = self.recovery["config_and_case"](
            self.summary, old_result, authority
        )
        self.assertEqual(case.case_id, "cohort__case")
        self.assertEqual(case.flat_case_id, "cohort__case")
        self.assertEqual(case.source_case, "case")
        self.assertEqual(config.proof_authority_root, self.authority_root)
        self.assertEqual(config.rocq_authority_snapshot, self.snapshot)
        self.assertEqual(config.proof_rocq_opam_switch, self.switch)
        self.assertEqual(config.trusted_stack, self.configuration["trustedStack"])
        self.assertEqual(
            config.case_process_isolation, self.configuration["caseProcessIsolation"]
        )
        self.assertEqual(
            config.case_process_bootstrap,
            self.run_dir / "runtime/case-process-bootstrap",
        )
        self.assertEqual(
            config.case_process_supervisor,
            self.run_dir / "runtime/case-process-supervisor",
        )
        self.assertTrue(config.allow_framework_source_drift)
        self.assertIsNone(config.rbot_authority)

    def test_committing_publication_is_rolled_back_idempotently_after_crash(self) -> None:
        case_dir = self.run_dir / "cases/cohort__case"
        recovery_root = case_dir / self.recovery["RECOVERY_RELATIVE"]
        backup_root = recovery_root / "pre-publication"
        backup_root.mkdir(parents=True)
        originals = {}
        paths = self.recovery["recovery_publication_paths"](
            case_dir, recovery_root
        )
        absent_names = {"recovery.json", "usage.json"}
        for path, name in paths:
            path.parent.mkdir(parents=True, exist_ok=True)
            if name not in absent_names:
                payload = f"original {name}\n".encode()
                path.write_bytes(payload)
                (backup_root / name).write_bytes(payload)
                originals[path] = payload
            path.write_bytes(f"partial publication {name}\n".encode())

        formal_modules = case_dir / "proof-stage/formal-sql/ProofModules"
        formal_modules.mkdir()
        (formal_modules / "NewModule.v").write_text("partial\n", encoding="utf-8")
        stale_stage = recovery_root / ".recovery-module-publication.interrupted"
        stale_stage.mkdir()
        (stale_stage / "partial").write_text("partial\n", encoding="utf-8")
        (recovery_root / "publication-journal.json").write_text(
            json.dumps(
                {
                    "schemaVersion": 2,
                    "status": "committing",
                    "caseId": case_dir.name,
                    "checkpointSha256": "a" * 64,
                    "formalModulesExisted": False,
                }
            ),
            encoding="utf-8",
        )

        recover = self.recovery["recover_interrupted_publication"]
        recover(case_dir, recovery_root)
        for path, payload in originals.items():
            self.assertEqual(path.read_bytes(), payload)
        for path, name in paths:
            if name in absent_names:
                self.assertFalse(path.exists())
        self.assertFalse(formal_modules.exists())
        self.assertFalse(stale_stage.exists())
        journal = json.loads(
            (recovery_root / "publication-journal.json").read_text()
        )
        self.assertEqual(journal["status"], "rolled_back")
        self.assertTrue(journal["recoveredAfterInterruptedCommit"])

        # A second startup sees a completed rollback and makes no further
        # filesystem changes.
        recover(case_dir, recovery_root)
        for path, payload in originals.items():
            self.assertEqual(path.read_bytes(), payload)

    def test_committed_publication_retry_is_validated_and_idempotent(self) -> None:
        authority, _ = self.load_authority()
        case_dir = self.run_dir / "cases/cohort__case"
        recovery_root = case_dir / self.recovery["RECOVERY_RELATIVE"]
        (recovery_root / "pre-publication").mkdir(parents=True)
        problem = case_dir / "proof-stage/formal-sql/Problem.v"
        problem.parent.mkdir(parents=True)
        problem.write_text("Theorem recovered : True. exact I. Qed.\n", encoding="utf-8")
        recovery = {
            "status": "published",
            "publishedProblem": {"sha256": hashlib.sha256(problem.read_bytes()).hexdigest()},
            "trustedCheck": {"elapsedMs": 17},
        }
        recovery_path = recovery_root / "recovery.json"
        recovery_path.write_text(json.dumps(recovery), encoding="utf-8")
        proof = {"deterministicTailRecovery": recovery}
        proof_report = case_dir / "proof-stage/report.json"
        proof_report.write_text(json.dumps(proof), encoding="utf-8")
        report = {"proof": proof}
        report_path = case_dir / "report.json"
        report_path.write_text(json.dumps(report), encoding="utf-8")
        result = {"caseId": case_dir.name, "proofMetrics": {}}
        result_path = case_dir / "runner-result.json"
        result_path.write_text(json.dumps(result), encoding="utf-8")
        journal = {
            "schemaVersion": 3,
            "status": "committed",
            "caseId": case_dir.name,
            "checkpointSha256": recovery["publishedProblem"]["sha256"],
            "formalModulesExisted": False,
            "committedAt": "2026-07-30T00:00:00Z",
            "publishedProblem": self.recovery["relative_binding"](case_dir, problem),
            "publishedRecovery": self.recovery["relative_binding"](
                case_dir, recovery_path
            ),
            "publishedProofReport": self.recovery["relative_binding"](
                case_dir, proof_report
            ),
            "publishedReport": self.recovery["relative_binding"](
                case_dir, report_path
            ),
            "publishedResult": self.recovery["relative_binding"](
                case_dir, result_path
            ),
        }
        journal_path = recovery_root / "publication-journal.json"
        journal_path.write_text(json.dumps(journal), encoding="utf-8")
        validator = mock.Mock(return_value=(result, report))
        globals_dict = self.recovery["publish_case"].__globals__
        with mock.patch.dict(
            globals_dict, {"validate_current_completed_case": validator}, clear=False
        ):
            resumed = self.recovery["publish_case"](
                case_dir, self.summary, authority=authority
            )
        self.assertEqual(resumed["status"], "already_published")
        self.assertTrue(resumed["recoveredCommittedTransaction"])
        self.assertGreaterEqual(validator.call_count, 1)

        report_path.write_text(json.dumps({"proof": {"tampered": True}}), encoding="utf-8")
        with mock.patch.dict(
            globals_dict, {"validate_current_completed_case": validator}, clear=False
        ):
            with self.assertRaisesRegex(self.error, "binding drifted"):
                self.recovery["recover_interrupted_publication"](
                    case_dir, recovery_root, self.summary, authority
                )

    def test_live_publication_and_revalidation_are_refused_before_mutation(self) -> None:
        case_dir = self.run_dir / "cases/cohort__case"
        case_dir.mkdir(parents=True)
        with self.assertRaisesRegex(self.error, "live recovery publication is unsupported"):
            self.recovery["publish_case"](
                case_dir, self.summary, allow_live=True
            )
        with self.assertRaisesRegex(self.error, "live recovery publication is unsupported"):
            self.recovery["revalidate_certified_case"](
                case_dir, self.summary, allow_live=True
            )

    def test_ineligible_publication_does_not_interrupt_summary(self) -> None:
        authority, _ = self.load_authority()
        self.summary["status"] = "complete"
        self.summary["integrityVerification"] = {
            "verified": True,
            "verifiedAt": "before-ineligible-request",
        }
        summary_path = self.run_dir / "runner-summary.json"
        summary_path.write_text(json.dumps(self.summary), encoding="utf-8")
        before = summary_path.read_bytes()
        case_dir = self.run_dir / "cases/cohort__case"
        case_dir.mkdir(parents=True)
        with self.assertRaises(self.error):
            self.recovery["publish_case"](
                case_dir, self.summary, authority=authority
            )
        self.assertEqual(summary_path.read_bytes(), before)
        self.assertFalse(
            (self.run_dir / "deterministic-tail-pending-reconciliation.json").exists()
        )
        with self.assertRaises(self.error):
            self.recovery["revalidate_certified_case"](
                case_dir, self.summary, authority=authority
            )
        self.assertEqual(summary_path.read_bytes(), before)

    def test_pending_reconciliation_marks_summary_fail_closed_before_promotion(self) -> None:
        self.summary["status"] = "complete"
        self.summary["integrityVerification"] = {
            "verified": True,
            "verifiedAt": "before-promotion",
        }
        summary_path = self.run_dir / "runner-summary.json"
        summary_path.write_text(json.dumps(self.summary), encoding="utf-8")
        before_digest = hashlib.sha256(summary_path.read_bytes()).hexdigest()
        self.recovery["begin_pending_reconciliation"](
            self.run_dir, self.summary, ["cohort__case"]
        )
        interrupted = json.loads(summary_path.read_text(encoding="utf-8"))
        self.assertEqual(interrupted["status"], "interrupted")
        self.assertIs(interrupted["integrityVerification"]["verified"], False)
        self.assertIn("pending reconciliation", interrupted["integrityError"])
        pending = json.loads(
            (
                self.run_dir / "deterministic-tail-pending-reconciliation.json"
            ).read_text(encoding="utf-8")
        )
        self.assertEqual(pending["status"], "pending")
        self.assertEqual(pending["originalSummaryStatus"], "complete")
        self.assertEqual(
            pending["originalIntegrityVerification"],
            self.summary["integrityVerification"],
        )
        self.assertEqual(pending["summarySha256BeforeInterruption"], before_digest)

    def test_reconciliation_recomputes_integrity_and_never_reuses_stale_success(self) -> None:
        postgres_url = "postgresql://fixture/recovery"
        self.configuration["postgresUrl"] = {
            "configured": True,
            "sha256": hashlib.sha256(postgres_url.encode()).hexdigest(),
        }
        self.summary["integrityVerification"] = {
            "verified": True,
            "verifiedAt": "before-promotion",
        }
        (self.run_dir / "runner-summary.json").write_text(
            json.dumps(self.summary), encoding="utf-8"
        )
        authority, _ = self.load_authority()
        input_dir = self.root / "inputs/cohort__case"
        input_dir.mkdir(parents=True)
        bindings = {}
        for field, name in (
            ("schema", "schema.sql"),
            ("source", "sql1.sql"),
            ("target", "sql2.sql"),
        ):
            path = input_dir / name
            path.write_text("SELECT 1;\n", encoding="utf-8")
            bindings[field] = {
                "path": str(path),
                "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            }
        metadata_path = input_dir / "metadata.json"
        metadata_path.write_text(
            json.dumps({"flatCaseId": "cohort__case"}), encoding="utf-8"
        )
        bindings["metadata"] = {
            "path": str(metadata_path),
            "sha256": hashlib.sha256(metadata_path.read_bytes()).hexdigest(),
        }
        usage = {
            "model": "gpt-5.6-sol",
            "inputTokens": 0,
            "cachedInputTokens": 0,
            "outputTokens": 0,
            "totalTokens": 0,
            "estimatedCostUsd": 0.0,
        }
        result = {
            "caseId": "cohort__case",
            "benchmark": "cohort",
            "inputDir": str(input_dir),
            "inputFiles": bindings,
            "status": "completed",
            "returnCode": 0,
            "usageComplete": True,
            "llmUsage": usage,
        }
        result_path = self.run_dir / "cases/cohort__case/runner-result.json"
        result_path.parent.mkdir(parents=True)
        result_path.write_text(json.dumps(result), encoding="utf-8")
        with mock.patch.dict(
            self.recovery["RUNNER"],
            {
                "verify_run_integrity": mock.Mock(
                    side_effect=self.recovery["RUNNER"]["RunnerError"](
                        "injected integrity failure"
                    )
                )
            },
            clear=False,
        ):
            with self.assertRaisesRegex(
                self.recovery["RUNNER"]["RunnerError"],
                "injected integrity failure",
            ):
                self.recovery["reconcile_summary"](
                    self.run_dir,
                    self.summary,
                    authority,
                    postgres_url,
                )
        failed_summary = json.loads(
            (self.run_dir / "runner-summary.json").read_text(encoding="utf-8")
        )
        self.assertEqual(failed_summary["status"], "interrupted")
        self.assertEqual(
            failed_summary["integrityVerification"]["verified"], False
        )
        self.assertEqual(
            failed_summary["integrityError"], "injected integrity failure"
        )
        self.assertEqual(failed_summary["results"], [result])

        observed = {}

        def verify(input_root, cases, config, results):
            observed["inputRoot"] = input_root
            observed["cases"] = cases
            observed["config"] = config
            observed["results"] = results
            return {"verified": True, "verifiedAt": "after-promotion"}

        with mock.patch.dict(
            self.recovery["RUNNER"], {"verify_run_integrity": verify}, clear=False
        ):
            reconciled = self.recovery["reconcile_summary"](
                self.run_dir,
                self.summary,
                authority,
                postgres_url,
            )
        self.assertEqual(
            reconciled["integrityVerification"],
            {"verified": True, "verifiedAt": "after-promotion"},
        )
        self.assertEqual(reconciled["status"], "complete")
        self.assertNotIn("integrityError", reconciled)
        self.assertEqual(observed["config"].postgres_url, postgres_url)
        self.assertEqual(set(observed["config"].input_files), {"cohort__case"})
        self.assertEqual(observed["cases"][0].flat_case_id, "cohort__case")

    def test_committing_revalidation_is_rolled_back_after_crash(self) -> None:
        case_dir = self.run_dir / "cases/cohort__case"
        transaction_root = (
            case_dir / "proof-stage/deterministic-runner-revalidation-transaction"
        )
        backup_root = transaction_root / "pre-state"
        backup_root.mkdir(parents=True)
        paths = self.recovery["revalidation_transaction_paths"](case_dir)
        originals = {}
        for path, name in paths:
            path.parent.mkdir(parents=True, exist_ok=True)
            if name != "usage.json":
                payload = f"original {name}\n".encode()
                path.write_bytes(payload)
                (backup_root / name).write_bytes(payload)
                originals[path] = payload
            path.write_bytes(f"partial {name}\n".encode())
        evidence = case_dir / "proof-stage/deterministic-runner-revalidation"
        evidence.mkdir()
        (evidence / "partial").write_text("partial\n", encoding="utf-8")
        (transaction_root / "journal.json").write_text(
            json.dumps(
                {
                    "schemaVersion": 1,
                    "status": "committing",
                    "caseId": case_dir.name,
                }
            ),
            encoding="utf-8",
        )
        recover = self.recovery["recover_interrupted_revalidation"]
        self.assertEqual(recover(case_dir), "rolled_back")
        for path, payload in originals.items():
            self.assertEqual(path.read_bytes(), payload)
        self.assertFalse((case_dir / "usage.json").exists())
        self.assertFalse(evidence.exists())
        journal = json.loads((transaction_root / "journal.json").read_text())
        self.assertEqual(journal["status"], "rolled_back")
        self.assertTrue(journal["recoveredAfterInterruptedCommit"])
        self.assertIsNone(recover(case_dir))

        abandoned = (
            case_dir / "proof-stage/deterministic-runner-revalidation-transaction"
        )
        (abandoned / "pre-state").mkdir(parents=True)
        live_result = case_dir / "runner-result.json"
        before = live_result.read_bytes()
        self.assertIsNone(recover(case_dir))
        self.assertEqual(live_result.read_bytes(), before)
        self.assertTrue(
            any(
                path.name.startswith(
                    "deterministic-runner-revalidation-transaction-abandoned-"
                )
                for path in (case_dir / "proof-stage").iterdir()
            )
        )

    def test_committed_revalidation_retry_revalidates_evidence_and_result(self) -> None:
        authority, _ = self.load_authority()
        case_dir = self.run_dir / "cases/cohort__case"
        transaction_root = (
            case_dir / "proof-stage/deterministic-runner-revalidation-transaction"
        )
        backup_root = transaction_root / "pre-state"
        backup_root.mkdir(parents=True)
        evidence_root = case_dir / "proof-stage/deterministic-runner-revalidation"
        evidence_root.mkdir()
        report_path = case_dir / "report.json"
        report_path.parent.mkdir(parents=True, exist_ok=True)
        report = {"proof": {"backendStatus": "proof_complete"}}
        report_path.write_text(json.dumps(report), encoding="utf-8")
        problem_path = case_dir / "proof-stage/formal-sql/Problem.v"
        problem_path.parent.mkdir(parents=True)
        problem_path.write_text("Theorem p : True. exact I. Qed.\n", encoding="utf-8")
        result_path = case_dir / "runner-result.json"
        result = {"caseId": case_dir.name, "proofMetrics": {"finalProofCheckElapsedMs": 1}}
        result_path.write_text(json.dumps(result), encoding="utf-8")
        prior_result = backup_root / "runner-result.json"
        prior_result.write_text(json.dumps({"status": "failed"}), encoding="utf-8")
        evidence = {
            "schemaVersion": 1,
            "status": "accepted",
            "validatedAt": "2026-07-30T00:00:00Z",
            "report": self.recovery["relative_binding"](case_dir, report_path),
            "problem": self.recovery["relative_binding"](case_dir, problem_path),
            "priorResultSha256": hashlib.sha256(prior_result.read_bytes()).hexdigest(),
            "publishedResult": self.recovery["relative_binding"](
                case_dir, result_path
            ),
        }
        (evidence_root / "revalidation.json").write_text(
            json.dumps(evidence), encoding="utf-8"
        )
        (transaction_root / "journal.json").write_text(
            json.dumps(
                {
                    "schemaVersion": 1,
                    "status": "committed",
                    "caseId": case_dir.name,
                    "committedAt": "2026-07-30T00:00:00Z",
                }
            ),
            encoding="utf-8",
        )
        validator = mock.Mock(return_value=(result, report))
        globals_dict = self.recovery["recover_interrupted_revalidation"].__globals__
        with mock.patch.dict(
            globals_dict, {"validate_current_completed_case": validator}, clear=False
        ):
            self.assertEqual(
                self.recovery["recover_interrupted_revalidation"](
                    case_dir, self.summary, authority
                ),
                "committed",
            )
        validator.assert_called_once()
        result_path.write_text(json.dumps({"tampered": True}), encoding="utf-8")
        with mock.patch.dict(
            globals_dict, {"validate_current_completed_case": validator}, clear=False
        ):
            with self.assertRaisesRegex(self.error, "binding drifted"):
                self.recovery["recover_interrupted_revalidation"](
                    case_dir, self.summary, authority
                )


class RecoveryContextAuthorityTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.recovery = runpy.run_path(
            str(SCRIPT), run_name="recover_logos_context_authority_test"
        )
        cls.error = cls.recovery["RecoveryError"]

    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.case_dir = self.root / "run/cases/cohort__case"
        self.formal = self.case_dir / "proof-stage/formal-sql"
        self.formal.mkdir(parents=True)
        payloads = {
            "source.sql": b"SELECT 1;\n",
            "target.sql": b"SELECT 1;\n",
            "query-shape.json": b"{}\n",
            "ordered-signatures.json": b"{}\n",
            "observation-certificates.json": b"{}\n",
            "semantic-primer.md": b"primer\n",
            "search-rocq-declarations.py": b"# helper\n",
            "Schema.v": b"Definition schema_marker : True := I.\n",
            "Queries.v": b"Definition queries_marker : True := I.\n",
            "Witness.v": b"Definition witness_marker : True := I.\n",
            "Goal.v": b"Theorem generated_verification_certificate : True. exact I. Qed.\n",
        }
        for name, payload in payloads.items():
            (self.formal / name).write_bytes(payload)

        def binding(name: str) -> dict[str, object]:
            payload = payloads[name]
            return {
                "path": name,
                "bytes": len(payload),
                "sha256": hashlib.sha256(payload).hexdigest(),
            }

        manifest = {
            "schemaVersion": 8,
            "authority": self.recovery["CONTEXT_MANIFEST_AUTHORITY"],
            "verificationMode": "outcome_unconditional",
            "staticPromptAndPrimerBytes": 17,
            "sourceSql": binding("source.sql"),
            "targetSql": binding("target.sql"),
            "queryShape": binding("query-shape.json"),
            "orderedSignatures": binding("ordered-signatures.json"),
            "observationCertificates": binding("observation-certificates.json"),
            "semanticPrimer": binding("semantic-primer.md"),
            "declarationSearch": binding("search-rocq-declarations.py"),
            "schemaModule": binding("Schema.v"),
            "queriesModule": binding("Queries.v"),
            "witnessModule": binding("Witness.v"),
            "goalModule": binding("Goal.v"),
        }
        manifest_path = self.formal / "context-manifest.json"
        manifest_path.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
        context = {
            "manifestPath": "proof-stage/formal-sql/context-manifest.json",
            "manifestSha256": hashlib.sha256(manifest_path.read_bytes()).hexdigest(),
            "manifestBytes": manifest_path.stat().st_size,
            "problemModuleBytes": 1,
            "goalModuleBytes": manifest["goalModule"]["bytes"],
            "semanticPrimerBytes": manifest["semanticPrimer"]["bytes"],
            "generatedContextBytes": sum(len(value) for value in payloads.values()),
        }
        report_fields = self.recovery["CONTEXT_REPORT_BINDINGS"]
        for manifest_key, (digest_key, bytes_key) in report_fields.items():
            context[digest_key] = manifest[manifest_key]["sha256"]
            context[bytes_key] = manifest[manifest_key]["bytes"]
        self.proof = {
            "verificationMode": "outcome_unconditional",
            "proofAgentConfiguration": {
                "staticPromptAndPrimerBytes": 17,
                "context": context,
            },
        }
        self.input_files = {
            "source": {"sha256": context["sourceSqlSha256"]},
            "target": {"sha256": context["targetSqlSha256"]},
        }

        input_dir = self.root / "inputs/cohort__case"
        input_dir.mkdir(parents=True)
        sql_payloads = {
            "schema": ("schema.sql", "CREATE TABLE t (a INT);\n"),
            "source": ("sql1.sql", "SELECT 1;\n"),
            "target": ("sql2.sql", "SELECT 1;\n"),
        }
        input_files = {}
        for role, (name, sql) in sql_payloads.items():
            path = input_dir / name
            path.write_text(sql, encoding="utf-8")
            input_files[role] = {
                "path": str(path),
                "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            }
        metadata = {
            "flatCaseId": "cohort__case",
            "integrityContract": {
                "authoritativeForLogos": True,
                "silentDrops": 0,
                "sources": [{"kind": "parser_facing_ddl", "path": "schema.sql"}],
            },
        }
        metadata_path = input_dir / "metadata.json"
        metadata_path.write_text(json.dumps(metadata) + "\n", encoding="utf-8")
        input_files["metadata"] = {
            "path": str(metadata_path),
            "sha256": hashlib.sha256(metadata_path.read_bytes()).hexdigest(),
        }
        artifact_root = self.case_dir / "input"
        artifact_root.mkdir()
        integrity = {
            "caseId": "cohort__case",
            "source": str(metadata_path),
            "tables": [],
        }
        verification = {
            "sqlEnvironment": {
                "defaultCollation": "C",
                "characterClassification": "C",
                "localeProvider": "libc",
                "serverEncoding": "UTF8",
            },
            "integrityContract": integrity,
            "schema": {"path": str(input_dir / "schema.sql"), "sql": sql_payloads["schema"][1]},
            "sourceQuery": {"path": str(input_dir / "sql1.sql"), "sql": sql_payloads["source"][1]},
            "targetQuery": {"path": str(input_dir / "sql2.sql"), "sql": sql_payloads["target"][1]},
        }
        (artifact_root / "verification-input.json").write_text(
            json.dumps(verification) + "\n", encoding="utf-8"
        )
        (artifact_root / "integrity-contract.json").write_text(
            json.dumps(integrity) + "\n", encoding="utf-8"
        )
        for name, value in (
            ("schema-ir.json", {}),
            ("source-ir.json", []),
            ("target-ir.json", []),
        ):
            (artifact_root / name).write_text(json.dumps(value) + "\n", encoding="utf-8")
        self.proof["sqlEnvironment"] = verification["sqlEnvironment"]
        lowering = {
            "backend": "formal_sql_rocq",
            "sqlEnvironment": verification["sqlEnvironment"],
            "inputBindings": {
                "schemaVersion": 1,
                "caseId": "cohort__case",
                "schemaSqlSha256": input_files["schema"]["sha256"],
                "sourceSqlSha256": input_files["source"]["sha256"],
                "targetSqlSha256": input_files["target"]["sha256"],
                "verificationInputSha256": hashlib.sha256(
                    (artifact_root / "verification-input.json").read_bytes()
                ).hexdigest(),
                "integrityContractSha256": hashlib.sha256(
                    (artifact_root / "integrity-contract.json").read_bytes()
                ).hexdigest(),
                "schemaIrSha256": hashlib.sha256(
                    (artifact_root / "schema-ir.json").read_bytes()
                ).hexdigest(),
                "sourceIrSha256": hashlib.sha256(
                    (artifact_root / "source-ir.json").read_bytes()
                ).hexdigest(),
                "targetIrSha256": hashlib.sha256(
                    (artifact_root / "target-ir.json").read_bytes()
                ).hexdigest(),
            },
            "schema": {
                "status": "lowered",
                "schema": {"rocqModule": (self.formal / "Schema.v").read_text()},
            },
            "queryModule": {"rocqModule": (self.formal / "Queries.v").read_text()},
            "proofModule": {"rocqModule": "P"},
            "goalModule": {"rocqModule": (self.formal / "Goal.v").read_text()},
        }
        self.lowering_path = self.case_dir / "proof-stage/formal-sql-lowering.json"
        self.lowering_path.write_text(json.dumps(lowering) + "\n", encoding="utf-8")
        self.old_result = {
            "caseId": "cohort__case",
            "inputDir": str(input_dir),
            "inputFiles": input_files,
            "effectiveConfiguration": {
                "verificationMode": "outcome-unconditional",
                "sqlEnvironment": {"timeZone": "UTC", **verification["sqlEnvironment"]},
            },
        }

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def test_goal_and_complete_context_are_manifest_bound(self) -> None:
        bindings = self.recovery["validate_formal_context"](
            self.case_dir, self.proof, self.input_files
        )
        self.assertEqual(bindings["Goal.v"]["sha256"], hashlib.sha256(
            (self.formal / "Goal.v").read_bytes()
        ).hexdigest())
        staging = self.case_dir / "staging"
        staging.mkdir()
        for name in ("Schema.v", "Queries.v", "Witness.v", "Goal.v"):
            (staging / name).write_bytes((self.formal / name).read_bytes())
        self.recovery["validate_staged_context"](staging, bindings)
        (staging / "Goal.v").write_text("Theorem wrong : True. exact I. Qed.\n")
        with self.assertRaisesRegex(self.error, "staged context differs"):
            self.recovery["validate_staged_context"](staging, bindings)
        (self.formal / "Goal.v").write_text(
            "Theorem generated_verification_certificate : False. Admitted.\n",
            encoding="utf-8",
        )
        with self.assertRaisesRegex(self.error, "goalModule artifact drifted"):
            self.recovery["validate_formal_context"](
                self.case_dir, self.proof, self.input_files
            )

    def test_context_ancestor_symlink_is_rejected(self) -> None:
        real_formal = self.case_dir / "proof-stage/formal-real"
        self.formal.rename(real_formal)
        self.formal.symlink_to(real_formal, target_is_directory=True)
        with self.assertRaisesRegex(self.error, "symlinked ancestor"):
            self.recovery["validate_formal_context"](
                self.case_dir, self.proof, self.input_files
            )

    def test_recovery_context_is_bound_to_lowering_and_frozen_schema(self) -> None:
        bindings = self.recovery["validate_formal_context"](
            self.case_dir, self.proof, self.old_result["inputFiles"]
        )
        self.recovery["validate_case_semantic_authority"](
            self.case_dir, self.proof, self.old_result, bindings
        )
        lowering = json.loads(self.lowering_path.read_text())
        lowering["goalModule"]["rocqModule"] = "Theorem copied_goal : True. exact I. Qed.\n"
        self.lowering_path.write_text(json.dumps(lowering) + "\n")
        with self.assertRaisesRegex(self.error, "generated Goal.v differs"):
            self.recovery["validate_case_semantic_authority"](
                self.case_dir, self.proof, self.old_result, bindings
            )
        lowering["goalModule"]["rocqModule"] = (self.formal / "Goal.v").read_text()
        self.lowering_path.write_text(json.dumps(lowering) + "\n")
        schema_path = Path(self.old_result["inputFiles"]["schema"]["path"])
        schema_path.write_text("CREATE TABLE copied (x TEXT);\n")
        with self.assertRaisesRegex(self.error, "frozen schema SQL input digest drifted"):
            self.recovery["validate_case_semantic_authority"](
                self.case_dir, self.proof, self.old_result, bindings
            )

    def test_declared_semantic_sidecar_authority_is_case_name_independent(self) -> None:
        bindings = self.recovery["validate_formal_context"](
            self.case_dir, self.proof, self.old_result["inputFiles"]
        )
        metadata_path = Path(self.old_result["inputFiles"]["metadata"]["path"])
        sidecar = self.root / "authority/schema.constraints.json"
        sidecar.parent.mkdir()
        sidecar.write_text('{"tables": []}\n')
        metadata = json.loads(metadata_path.read_text())
        metadata["integrityContract"] = {
            "authoritativeForLogos": True,
            "sourceKind": "wetune_base_schema_sidecar",
            "semanticSidecar": str(sidecar),
            "sidecarAuthority": "integrity_declarations_only",
        }
        metadata["semanticConstraints"] = {"source": str(sidecar)}
        metadata_path.write_text(json.dumps(metadata) + "\n")
        self.old_result["inputFiles"]["metadata"]["sha256"] = hashlib.sha256(
            metadata_path.read_bytes()
        ).hexdigest()

        integrity_path = self.case_dir / "input/integrity-contract.json"
        integrity = json.loads(integrity_path.read_text())
        integrity["source"] = str(sidecar)
        integrity_path.write_text(json.dumps(integrity) + "\n")
        verification_path = self.case_dir / "input/verification-input.json"
        verification = json.loads(verification_path.read_text())
        verification["integrityContract"] = integrity
        verification_path.write_text(json.dumps(verification) + "\n")
        lowering = json.loads(self.lowering_path.read_text())
        lowering["inputBindings"]["integrityContractSha256"] = hashlib.sha256(
            integrity_path.read_bytes()
        ).hexdigest()
        lowering["inputBindings"]["verificationInputSha256"] = hashlib.sha256(
            verification_path.read_bytes()
        ).hexdigest()
        self.lowering_path.write_text(json.dumps(lowering) + "\n")
        self.recovery["validate_case_semantic_authority"](
            self.case_dir, self.proof, self.old_result, bindings
        )
        metadata["semanticConstraints"]["source"] = str(self.root / "wrong.json")
        metadata_path.write_text(json.dumps(metadata) + "\n")
        self.old_result["inputFiles"]["metadata"]["sha256"] = hashlib.sha256(
            metadata_path.read_bytes()
        ).hexdigest()
        with self.assertRaisesRegex(self.error, "semantic-sidecar authority is malformed"):
            self.recovery["validate_case_semantic_authority"](
                self.case_dir, self.proof, self.old_result, bindings
            )


class RecoveryModuleCacheTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.recovery = runpy.run_path(
            str(SCRIPT), run_name="recover_logos_module_cache_test"
        )
        cls.error = cls.recovery["RecoveryError"]

    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.formal = self.root / "formal"
        self.cache = self.root / "cache"
        self.formal.mkdir()
        (self.cache / "ProofModules").mkdir(parents=True)
        for name in ("Schema.v", "Queries.v", "Witness.v"):
            payload = f"Definition {name[:-2].lower()}_marker : True := I.\n".encode()
            (self.formal / name).write_bytes(payload)
            (self.cache / name).write_bytes(payload)
            (self.cache / name.replace(".v", ".vo")).write_bytes(b"object:" + payload)
        (self.formal / "Problem.v").write_text("Definition old : True := I.\n")
        (self.formal / "Goal.v").write_text("Definition goal : True := I.\n")
        self.checkpoint = self.root / "checkpoint-Problem.v"
        self.checkpoint.write_text(
            "From LogosGenerated.ProofModules Require Import CoreFacts.\n"
            "Theorem generated_queries_verified : True. exact I. Qed.\n",
            encoding="utf-8",
        )
        (self.cache / "ProofModules/ORDER").write_text(
            "CoreFacts.v\nLiftFacts.v\n", encoding="utf-8"
        )
        for name in ("CoreFacts.v", "LiftFacts.v"):
            payload = f"Lemma {name[:-2].lower()} : True. exact I. Qed.\n".encode()
            (self.cache / "ProofModules" / name).write_bytes(payload)
            (self.cache / "ProofModules" / name.replace(".v", ".vo")).write_bytes(
                b"object:" + payload
            )
        self.write_manifest()

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def write_manifest(self) -> None:
        names = [
            "Schema.v",
            "Schema.vo",
            "Queries.v",
            "Queries.vo",
            "Witness.v",
            "Witness.vo",
            "ProofModules/ORDER",
            "ProofModules/CoreFacts.v",
            "ProofModules/CoreFacts.vo",
            "ProofModules/LiftFacts.v",
            "ProofModules/LiftFacts.vo",
        ]
        text = "".join(
            f"{hashlib.sha256((self.cache / name).read_bytes()).hexdigest()}  {name}\n"
            for name in names
        )
        (self.cache / "SHA256SUMS").write_text(text, encoding="utf-8")

    def test_cache_order_and_digest_tampering_fail_closed(self) -> None:
        validate = self.recovery["validated_trusted_cache"]
        closure = validate(self.cache, self.formal)
        self.assertEqual(closure.order, ("CoreFacts.v", "LiftFacts.v"))

        (self.cache / "ProofModules/ORDER").write_text(
            "CoreFacts.v\nCoreFacts.v\n", encoding="utf-8"
        )
        with self.assertRaises(self.error):
            validate(self.cache, self.formal)

        (self.cache / "ProofModules/ORDER").write_text(
            "CoreFacts.v\nLiftFacts.v\n", encoding="utf-8"
        )
        self.write_manifest()
        (self.cache / "ProofModules/LiftFacts.vo").write_bytes(b"tampered object")
        with self.assertRaisesRegex(self.error, "manifest is not canonical"):
            validate(self.cache, self.formal)

    def test_module_importing_staging_binds_sources_and_external_order(self) -> None:
        closure = self.recovery["validated_trusted_cache"](self.cache, self.formal)
        recovery_root = self.root / "recovery"
        staging = recovery_root / "staging-workspace"
        staging.mkdir(parents=True)
        self.recovery["stage_recovery_workspace"](
            staging, self.formal, self.checkpoint, closure
        )
        self.assertEqual(
            {path.name for path in (staging / "ProofModules").iterdir()},
            {"CoreFacts.v", "LiftFacts.v"},
        )
        self.assertFalse((staging / "ProofModules/ORDER").exists())
        order_path = self.recovery["persist_staging_module_order"](
            recovery_root, closure
        )
        manifest = self.recovery["staging_manifest_document"](
            staging,
            hashlib.sha256(self.checkpoint.read_bytes()).hexdigest(),
            closure,
            order_path,
        )
        self.recovery["validate_staging_workspace"](
            staging,
            manifest,
            self.checkpoint,
            self.formal,
            closure,
            order_path,
        )
        self.assertEqual(manifest["schemaVersion"], 2)
        self.assertEqual(
            manifest["proofModuleOrder"]["modules"],
            ["CoreFacts.v", "LiftFacts.v"],
        )
        self.assertEqual(
            [entry["name"] for entry in manifest["files"]],
            [
                "Schema.v",
                "Queries.v",
                "Witness.v",
                "Problem.v",
                "Goal.v",
                "ProofModules/CoreFacts.v",
                "ProofModules/LiftFacts.v",
            ],
        )
        self.assertFalse(any(entry["name"].endswith(".vo") for entry in manifest["files"]))


if __name__ == "__main__":
    unittest.main()
