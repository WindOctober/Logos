#!/usr/bin/env python3
"""Exercise the diagnostic CLI and broker protocol, not its shell/Python spelling."""

import hashlib
import json
import os
from pathlib import Path
import socket
import subprocess
import tempfile
import unittest
from concurrent.futures import ThreadPoolExecutor


SCRIPT = Path(__file__).resolve().parents[1] / "scripts" / "run-rocq-check.sh"


class ModuleDraftClientTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="logos-draft-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.script = self.root / SCRIPT.name
        self.script.write_bytes(SCRIPT.read_bytes())
        self.draft = self.root / "scratch/ProofModules/CoreBridge.v"
        self.draft.parent.mkdir(parents=True)
        self.source = b"Lemma bridge : True. Proof. exact I. Qed.\n"
        self.draft.write_bytes(self.source)
        self.socket_path = self.root / "broker.sock"

    def client(self, path="scratch/ProofModules/CoreBridge.v", mode="module", extra=(),
               purpose="semantic-equivalence"):
        return subprocess.run(
            [
                "bash",
                str(self.script),
                "--mode",
                mode,
                "--candidate",
                path,
                "--purpose",
                purpose,
                "--timeout-seconds",
                "5",
                *extra,
            ],
            env={
                **os.environ,
                "LOGOS_PROOF_DIAGNOSTIC_SOCKET": str(self.socket_path),
                "LOGOS_PROOF_DIAGNOSTIC_NONCE": "a" * 64,
            },
            capture_output=True,
            text=True,
            timeout=10,
        )

    def exchange(
        self, overrides=None, path="scratch/ProofModules/CoreBridge.v", mode="module", extra=(),
        purpose="semantic-equivalence",
    ):
        with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as listener:
            listener.bind(str(self.socket_path))
            listener.listen(1)
            listener.settimeout(5)

            def serve():
                with listener.accept()[0] as connection:
                    connection.settimeout(5)
                    with connection.makefile("rb") as stream:
                        request = json.loads(stream.readline())
                        uploaded = stream.read(request["candidateBytes"])
                        result = {
                            "schemaVersion": 2,
                            "mode": request["mode"],
                            "candidatePath": request["candidatePath"],
                            "purpose": request["purpose"],
                            "candidateSha256": request["candidateSha256"],
                            "compilePassed": True,
                            "problemCompilePassed": False,
                            "compileCheckpointAdvanced": False,
                            "exitCode": 0,
                            "timedOut": False,
                        }
                        result.update(overrides or {})
                        connection.sendall(json.dumps(result).encode() + b"\n")
                        return request, uploaded

            with ThreadPoolExecutor(max_workers=1) as executor:
                response = executor.submit(serve)
                completed = self.client(path, mode, extra, purpose)
                request, uploaded = response.result(timeout=6)
        self.socket_path.unlink()
        return completed, request, uploaded

    def test_draft_is_uploaded_once_as_final_module_without_local_publication(self):
        result, request, uploaded = self.exchange()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(request["schemaVersion"], 2)
        self.assertEqual(request["nonce"], "a" * 64)
        self.assertEqual(request["requestedTimeoutSeconds"], 5)
        self.assertEqual(request["purpose"], "semantic-equivalence")
        self.assertEqual(request["mode"], "module")
        self.assertEqual(request["candidatePath"], "ProofModules/CoreBridge.v")
        self.assertEqual(
            request["candidateSha256"], hashlib.sha256(self.source).hexdigest()
        )
        self.assertEqual(request["candidateBytes"], len(self.source))
        self.assertEqual(uploaded, self.source)
        self.assertIn("ProofModules/CoreBridge.v", result.stdout)
        self.assertEqual(self.draft.read_bytes(), self.source)
        self.assertFalse((self.root / "ProofModules").exists())

    def test_prefix_probe_is_explicit_and_never_claims_publication(self):
        extra = ("--operation", "probe", "--stop-after", "2")
        result, request, uploaded = self.exchange({
            "compilePassed": False,
            "probe": {"stopAfter": 2, "prefixBytes": 25, "passed": True},
            "stdout": "1 goal: True\n",
        }, extra=extra)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(request["probe"], {"stopAfter": 2})
        self.assertEqual(uploaded, self.source)
        self.assertIn("1 goal", result.stdout)
        self.assertIn("no compilation, publication, or checkpoint", result.stdout)
        self.assertFalse((self.root / "ProofModules").exists())
        result, _, _ = self.exchange(extra=extra)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("incorrectly granted", result.stderr)
        result, _, _ = self.exchange({
            "compilePassed": False, "candidateSha256": None,
            "probe": {"stopAfter": 2, "prefixBytes": 25, "passed": True},
        }, extra=extra)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("response identity mismatch", result.stderr)

    def test_invalid_probe_options_never_connect(self):
        for extra in [
            ("--stop-after", "2"), ("--operation", "probe"),
            ("--operation", "probe", "--stop-after", "0"),
            ("--operation", "probe", "--stop-after", "-1"),
            ("--operation", "unknown"),
        ]:
            with self.subTest(extra=extra):
                self.assertEqual(self.client(extra=extra).returncode, 64)

    def test_failed_draft_remains_editable_at_the_same_logical_name(self):
        result, first, _ = self.exchange({"compilePassed": False, "exitCode": 1})
        self.assertEqual(result.returncode, 1)
        self.assertEqual(self.draft.read_bytes(), self.source)
        revised = self.source + b"(* revision *)\n"
        self.draft.write_bytes(revised)
        result, second, uploaded = self.exchange()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(first["candidatePath"], second["candidatePath"])
        self.assertNotEqual(first["candidateSha256"], second["candidateSha256"])
        self.assertEqual(uploaded, revised)

    def test_response_must_bind_final_name_mode_and_digest(self):
        for field, wrong in (
            ("mode", None),
            ("candidatePath", "scratch/ProofModules/CoreBridge.v"),
            ("candidatePath", "ProofModules/Other.v"),
            ("mode", "scratch"),
            ("candidateSha256", "0" * 64),
            ("purpose", "assembly"),
        ):
            with self.subTest(field=field, wrong=wrong):
                result, _, _ = self.exchange({field: wrong})
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("response identity mismatch", result.stderr)

    def test_unsupported_response_schema_is_rejected(self):
        for version in (None, 1, 3, "2"):
            with self.subTest(version=version):
                result, _, _ = self.exchange({"schemaVersion": version})
                self.assertNotEqual(result.returncode, 0)

    def test_problem_success_requires_both_checkpoint_flags(self):
        (self.root / "Problem.v").write_bytes(self.source)
        for passed in (False, True):
            for advanced in (False, True):
                with self.subTest(passed=passed, advanced=advanced):
                    result, request, uploaded = self.exchange(
                        {"problemCompilePassed": passed, "compileCheckpointAdvanced": advanced},
                        path="Problem.v", mode="problem", purpose="assembly",
                    )
                    self.assertEqual(result.returncode == 0, passed and advanced, result.stderr)
                    self.assertEqual(request["candidatePath"], "Problem.v")
                    self.assertEqual(request["purpose"], "assembly")
                    self.assertEqual(uploaded, self.source)

    def test_auxiliary_success_cannot_advance_problem_checkpoint(self):
        for mode in ("module", "scratch"):
            for field in ("problemCompilePassed", "compileCheckpointAdvanced"):
                with self.subTest(mode=mode, field=field):
                    result, _, _ = self.exchange({field: True}, mode=mode)
                    self.assertNotEqual(result.returncode, 0)

    def test_cli_purposes_and_failure_exit_codes(self):
        for purpose in ("static-obligation", "semantic-equivalence", "assembly"):
            with self.subTest(purpose=purpose):
                result, request, _ = self.exchange(purpose=purpose)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(request["purpose"], purpose)
        for response, expected in (
            ({"compilePassed": False, "exitCode": 1}, 1),
            ({"compilePassed": False, "exitCode": 86}, 86),
            ({"compilePassed": False, "timedOut": True}, 124),
        ):
            with self.subTest(response=response):
                result, _, _ = self.exchange(response)
                self.assertEqual(result.returncode, expected)

    def test_invalid_mode_purpose_and_missing_required_options_fail_before_connect(self):
        self.assertEqual(self.client(mode="unknown").returncode, 64)
        self.assertEqual(self.client(purpose="unknown").returncode, 64)
        result = subprocess.run(
            ["bash", str(self.script), "--timeout-seconds", "5"],
            capture_output=True, text=True, timeout=10,
        )
        self.assertEqual(result.returncode, 64, result.stderr)

    def test_legacy_module_and_disposable_scratch_modes_keep_their_identity(self):
        source = self.root / "ProofModules/CoreBridge.v"
        source.parent.mkdir()
        source.write_bytes(self.source)
        result, request, uploaded = self.exchange(path="ProofModules/CoreBridge.v")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(request["candidatePath"], "ProofModules/CoreBridge.v")
        self.assertEqual(uploaded, self.source)
        result, request, _ = self.exchange(mode="scratch")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(request["mode"], "scratch")
        self.assertEqual(request["candidatePath"], "scratch/ProofModules/CoreBridge.v")
        self.assertIn("Host scratch compile passed", result.stdout)

    def test_invalid_or_ambiguous_names_are_rejected_before_connecting(self):
        for path in (
            "scratch/ProofModules/lower.v",
            "scratch/ProofModules/Bad-name.v",
            "scratch/ProofModules/../CoreBridge.v",
            "scratch//ProofModules/CoreBridge.v",
            "scratch/ProofModules/Nested/CoreBridge.v",
            "scratch/checked/CoreBridge.v",
            "scratch/CoreBridge.v",
            "/scratch/ProofModules/CoreBridge.v",
            "scratch/ProofModules/CoreBridge.vo",
            "scratch/ProofModules/É.v",
        ):
            with self.subTest(path=path):
                result = self.client(path)
                self.assertEqual(result.returncode, 64, result.stderr)

    def test_symlink_source_or_parent_is_not_followed(self):
        self.draft.unlink()
        target = self.root / "target.v"
        target.write_bytes(self.source)
        self.draft.symlink_to(target)
        result = self.client()
        self.assertEqual(result.returncode, 66, result.stderr)
        self.draft.unlink()
        self.draft.parent.rmdir()
        target_directory = self.root / "target"
        target_directory.mkdir()
        (target_directory / self.draft.name).write_bytes(self.source)
        self.draft.parent.symlink_to(target_directory, target_is_directory=True)
        result = self.client()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("candidate parent must not be a symlink", result.stderr)


if __name__ == "__main__":
    unittest.main()
