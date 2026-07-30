import hashlib
import importlib.util
import json
import subprocess
import tempfile
import unittest
from importlib.machinery import SourceFileLoader
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[3]
SCRIPT = ROOT / "benchmarks/scripts/cosette-preflight"
LOADER = SourceFileLoader("logos_cosette_preflight", str(SCRIPT))
SPEC = importlib.util.spec_from_loader(LOADER.name, LOADER)
assert SPEC is not None and SPEC.loader is not None
preflight = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(preflight)


class CosettePreflightTest(unittest.TestCase):
    @staticmethod
    def write_case(root: Path, name: str = "case") -> Path:
        case_dir = root / "nonwetune-flat" / name
        case_dir.mkdir(parents=True)
        case_path = case_dir / "case.cos"
        case_path.write_text("schema s(x:int); query q1 `select x from s`;\n")
        metadata = {
            "profile": "cosette",
            "cosetteFile": "case.cos",
            "cosetteFileSha256": hashlib.sha256(case_path.read_bytes()).hexdigest(),
            "semanticProfileCompatibility": "flagged",
            "semanticProfileCompatibilityBlockers": ["nullable SQL values"],
        }
        (case_dir / "metadata.json").write_text(json.dumps(metadata))
        return case_dir

    def test_discovers_and_binds_exact_case(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            case_dir = self.write_case(root, "rbot-demo")

            self.assertEqual(preflight.discover_cases(root, []), [case_dir])
            self.assertEqual(
                preflight.discover_cases(root, [preflight.re.compile("demo")]),
                [case_dir],
            )
            binding = preflight.validate_case_binding(case_dir)
            self.assertEqual(
                binding["sha256"], preflight.sha256_path(case_dir / "case.cos")
            )

    def test_runs_both_target_translators_without_solver(self) -> None:
        payload = {
            "coq": {
                "status": "unsupported",
                "outputBytes": 5,
                "outputSha256": "a" * 64,
                "messageTail": "parse error",
            },
            "rosette": {
                "status": "unsupported",
                "outputBytes": 5,
                "outputSha256": "b" * 64,
                "messageTail": "parse error",
            },
            "normalization": {
                "kind": "cosette-solver-whole-input-lowercase",
                "changed": True,
                "inputBytes": 52,
                "inputSha256": "",
                "outputBytes": 52,
                "outputSha256": "c" * 64,
            },
        }
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            case_dir = self.write_case(root)
            payload["normalization"]["inputSha256"] = preflight.sha256_path(
                case_dir / "case.cos"
            )
            completed = subprocess.CompletedProcess(
                args=[], returncode=0, stdout=json.dumps(payload) + "\n", stderr=""
            )
            with mock.patch.object(
                preflight.subprocess, "run", return_value=completed
            ) as run:
                result = preflight.preflight_case(
                    input_root=root,
                    case_dir=case_dir,
                    image="example.invalid/cosette@sha256:" + "1" * 64,
                    timeout_seconds=10,
                )

        self.assertEqual(result["status"], "unsupported")
        self.assertEqual(result["failureCategory"], "parser-failure")
        self.assertFalse(
            result["targetBuiltinNormalization"]["semanticPreservationEstablished"]
        )
        self.assertFalse(
            result["targetBuiltinNormalization"]["sourceAuthoritativeSubmissionAllowed"]
        )
        command = run.call_args.args[0]
        program = command[-1]
        self.assertIn("solver.gen_coq", program)
        self.assertIn("solver.gen_rosette", program)
        self.assertNotIn("solver.solve", program)

    def test_internal_generator_error_is_a_tool_crash(self) -> None:
        self.assertEqual(
            preflight.classify_stage_failure("Internal Error (to rosette)"),
            "tool-crash",
        )
        self.assertEqual(
            preflight.classify_stage_failure("Syntax Error at line 1"),
            "parser-failure",
        )

    def test_timeout_is_not_a_parser_or_prover_result(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            case_dir = self.write_case(root)
            with mock.patch.object(
                preflight.subprocess,
                "run",
                side_effect=subprocess.TimeoutExpired(["docker"], 1),
            ):
                result = preflight.preflight_case(
                    input_root=root,
                    case_dir=case_dir,
                    image="example.invalid/cosette@sha256:" + "1" * 64,
                    timeout_seconds=1,
                )

        self.assertEqual(result["status"], "timeout")
        self.assertEqual(result["failureCategory"], "timeout-resource")


if __name__ == "__main__":
    unittest.main()
