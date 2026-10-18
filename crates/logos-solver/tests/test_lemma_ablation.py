"""Availability, non-disclosure, and real Rocq elaboration regression tests."""

import importlib.util
import json
import os
from pathlib import Path
import subprocess
import shutil
import tempfile
import unittest

SCRIPTS = Path(__file__).resolve().parents[1] / "scripts"
SPEC = importlib.util.spec_from_file_location(
    "lemma_ablation", SCRIPTS / "lemma-ablation.py"
)
A = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(A)
REPO = SCRIPTS.parents[2]
ROCQ = Path(os.environ.get("LOGOS_TEST_ROCQ", REPO / ".opam-rocq/_opam/bin/rocq"))


class AvailabilityTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.authority = self.root / "authority"
        source = self.authority / "theories/FormalSQL/Example.v"
        source.parent.mkdir(parents=True)
        source.write_text("""Definition rows_bag : Prop := True.
Lemma bag_same : rows_bag. Proof. exact I. Qed.
Lemma wrapper : True. Proof. exact bag_same. Qed.
Local Lemma local_wrapper : True. Proof. exact wrapper. Qed.
Lemma plain : True. Proof. exact I. Qed.
Lemma prime' : True. Proof. exact I. Qed.
""")
        self.baseline = self.root / "Problem.v"
        self.baseline.write_text("Definition baseline_marker := 0.\n")

    def prepare(self, bag, other):
        output = self.root / f"{bag}-{other}"
        A.prepare(self.authority, output, bag, other, self.baseline)
        return output, json.loads((output / "lemma-policy.json").read_text())

    def test_four_profiles_and_bag_wrapper_closure(self):
        for bag in [False, True]:
            for other in [False, True]:
                output, policy = self.prepare(bag, other)
                for name in ["bag_same", "wrapper", "local_wrapper"]:
                    self.assertEqual(name not in policy["disabledNames"], bag)
                self.assertEqual("plain" not in policy["disabledNames"], other)
                for cached in [False, True]:
                    result = A.search.search_authority(
                        output / "lemma-surface",
                        filters=A.search.ExactFilters(),
                        page=1,
                        page_size=100,
                        show_statement=True,
                        use_cache=cached,
                    )
                    names = {r["name"] for r in result["entries"]}
                    self.assertEqual("bag_same" in names, bag)
                    self.assertEqual("plain" in names, other)
                    self.assertTrue(names.isdisjoint(policy["disabledNames"]))

    def test_abstraction_and_primitive_bag_facts_do_not_require_bag_in_name(self):
        source = self.authority / "theories/FormalSQL/FiniteBag.v"
        source.write_text("Lemma count_identity : True. Proof. exact I. Qed.\n")
        source = self.authority / "theories/FormalSQL/Abstraction.v"
        source.write_text("Lemma alpha_extensional : True. Proof. exact I. Qed.\n")
        _, policy = self.prepare(False, True)
        self.assertIn("count_identity", policy["disabledNames"])
        self.assertIn("alpha_extensional", policy["disabledNames"])

    def test_navigation_has_no_proof_body_or_hidden_names_or_objects(self):
        output, policy = self.prepare(False, True)
        view = output / "lemma-surface"
        text = (view / "theories/FormalSQL/Example.v").read_text()
        self.assertNotIn("exact I", text)
        self.assertNotIn("bag_same", text)
        self.assertNotIn("local_wrapper", text)
        self.assertIn("Definition rows_bag", text)
        self.assertIn("Lemma plain", text)
        self.assertEqual(list(view.rglob("*.vo")), [])
        self.assertNotIn(
            "exact",
            json.dumps(
                json.loads((view / "lemma-surface.json").read_text())["declarations"]
            ),
        )

    def test_navigation_preserves_literals_not_comments(self):
        text = 'Definition s := "(* real string *)". (* hidden *)\n'
        view = A.navigation_source(text, set())
        self.assertIn('"(* real string *)"', view)
        self.assertNotIn("hidden", view)

    def test_index_lines_point_into_navigation_view(self):
        output, _ = self.prepare(False, True)
        view = output / "lemma-surface"
        for record in json.loads((view / "lemma-surface.json").read_text())[
            "declarations"
        ]:
            line = (
                (view / record["source"]).read_text().splitlines()[record["line"] - 1]
            )
            self.assertIn(record["name"], line)

    @unittest.skipUnless(
        os.environ.get("LOGOS_TEST_AUTHORITY"),
        "set LOGOS_TEST_AUTHORITY to a built immutable authority for sandbox integration",
    )
    def test_real_host_checker_with_ablation_and_module_publication(self):
        authority = Path(os.environ["LOGOS_TEST_AUTHORITY"]).resolve()
        work = self.root / "workspace"
        work.mkdir()
        for name in ["WitnessModules", "ProofModules"]:
            (work / name).mkdir()
        (work / "WitnessModules/ORDER").write_text("")
        (work / "Schema.v").write_text(
            "From SQLFS Require Import SqlSyntax GenericInstance.\nDefinition sandbox_schema_marker : Prop := True.\n"
        )
        for name in ["Queries", "Witness", "WitnessData"]:
            (work / f"{name}.v").write_text(
                "From LogosGenerated Require Import Schema.\n"
            )
        (work / "Problem.v").write_text(
            "From LogosGenerated Require Import Schema Queries Witness.\nLemma sandbox_problem_marker : True. Proof. exact I. Qed.\n"
        )
        (work / "Goal.v").write_text(
            "From LogosGenerated Require Import Schema Queries Witness Problem.\nTheorem sandbox_goal_marker : True. Proof. exact sandbox_problem_marker. Qed.\n"
        )
        host = self.root / "host"
        host.mkdir()
        for name in [
            "run-trusted-rocq-check.sh",
            "lemma-ablation.py",
            "search-rocq-declarations.py",
        ]:
            shutil.copyfile(SCRIPTS / name, host / name)
        A.prepare(authority, host, False, False, work / "Problem.v")
        env = {
            **os.environ,
            "LOGOS_REPO_ROOT": str(authority),
            "LOGOS_PROOF_WORKDIR": str(work),
            "LOGOS_ROCQ_OPAM_SWITCH": str(ROCQ.parent.parent.parent),
            "LOGOS_TRUSTED_ROCQ_CACHE_DIR": str(self.root / "cache-parent/cache"),
        }
        (self.root / "cache-parent").mkdir(mode=0o700)

        def check(*args, success=True):
            result = subprocess.run(
                ["bash", str(host / "run-trusted-rocq-check.sh"), *args],
                env=env,
                capture_output=True,
                text=True,
                timeout=180,
            )
            self.assertEqual(
                result.returncode == 0, success, result.stdout + result.stderr
            )
            self.assertNotIn(A.MARKER, result.stdout + result.stderr)
            return result

        check("--preflight")
        (work / "ProofModules/Core.v").write_text(
            "Lemma own_fact : True. Proof. exact I. Qed.\n"
        )
        check(
            "--module-diagnostic",
            "--candidate",
            "ProofModules/Core.v",
            "--timeout-seconds",
            "30",
        )
        self.assertTrue(
            (self.root / "cache-parent/cache/ProofModules/Core.vo").is_file()
        )
        with (work / "Problem.v").open("a") as output:
            output.write(
                "From LogosGenerated.ProofModules Require Import Core.\nLemma another : True. Proof. exact own_fact. Qed.\n"
            )
        check("--problem-diagnostic", "--timeout-seconds", "30")
        check()
        policy = json.loads((host / "lemma-policy.json").read_text())
        with (work / "Problem.v").open("a") as output:
            output.write(f"Check {policy['disabledNames'][0]}.\n")
        rejected = check(
            "--problem-diagnostic", "--timeout-seconds", "30", success=False
        )
        self.assertIn("disabled lemma reference", rejected.stderr)

    def test_direct_and_qualified_disabled_references_rejected(self):
        _, policy = self.prepare(False, True)
        for ref in ["bag_same", "Logos.FormalSQL.Example.bag_same"]:
            with self.assertRaisesRegex(ValueError, "disabled lemma"):
                A.source_check(
                    f"Lemma candidate : True. Proof. exact {ref}. Qed.", policy
                )
        A.source_check("Lemma candidate : True. Proof. exact plain. Qed.", policy)

    def test_policy_cannot_change_in_place(self):
        output, _ = self.prepare(False, True)
        with self.assertRaisesRegex(ValueError, "fresh log directory"):
            A.prepare(self.authority, output, True, False, self.baseline)

    def test_baseline_exemption_is_exact_not_name_based(self):
        self.baseline.write_text("Lemma scaffold : True. Proof. exact bag_same. Qed.\n")
        _, policy = self.prepare(False, False)
        A.source_check(self.baseline.read_text(), policy)
        with self.assertRaisesRegex(ValueError, "disabled lemma"):
            A.source_check(
                self.baseline.read_text().replace("exact bag_same", "apply bag_same"),
                policy,
            )

    def test_introspection_rejected_before_probe(self):
        _, policy = self.prepare(False, True)
        for command in [
            "Search True.",
            "About plain.",
            "Print All.",
            "Hint Resolve plain.",
            "Goal True.",
            "Program Definition x := 0.",
        ]:
            with self.assertRaises(ValueError):
                A.source_check(command, policy)

    @unittest.skipUnless(ROCQ.is_file(), "local Rocq unavailable; set LOGOS_TEST_ROCQ")
    def test_real_elaboration_rejects_implicit_hint_use(self):
        hidden = self.root / "Hidden.v"
        hidden.write_text(
            "Parameter p : Prop. Axiom forbidden : p.\n#[export] Hint Resolve forbidden : core.\n"
        )
        subprocess.run(
            [str(ROCQ), "compile", "-q", str(hidden)],
            cwd=self.root,
            check=True,
            capture_output=True,
        )
        # Axioms here are only a test fixture, never part of the production authority.
        policy = {"disabledNames": ["forbidden"], "baseline": {}}
        policy_path = self.root / "policy.json"
        policy_path.write_text(json.dumps(policy))
        for body, accepted in [("exact I", True), ("auto", False)]:
            candidate = self.root / "Candidate.v"
            typ = "True" if accepted else "p"
            # One-line declarations and module scopes must not escape inspection.
            candidate.write_text(
                f"Require Import Hidden.\nModule Inner.\nLemma result : {typ}. Proof. {body}. Qed.\nEnd Inner.\n"
            )
            instrumented = self.root / "Inspected.v"
            A.instrument(candidate, instrumented, policy)
            result = subprocess.run(
                [str(ROCQ), "compile", "-q", str(instrumented)],
                cwd=self.root,
                capture_output=True,
                text=True,
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            transcript = self.root / "transcript.txt"
            transcript.write_text(result.stdout + result.stderr)
            checked = subprocess.run(
                [
                    "python3",
                    str(SCRIPTS / "lemma-ablation.py"),
                    "check-output",
                    "--policy",
                    str(policy_path),
                    "--source",
                    str(transcript),
                ],
                capture_output=True,
                text=True,
            )
            self.assertEqual(checked.returncode == 0, accepted, checked.stderr)
            self.assertNotIn("result =", checked.stdout)
            self.assertNotIn(A.MARKER, checked.stdout)


if __name__ == "__main__":
    unittest.main()
