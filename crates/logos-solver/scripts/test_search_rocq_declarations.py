#!/usr/bin/env python3
"""Regression tests for the unranked Rocq declaration search helper."""

from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).with_name("search-rocq-declarations.py")
SPEC = importlib.util.spec_from_file_location("search_rocq_declarations", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
SEARCH = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = SEARCH
SPEC.loader.exec_module(SEARCH)


class RocqDeclarationSearchTest(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        (self.root / "vendor/FormalSQL/src/data").mkdir(parents=True)
        (self.root / "theories/FormalSQL").mkdir(parents=True)

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def write_vendor(self, relative: str, text: str) -> Path:
        path = self.root / "vendor/FormalSQL/src" / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")
        return path

    def write_theory(self, relative: str, text: str) -> Path:
        path = self.root / "theories/FormalSQL" / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")
        return path

    def run_cli(self, *arguments: str) -> dict[str, object]:
        completed = subprocess.run(
            [
                sys.executable,
                str(SCRIPT),
                "--authority-root",
                str(self.root),
                *arguments,
            ],
            check=True,
            capture_output=True,
            text=True,
        )
        return json.loads(completed.stdout)

    def test_only_nonlocal_qed_declarations_are_exported(self) -> None:
        self.write_vendor(
            "data/Public.v",
            """
Lemma public_qed : True.
Proof. exact I. Qed.

Lemma public_qed' : True.
Proof. exact I. Qed.

Local Lemma local_qed : True.
Proof. exact I. Qed.

Lemma transparent_defined : True.
Proof. exact I. Defined.

Theorem unfinished_abort : True.
Proof. Abort.

Corollary admitted_claim : True.
Admitted.
""",
        )
        result = self.run_cli("--show-statement")
        self.assertEqual(result["matched"], 2)
        by_name = {entry["name"]: entry for entry in result["entries"]}
        self.assertEqual(set(by_name), {"public_qed", "public_qed'"})
        entry = by_name["public_qed"]
        self.assertEqual(entry["fqn"], "SQLFS.data.Public.public_qed")
        self.assertIn("Lemma public_qed : True.", entry["statement"])

    def test_nested_modules_are_part_of_the_exact_fqn(self) -> None:
        self.write_vendor(
            "logic/Nested.v",
            """
Module Outer.
Section HiddenSection.
Module Inner.
Theorem nested (x : nat) : True -> eq x x.
Proof. intros _. reflexivity. Qed.
End Inner.
End HiddenSection.
End Outer.
""",
        )
        result = self.run_cli("--name", "nested")
        self.assertEqual(result["matched"], 1)
        entry = result["entries"][0]
        self.assertEqual(entry["module"], "SQLFS.logic.Nested.Outer.Inner")
        self.assertEqual(entry["fqn"], "SQLFS.logic.Nested.Outer.Inner.nested")
        self.assertEqual(entry["conclusionSymbol"], "eq")

    def test_all_exact_filters_are_intersected(self) -> None:
        self.write_theory(
            "FilterFacts.v",
            """
Lemma selected (x : nat) : Qualified.Marker x -> Wanted x.
Proof. intros. assumption. Qed.

Lemma wrong_head (x : nat) : Marker x -> Other x.
Proof. intros. assumption. Qed.
""",
        )
        source = "theories/FormalSQL/FilterFacts.v"
        module = "Logos.FormalSQL.FilterFacts"
        fqn = f"{module}.selected"
        result = self.run_cli(
            "--fqn",
            fqn,
            "--name",
            "selected",
            "--module",
            module,
            "--source",
            source,
            "--conclusion-symbol",
            "Wanted",
            "--symbol",
            "Qualified.Marker",
            "--symbol",
            "Wanted",
        )
        self.assertEqual(result["matched"], 1)
        self.assertEqual(result["entries"][0]["fqn"], fqn)

        unqualified = self.run_cli("--name", "selected", "--symbol", "Marker")
        self.assertEqual(unqualified["matched"], 1)

        rejected = self.run_cli(
            "--name", "selected", "--symbol", "Marker", "--symbol", "Missing"
        )
        self.assertEqual(rejected["matched"], 0)
        self.assertEqual(rejected["entries"], [])

    def test_pages_are_stable_complete_and_have_no_priority_metadata(self) -> None:
        # Create files and declarations in deliberately non-lexical order.
        self.write_theory(
            "Zeta.v",
            """
Lemma z_second : True. Proof. exact I. Qed.
Lemma a_first_in_file : True. Proof. exact I. Qed.
""",
        )
        self.write_vendor(
            "common/Alpha.v",
            """
Lemma middle : True. Proof. exact I. Qed.
Lemma last_in_file : True. Proof. exact I. Qed.
Lemma final_entry : True. Proof. exact I. Qed.
""",
        )

        first_pass = [
            self.run_cli("--page", str(page), "--page-size", "2") for page in (1, 2, 3)
        ]
        second_pass = [
            self.run_cli("--page", str(page), "--page-size", "2") for page in (1, 2, 3)
        ]
        self.assertEqual(first_pass, second_pass)
        self.assertEqual([page["matched"] for page in first_pass], [5, 5, 5])
        self.assertEqual([page["pageCount"] for page in first_pass], [3, 3, 3])
        self.assertEqual([page["hasNext"] for page in first_pass], [True, True, False])

        fqns = [entry["fqn"] for page in first_pass for entry in page["entries"]]
        self.assertEqual(len(fqns), len(set(fqns)))
        self.assertEqual(fqns, sorted(fqns))

        forbidden = {"rank", "score", "priority", "route", "routes", "topK"}

        def assert_no_priority_fields(value: object) -> None:
            if isinstance(value, dict):
                self.assertTrue(forbidden.isdisjoint(value))
                for nested in value.values():
                    assert_no_priority_fields(nested)
            elif isinstance(value, list):
                for nested in value:
                    assert_no_priority_fields(nested)

        for page in first_pass:
            assert_no_priority_fields(page)


if __name__ == "__main__":
    unittest.main()
