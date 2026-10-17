#!/usr/bin/env python3
"""Regression tests for the unranked Rocq declaration search helper."""

from __future__ import annotations

import importlib.util
import json
import os
import subprocess
import sys
import tempfile
import unittest
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from unittest import mock


SCRIPT = Path(__file__).resolve().parents[1] / "scripts" / "search-rocq-declarations.py"
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
        self.cache = self.root / "cache"

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
                "--cache-dir",
                str(self.cache),
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

    def test_warm_cache_skips_parsing_and_matches_reference(self) -> None:
        self.write_vendor("A.v", "Lemma a : True. Proof. exact I. Qed.\n")
        self.write_theory("B.v", "Theorem b : True. Proof. exact I. Qed.\n")
        reference = SEARCH.scan_authority(self.root)
        self.assertEqual(SEARCH.cached_authority(self.root, self.cache), reference)
        with mock.patch.object(
            SEARCH, "declarations_from_source", side_effect=AssertionError("reparsed")
        ):
            self.assertEqual(SEARCH.cached_authority(self.root, self.cache), reference)
            for filters in (
                SEARCH.ExactFilters(),
                SEARCH.ExactFilters(name="a"),
                SEARCH.ExactFilters(
                    fqn="SQLFS.A.a",
                    module="SQLFS.A",
                    source="vendor/FormalSQL/src/A.v",
                    conclusion_symbol="True",
                    symbols=("True",),
                ),
                SEARCH.ExactFilters(symbols=("Missing",)),
            ):
                for page in (1, 2, 3):
                    for show_statement in (False, True):
                        arguments = dict(
                            filters=filters,
                            page=page,
                            page_size=1,
                            show_statement=show_statement,
                        )
                        warm = SEARCH.search_authority(
                            self.root, cache_dir=self.cache, **arguments
                        )
                        with mock.patch.object(
                            SEARCH, "scan_authority", return_value=reference
                        ):
                            self.assertEqual(
                                warm,
                                SEARCH.search_authority(
                                    self.root, use_cache=False, **arguments
                                ),
                            )

    def test_cli_reuses_index_between_processes_and_no_cache_is_identical(self) -> None:
        self.write_vendor("A.v", "Lemma a : True. Proof. exact I. Qed.\n")
        cold = self.run_cli("--show-statement")
        (index,) = self.cache.glob("*.json")
        before = index.stat()
        warm = self.run_cli("--show-statement")
        self.assertEqual(cold, warm)
        self.assertEqual(index.stat().st_mtime_ns, before.st_mtime_ns)
        self.assertEqual(index.stat().st_ino, before.st_ino)
        self.assertEqual(cold, self.run_cli("--show-statement", "--no-cache"))

    def test_content_change_invalidates_even_with_same_size_and_mtime(self) -> None:
        source = self.write_vendor("A.v", "Lemma a : True. Proof. exact I. Qed.\n")
        self.run_cli()
        before = source.stat()
        source.write_text("Lemma b : True. Proof. exact I. Qed.\n")
        os.utime(source, ns=(before.st_atime_ns, before.st_mtime_ns))
        self.assertEqual(source.stat().st_size, before.st_size)
        self.assertEqual(self.run_cli()["entries"][0]["name"], "b")
        self.assertEqual(len(list(self.cache.glob("*.json"))), 2)

    def test_add_delete_rename_and_symlink_change_invalidate(self) -> None:
        source = self.write_vendor("A.v", "Lemma a : True. Proof. exact I. Qed.\n")
        self.assertEqual(self.run_cli()["matched"], 1)
        extra = self.write_theory("B.v", "Lemma b : True. Proof. exact I. Qed.\n")
        self.assertEqual(self.run_cli()["matched"], 2)
        extra.unlink()
        renamed = source.with_name("Renamed.v")
        source.rename(renamed)
        self.assertEqual(self.run_cli()["entries"][0]["fqn"], "SQLFS.Renamed.a")
        target = self.root / "outside.v"
        renamed.rename(target)
        renamed.symlink_to(target)
        self.assertEqual(self.run_cli()["matched"], 0)

    def test_invalid_source_and_duplicate_fqn_are_not_hidden_by_cache(self) -> None:
        source = self.write_vendor("A.v", "Lemma a : True. Proof. exact I. Qed.\n")
        SEARCH.cached_authority(self.root, self.cache)
        for content, message in (
            (b"(* unterminated", "unterminated"),
            (b"\xff", "cannot read"),
            (
                b"Lemma a : True. Proof. exact I. Qed.\nLemma a : True. Proof. exact I. Qed.",
                "duplicate",
            ),
        ):
            source.write_bytes(content)
            with self.assertRaisesRegex(SEARCH.SearchError, message):
                SEARCH.cached_authority(self.root, self.cache)

    def test_corrupt_or_incompatible_index_is_rebuilt(self) -> None:
        self.write_vendor("A.v", "Lemma a : True. Proof. exact I. Qed.\n")
        expected = self.run_cli()
        (index,) = self.cache.glob("*.json")
        original = index.read_bytes()
        for corruption in (b"{", b"null", b"\xff"):
            index.write_bytes(corruption)
            self.assertEqual(self.run_cli(), expected)
            self.assertEqual(index.read_bytes(), original)
        for field, value in (
            ("key", "wrong"),
            ("schemaVersion", -1),
            ("declarations", []),
            ("recordsSha256", "wrong"),
        ):
            document = json.loads(original)
            document[field] = value
            index.write_text(json.dumps(document))
            self.assertEqual(self.run_cli(), expected)
        # Even structurally malformed records with an internally consistent
        # checksum are disposable, not a search failure.
        document = json.loads(original)
        document["declarations"][0]["line"] = "bad"
        document["recordsSha256"] = SEARCH.hashlib.sha256(
            SEARCH.json_bytes(document["declarations"])
        ).hexdigest()
        index.write_text(json.dumps(document))
        self.assertEqual(self.run_cli(), expected)

    def test_parser_and_schema_changes_invalidate_index(self) -> None:
        self.write_vendor("A.v", "Lemma a : True. Proof. exact I. Qed.\n")
        reference = SEARCH.cached_authority(self.root, self.cache)
        parser_copy = self.root / "parser.py"
        parser_copy.write_bytes(SCRIPT.read_bytes() + b"\n# changed parser\n")
        with mock.patch.object(SEARCH, "__file__", str(parser_copy)):
            self.assertEqual(SEARCH.cached_authority(self.root, self.cache), reference)
        with mock.patch.object(SEARCH, "INDEX_SCHEMA", SEARCH.INDEX_SCHEMA + 1):
            self.assertEqual(SEARCH.cached_authority(self.root, self.cache), reference)
        self.assertEqual(len(list(self.cache.glob("*.json"))), 3)

    def test_unavailable_cache_falls_back_and_no_cache_does_not_create_directory(
        self,
    ) -> None:
        self.write_vendor("A.v", "Lemma a : True. Proof. exact I. Qed.\n")
        reference = self.run_cli("--no-cache")
        self.assertFalse(self.cache.exists())
        self.cache.write_text("not a directory")
        self.assertEqual(self.run_cli(), reference)
        self.cache.unlink()
        self.cache.mkdir(mode=0o700)
        with mock.patch.object(
            SEARCH, "write_index", side_effect=PermissionError("read only")
        ):
            self.assertEqual(
                SEARCH.cached_authority(self.root, self.cache),
                SEARCH.scan_authority(self.root),
            )
        self.assertEqual(list(self.cache.iterdir()), [])

    def test_symlinked_cache_directory_and_file_are_not_followed(self) -> None:
        self.write_vendor("A.v", "Lemma a : True. Proof. exact I. Qed.\n")
        reference = self.run_cli("--no-cache")
        target = self.root / "target"
        target.mkdir(mode=0o700)
        self.cache.symlink_to(target, target_is_directory=True)
        self.assertEqual(self.run_cli(), reference)
        self.assertEqual(list(target.iterdir()), [])
        self.cache.unlink()
        self.run_cli()
        (index,) = self.cache.glob("*.json")
        index.unlink()
        victim = self.root / "victim"
        victim.write_text("unchanged")
        index.symlink_to(victim)
        self.assertEqual(self.run_cli(), reference)
        self.assertEqual(victim.read_text(), "unchanged")
        self.assertFalse(index.is_symlink())

    def test_concurrent_cold_processes_publish_complete_index(self) -> None:
        self.write_vendor("A.v", "Lemma a : True. Proof. exact I. Qed.\n")
        reference = self.run_cli("--no-cache")
        with ThreadPoolExecutor(max_workers=6) as executor:
            results = list(executor.map(lambda _: self.run_cli(), range(12)))
        self.assertTrue(all(result == reference for result in results))
        self.assertEqual(len(list(self.cache.glob("*.json"))), 1)
        self.assertEqual(list(self.cache.glob(".index-*")), [])
        declarations = SEARCH.scan_authority(self.root)
        with mock.patch.object(
            SEARCH, "parse_sources", side_effect=AssertionError("reparsed")
        ):
            self.assertEqual(
                SEARCH.cached_authority(self.root, self.cache), declarations
            )

    def test_newline_normalization_matches_original_reader(self) -> None:
        source = self.write_vendor("A.v", "")
        source.write_bytes(b"Lemma a :\r\n True.\rProof. exact I. Qed.\r")
        reference = self.run_cli("--no-cache", "--show-statement")
        self.assertEqual(self.run_cli("--show-statement"), reference)
        self.assertEqual(self.run_cli("--show-statement"), reference)
        self.assertEqual(reference["entries"][0]["statement"], "Lemma a :\n True.")

    def test_same_content_at_another_root_reuses_only_relative_records(self) -> None:
        content = "Lemma a : True. Proof. exact I. Qed.\n"
        self.write_vendor("A.v", content)
        reference = SEARCH.cached_authority(self.root, self.cache)
        relocated = self.root / "relocated"
        source = relocated / "vendor/FormalSQL/src/A.v"
        source.parent.mkdir(parents=True)
        source.write_text(content)
        with mock.patch.object(
            SEARCH, "parse_sources", side_effect=AssertionError("reparsed")
        ):
            self.assertEqual(SEARCH.cached_authority(relocated, self.cache), reference)
        source.write_text(content.replace("Lemma a", "Lemma b"))
        self.assertEqual(SEARCH.cached_authority(relocated, self.cache)[0].name, "b")
        self.assertEqual(SEARCH.cached_authority(self.root, self.cache), reference)

    def test_source_read_failure_is_not_hidden_by_warm_cache(self) -> None:
        self.write_vendor("A.v", "Lemma a : True. Proof. exact I. Qed.\n")
        SEARCH.cached_authority(self.root, self.cache)
        with mock.patch.object(
            Path, "read_bytes", side_effect=PermissionError("unreadable")
        ):
            with self.assertRaisesRegex(SEARCH.SearchError, "cannot read"):
                SEARCH.cached_authority(self.root, self.cache)

    def test_failed_atomic_publication_does_not_leave_partial_index(self) -> None:
        self.write_vendor("A.v", "Lemma a : True. Proof. exact I. Qed.\n")
        reference = SEARCH.scan_authority(self.root)
        with mock.patch.object(
            SEARCH.os, "replace", side_effect=OSError("quota exceeded")
        ):
            self.assertEqual(SEARCH.cached_authority(self.root, self.cache), reference)
        self.assertEqual(list(self.cache.iterdir()), [])

    def test_nonprivate_directory_is_ignored_without_chmod(self) -> None:
        self.write_vendor("A.v", "Lemma a : True. Proof. exact I. Qed.\n")
        self.cache.mkdir()
        self.cache.chmod(0o755)
        reference = self.run_cli("--no-cache")
        self.assertEqual(self.run_cli(), reference)
        self.assertEqual(list(self.cache.iterdir()), [])
        self.assertEqual(self.cache.stat().st_mode & 0o777, 0o755)


if __name__ == "__main__":
    unittest.main()
