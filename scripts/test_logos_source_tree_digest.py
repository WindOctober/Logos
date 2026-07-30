#!/usr/bin/env python3
"""Focused tests for the canonical dirty source-tree digest."""

from __future__ import annotations

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

from logos_source_tree_digest import build_manifest, manifest_sha256, sha256_file


CLI = Path(__file__).with_name("logos_source_tree_digest.py")


def git(repository: Path, *arguments: str) -> None:
    subprocess.run(
        ["git", "-C", str(repository), *arguments],
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )


class SourceTreeDigestTests(unittest.TestCase):
    def test_mutable_outputs_are_excluded_but_dirty_source_is_bound(self) -> None:
        with tempfile.TemporaryDirectory(prefix="logos-source-digest-") as temporary:
            repository = Path(temporary)
            git(repository, "init", "--quiet")
            git(repository, "config", "user.name", "Digest Fixture")
            git(repository, "config", "user.email", "digest@example.invalid")
            (repository / "source.py").write_text("value = 1\n", encoding="utf-8")
            git(repository, "add", "source.py")
            git(repository, "commit", "--quiet", "-m", "fixture")

            baseline = manifest_sha256(build_manifest(repository))
            for relative in (
                "benchmarks/adapters/materializers/solver_frontend.py",
                "logs/case/stdout.log",
                ".pytest_cache/v/cache/nodeids",
                ".ruff_cache/cache-entry",
                "target/debug/binary",
                "frontend/build/generated.txt",
                "nested/logs/run.json",
            ):
                path = repository / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("mutable output\n", encoding="utf-8")
            self.assertEqual(manifest_sha256(build_manifest(repository)), baseline)

            with tempfile.TemporaryDirectory(
                prefix="logos-source-manifest-output-"
            ) as output_directory:
                output = Path(output_directory) / "manifest.json"
                completed = subprocess.run(
                    [
                        sys.executable,
                        str(CLI),
                        "--repository",
                        str(repository),
                        "--output",
                        str(output),
                    ],
                    check=False,
                    text=True,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                )
                self.assertEqual(completed.returncode, 0, completed.stderr)
                self.assertEqual(completed.stdout.strip(), sha256_file(output))

            (repository / "new_source.py").write_text(
                "new_value = 2\n", encoding="utf-8"
            )
            self.assertNotEqual(manifest_sha256(build_manifest(repository)), baseline)

    def test_dirty_submodule_content_changes_the_outer_digest(self) -> None:
        with tempfile.TemporaryDirectory(prefix="logos-submodule-digest-") as temporary:
            root = Path(temporary)
            dependency = root / "formal-sql-source"
            repository = root / "logos"
            dependency.mkdir()
            repository.mkdir()
            for value in (dependency, repository):
                git(value, "init", "--quiet")
                git(value, "config", "user.name", "Digest Fixture")
                git(value, "config", "user.email", "digest@example.invalid")
            (dependency / "Semantics.v").write_text(
                "Definition value := 1.\n", encoding="utf-8"
            )
            git(dependency, "add", "Semantics.v")
            git(dependency, "commit", "--quiet", "-m", "formal fixture")
            (repository / "runner.py").write_text("value = 1\n", encoding="utf-8")
            git(repository, "add", "runner.py")
            git(repository, "commit", "--quiet", "-m", "runner fixture")
            git(
                repository,
                "-c",
                "protocol.file.allow=always",
                "submodule",
                "add",
                "--quiet",
                str(dependency),
                "vendor/FormalSQL",
            )
            git(repository, "commit", "--quiet", "-am", "bind submodule")

            baseline = manifest_sha256(build_manifest(repository))
            checked_out = repository / "vendor/FormalSQL/Semantics.v"
            checked_out.write_text("Definition value := 2.\n", encoding="utf-8")
            dirty_manifest = build_manifest(repository)
            self.assertNotEqual(manifest_sha256(dirty_manifest), baseline)
            formal_sql = dirty_manifest["repository"]["submodules"][0]
            self.assertEqual(formal_sql["path"], "vendor/FormalSQL")
            self.assertTrue(formal_sql["dirty"])
            self.assertEqual(formal_sql["entries"][0]["path"], "Semantics.v")

    def test_runner_and_digest_helper_are_bound_even_when_clean(self) -> None:
        manifest = build_manifest(CLI.parents[1])
        entries = {
            entry["path"]: entry for entry in manifest["repository"]["entries"]
        }
        for relative in (
            "benchmarks/scripts/run-logos",
            "scripts/logos_source_tree_digest.py",
        ):
            self.assertEqual(entries[relative]["kind"], "file")
            self.assertEqual(
                entries[relative]["sha256"], sha256_file(CLI.parents[1] / relative)
            )


if __name__ == "__main__":
    unittest.main()
