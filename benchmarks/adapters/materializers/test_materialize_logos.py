#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from importlib.machinery import SourceFileLoader
from pathlib import Path
import re
import runpy
import sys
import tempfile
import unittest
from unittest import mock


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
SCRIPT = HERE / "materialize_logos.py"
DISPATCHER = ROOT / "benchmarks/scripts/materialize"
BASELINE = (
    ROOT.parent / "var/codex-background/logos-rbot-provenance-r1.non-rbot-baseline.json"
)

sys.path.insert(0, str(HERE))


def load_script():
    loader = SourceFileLoader("test_logos_materializer", str(SCRIPT))
    spec = importlib.util.spec_from_loader(loader.name, loader)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import {SCRIPT}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


logos = load_script()


class LogosMaterializerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.config = json.loads((ROOT / "benchmarks/core/ingestion.json").read_text())
        cls.exporter = logos.load_exporter()
        cls.baseline = json.loads(BASELINE.read_text())["files"]

    def test_production_frontend_has_no_external_solver_dependency(self) -> None:
        source = SCRIPT.read_text()
        for forbidden in (
            "materialize_nonwetune_sqlsolver",
            "materialize_wetune_sqlsolver",
            "solver_frontend",
            "sqlsolver-preflight",
        ):
            self.assertNotIn(forbidden, source)

    def test_dispatcher_routes_logos_to_its_own_root(self) -> None:
        namespace = runpy.run_path(str(DISPATCHER))
        args = argparse.Namespace(
            tool="logos",
            target="nonwetune",
            force=True,
            benchmark=["rbot-dsb", "rbot-tpch"],
            case=["query075"],
            limit=1,
            skip_parser=False,
            verify_non_rbot_baseline=False,
        )
        output = Path("/tmp/logos-materializer-dispatch-test")
        commands = namespace["build_commands"](args, output)
        self.assertEqual(len(commands), 1)
        command = commands[0]
        self.assertIn(str(HERE / "materialize_logos.py"), command)
        self.assertIn(str(output / "logos"), command)
        self.assertNotIn("sqlsolver-preflight", " ".join(command))

    def test_rbot_preserves_quoted_year_and_binds_every_exact_input(self) -> None:
        benchmark = next(
            row for row in self.config["benchmarks"] if row["id"] == "rbot-dsb"
        )
        case = next(
            row
            for row in self.exporter.iter_cases(self.config, benchmark)
            if row.case_id == "query075"
        )
        manifest, manifest_cases = logos.load_rbot_manifest()
        with tempfile.TemporaryDirectory(prefix="logos-rbot-materializer-test-") as tmp:
            output = Path(tmp) / "nonwetune-flat"
            logos.materialize_rbot_case(
                self.config,
                case,
                output,
                manifest,
                manifest_cases,
            )
            generated = output / "rbot-dsb__query075"
            source = ROOT / "benchmarks/core/rbot/dsb/query075/query075_0.sql"
            target = ROOT / "benchmarks/core/rbot/dsb/query075/query075_1.sql"
            schema = ROOT / "benchmarks/core/rbot/dsb/create_tables.sql"
            self.assertEqual((generated / "sql1.sql").read_bytes(), source.read_bytes())
            self.assertEqual((generated / "sql2.sql").read_bytes(), target.read_bytes())
            self.assertEqual(
                (generated / "schema.sql").read_bytes(), schema.read_bytes()
            )
            self.assertIn(b'AS "year"', (generated / "sql1.sql").read_bytes())

            metadata = json.loads((generated / "metadata.json").read_text())
            self.assertEqual(metadata["profile"], "logos")
            contract = metadata["materializationContract"]
            self.assertEqual(contract["semanticPreservation"]["repairs"], [])
            self.assertTrue(
                contract["semanticPreservation"]["identifierDelimitersPreserved"]
            )
            for name, path in (
                ("schema", schema),
                ("source", source),
                ("target", target),
            ):
                digest = hashlib.sha256(path.read_bytes()).hexdigest()
                self.assertEqual(contract["inputs"][name]["inputSha256"], digest)
                self.assertEqual(contract["inputs"][name]["outputSha256"], digest)
                self.assertTrue(contract["inputs"][name]["unchanged"])

    def test_rbot_rejects_a_forged_manifest_digest(self) -> None:
        with tempfile.TemporaryDirectory(prefix="logos-rbot-manifest-test-") as tmp:
            forged = Path(tmp) / "rewrite-pairs.manifest.json"
            forged.write_bytes(logos.RBOT_MANIFEST.read_bytes() + b"\n")
            with self.assertRaisesRegex(
                logos.LogosMaterializationError, "manifest digest changed"
            ):
                logos.load_rbot_manifest(forged)

    def test_rbot_rejects_a_forged_input_digest(self) -> None:
        _manifest, cases = logos.load_rbot_manifest()
        row = dict(cases["rbot-dsb__query075"])
        source = logos.manifest_input_path(row, "source")
        row["sourceSha256"] = "0" * 64
        with self.assertRaisesRegex(logos.LogosMaterializationError, "digest mismatch"):
            logos.bound_manifest_bytes(source, row, "sourceSha256")

    def test_rbot_rejects_a_mutated_workload_schema(self) -> None:
        with tempfile.TemporaryDirectory(prefix="logos-rbot-schema-test-") as tmp:
            root = Path(tmp)
            schema = root / "dsb/create_tables.sql"
            schema.parent.mkdir(parents=True)
            schema.write_text("CREATE TABLE forged (value INTEGER);\n")
            with mock.patch.object(logos, "RBOT_ROOT", root):
                with self.assertRaisesRegex(
                    logos.LogosMaterializationError,
                    "schema digest changed from the frozen authority",
                ):
                    logos.bound_rbot_schema_bytes("dsb")

    def test_rbot_exporter_must_equal_the_complete_frozen_case_set(self) -> None:
        _manifest, cases = logos.load_rbot_manifest()
        logos.validate_rbot_exported_case_set(self.config, self.exporter, cases)

        def altered_exporter(*, missing: str | None = None, extra: bool = False):
            wrapper = mock.Mock()

            def iter_cases(config, benchmark):
                exported = list(self.exporter.iter_cases(config, benchmark))
                if missing is not None:
                    exported = [case for case in exported if case.case_id != missing]
                if extra and benchmark["id"] == "rbot-tpch":
                    forged = mock.Mock()
                    forged.case_id = "query-forged"
                    exported.append(forged)
                return exported

            wrapper.iter_cases.side_effect = iter_cases
            return wrapper

        for exporter in (
            altered_exporter(missing="query001"),
            altered_exporter(extra=True),
        ):
            with self.subTest(exporter=exporter):
                with self.assertRaisesRegex(
                    logos.LogosMaterializationError,
                    "differ from the frozen 59-case authority",
                ):
                    logos.validate_rbot_exported_case_set(
                        self.config, exporter, cases
                    )

    def test_frozen_tpcds_representative_regenerates_byte_exactly(self) -> None:
        benchmark = next(
            row for row in self.config["benchmarks"] if row["id"] == "tpcds-variants"
        )
        case = next(
            row
            for row in self.exporter.iter_cases(self.config, benchmark)
            if row.case_id == "query036"
        )
        with tempfile.TemporaryDirectory(
            prefix="logos-tpcds-materializer-test-"
        ) as tmp:
            output_root = Path(tmp)
            logos.materialize_legacy_non_rbot_case(
                self.config,
                case,
                output_root / "nonwetune-flat",
                self.exporter,
            )
            self.assert_case_hashes(
                output_root, "nonwetune-flat/tpcds-variants__query036"
            )

    def test_frozen_calcite_cast_is_shape_and_source_span_bound(self) -> None:
        benchmark = next(
            row for row in self.config["benchmarks"] if row["id"] == "verieql-calcite"
        )
        case = next(
            row
            for row in self.exporter.iter_cases(self.config, benchmark)
            if row.case_id == "calcite-133"
        )
        before = logos.materialize_frozen_calcite_integer_casts(
            case, "before", case.before_sql
        )
        after = logos.materialize_frozen_calcite_integer_casts(
            case, "after", case.after_sql
        )
        self.assertIn("CAST(NAME AS INTEGER)", before)
        self.assertIn("CAST(DEPT0.NAME AS INTEGER)", after)
        with self.assertRaisesRegex(
            logos.LogosMaterializationError, "authority SQL drift"
        ):
            logos.materialize_frozen_calcite_integer_casts(
                case, "before", case.before_sql.replace("NAME", "NAME_CHANGED", 1)
            )

        with tempfile.TemporaryDirectory(
            prefix="logos-calcite-materializer-test-"
        ) as tmp:
            output_root = Path(tmp)
            logos.materialize_legacy_non_rbot_case(
                self.config,
                case,
                output_root / "nonwetune-flat",
                self.exporter,
            )
            self.assert_case_hashes(
                output_root, "nonwetune-flat/verieql-calcite__calcite-133"
            )

    def test_frozen_wetune_representative_regenerates_byte_exactly(self) -> None:
        with tempfile.TemporaryDirectory(
            prefix="logos-wetune-materializer-test-"
        ) as tmp:
            output_root = Path(tmp)
            materialized, failed = logos.materialize_wetune_cases(
                config=self.config,
                output_dir=output_root / "wetune-issues",
                case_patterns=[re.compile(r"^4$")],
                limit=None,
            )
            self.assertEqual((materialized, failed), (1, 0))
            self.assert_case_hashes(output_root, "wetune-issues/4")

    def assert_case_hashes(self, output_root: Path, relative_case: str) -> None:
        for name in ("schema.sql", "sql1.sql", "sql2.sql", "metadata.json"):
            relative = f"{relative_case}/{name}"
            actual = hashlib.sha256((output_root / relative).read_bytes()).hexdigest()
            self.assertEqual(actual, self.baseline[relative], relative)


if __name__ == "__main__":
    unittest.main()
