#!/usr/bin/env python3
import importlib.util
import hashlib
import tempfile
import unittest
from importlib.machinery import SourceFileLoader
from pathlib import Path


SCRIPT = Path(__file__).with_name("export-benchmark-ir")
loader = SourceFileLoader("export_benchmark_ir", str(SCRIPT))
spec = importlib.util.spec_from_loader(loader.name, loader)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot import {SCRIPT}")
exporter = importlib.util.module_from_spec(spec)
spec.loader.exec_module(exporter)


class ExportBenchmarkIrIntegrityTests(unittest.TestCase):
    def test_force_failure_cannot_reuse_stale_pair_artifacts(self) -> None:
        config = {
            "defaults": {
                "adapter": "none",
                "semanticProfile": "test",
                "bagSemantics": True,
                "nullSemantics": "sql-three-valued",
            }
        }
        case = exporter.Case(
            benchmark={
                "id": "suite",
                "schemaScope": "pair",
            },
            case_id="case",
            schema_sql="CREATE TABLE t (x INTEGER);",
            before_sql="SELECT x FROM t",
            after_sql="SELECT x FROM t",
            constraints=[],
            feature_tags=[],
            source_metadata={},
        )
        with tempfile.TemporaryDirectory() as directory:
            output_root = Path(directory)
            case_dir = output_root / "suite" / "case"
            case_dir.mkdir(parents=True)
            for name in (
                "before.calcite-ir.json",
                "after.calcite-ir.json",
                "metadata.json",
            ):
                (case_dir / name).write_text("stale")

            original = exporter.run_frontend

            def fail_after(
                _config,
                _case,
                _schema_path,
                _sql_path,
                ir_path,
                side,
                _keep_intermediate,
            ):
                if side == "after":
                    raise RuntimeError("expected after-side failure")
                ir_path.write_text("fresh-before")

            exporter.run_frontend = fail_after
            try:
                with self.assertRaisesRegex(RuntimeError, "after-side failure"):
                    exporter.export_case(
                        config,
                        case,
                        output_root,
                        keep_intermediate=False,
                        force=True,
                    )
            finally:
                exporter.run_frontend = original

            self.assertFalse((case_dir / "before.calcite-ir.json").exists())
            self.assertFalse((case_dir / "after.calcite-ir.json").exists())
            self.assertFalse((case_dir / "metadata.json").exists())

    def test_metadata_write_failure_removes_both_fresh_ir_sides(self) -> None:
        config = {
            "defaults": {
                "adapter": "none",
                "semanticProfile": "test",
                "bagSemantics": True,
                "nullSemantics": "sql-three-valued",
            }
        }
        case = exporter.Case(
            benchmark={"id": "suite", "schemaScope": "pair"},
            case_id="case",
            schema_sql="CREATE TABLE t (x INTEGER);",
            before_sql="SELECT x FROM t",
            after_sql="SELECT x FROM t",
            constraints=[],
            feature_tags=[],
            source_metadata={},
        )
        with tempfile.TemporaryDirectory() as directory:
            output_root = Path(directory)
            case_dir = output_root / "suite" / "case"
            original_frontend = exporter.run_frontend
            original_write_text = exporter.write_text

            def emit_ir(
                _config,
                _case,
                _schema_path,
                _sql_path,
                ir_path,
                side,
                _keep_intermediate,
            ):
                ir_path.write_text(f"fresh-{side}")

            def fail_metadata(path, value):
                if Path(path).name == "metadata.json":
                    raise OSError("expected metadata write failure")
                return original_write_text(path, value)

            exporter.run_frontend = emit_ir
            exporter.write_text = fail_metadata
            try:
                with self.assertRaisesRegex(OSError, "metadata write failure"):
                    exporter.export_case(
                        config,
                        case,
                        output_root,
                        keep_intermediate=False,
                        force=True,
                    )
            finally:
                exporter.run_frontend = original_frontend
                exporter.write_text = original_write_text

            self.assertFalse((case_dir / "before.calcite-ir.json").exists())
            self.assertFalse((case_dir / "after.calcite-ir.json").exists())
            self.assertFalse((case_dir / "metadata.json").exists())

    def test_tsql_date_day_patch_requires_exact_paired_predicate_sites(self) -> None:
        before = (
            "SELECT * FROM d WHERE x BETWEEN CAST('1998-08-04' AS DATE) "
            "AND (CAST('1998-08-04' AS DATE) + 14 days)"
        )
        after = (
            "SELECT * FROM d WHERE x BETWEEN CAST('1998-08-04' AS DATE) "
            "AND (CAST('1998-08-04' AS DATE) + 14)"
        )
        case = exporter.Case(
            benchmark={
                "id": "tpcds-variants",
                "readDialect": "tsql",
                "sourceDialect": "tsql_like",
            },
            case_id="query005",
            schema_sql="CREATE TABLE d (x DATE);",
            before_sql=before,
            after_sql=after,
            constraints=[],
            feature_tags=[],
            source_metadata={},
        )

        patched_before, patched_after, report = exporter.patch_tsql_date_day_pair(case)

        expected = after.replace(
            "CAST('1998-08-04' AS DATE) + 14",
            "CAST('1998-08-04' AS DATE) + INTERVAL '14' DAY",
        )
        self.assertEqual(patched_before, expected)
        self.assertEqual(patched_after, expected)
        self.assertEqual(report["kind"], "paired-tsql-between-date-day-unit")
        self.assertEqual(report["occurrencesPerSide"], 1)
        self.assertNotEqual(
            report["sourceSha256"]["before"],
            report["frontendInputSha256"]["before"],
        )
        self.assertEqual(
            report["frontendInputSha256"]["before"],
            hashlib.sha256(exporter.ensure_sql_terminated(expected).encode()).hexdigest(),
        )

    def test_tsql_date_day_patch_rejects_aliases_and_pair_mismatches(self) -> None:
        safe_before = (
            "SELECT * FROM d WHERE x BETWEEN CAST('1998-08-04' AS DATE) "
            "AND (CAST('1998-08-04' AS DATE) + 14 days)"
        )
        safe_after = (
            "SELECT * FROM d WHERE x BETWEEN CAST('1998-08-04' AS DATE) "
            "AND (CAST('1998-08-04' AS DATE) + 14)"
        )
        rejected = (
            ("SELECT 1 + 14 days", "SELECT 1 + 14"),
            (safe_before, safe_after.replace("+ 14", "+ 15")),
            (safe_before, safe_before),
            (
                safe_before + " OR " + safe_after.removeprefix("SELECT * FROM d WHERE "),
                safe_after + " OR " + safe_after.removeprefix("SELECT * FROM d WHERE "),
            ),
            (
                "-- " + safe_before + "\nSELECT 1",
                "-- " + safe_after + "\nSELECT 1",
            ),
            (
                "SELECT '" + safe_before.replace("'", "''") + "'",
                "SELECT '" + safe_after.replace("'", "''") + "'",
            ),
            (
                "SELECT [BETWEEN CAST('1998-08-04' AS DATE) "
                "AND (CAST('1998-08-04' AS DATE) + 14 days)] FROM d",
                "SELECT [BETWEEN CAST('1998-08-04' AS DATE) "
                "AND (CAST('1998-08-04' AS DATE) + 14)] FROM d",
            ),
            (
                "-- BETWEEN CAST('1998-08-04' AS DATE)\n"
                "AND (CAST('1998-08-04' AS DATE) + 14 days)",
                "-- BETWEEN CAST('1998-08-04' AS DATE)\n"
                "AND (CAST('1998-08-04' AS DATE) + 14)",
            ),
        )
        for before, after in rejected:
            with self.subTest(before=before, after=after):
                case = exporter.Case(
                    benchmark={
                        "id": "tpcds-variants",
                        "readDialect": "tsql",
                        "sourceDialect": "tsql_like",
                    },
                    case_id="query",
                    schema_sql="CREATE TABLE d (x DATE);",
                    before_sql=before,
                    after_sql=after,
                    constraints=[],
                    feature_tags=[],
                    source_metadata={},
                )
                actual_before, actual_after, report = (
                    exporter.patch_tsql_date_day_pair(case)
                )
                self.assertEqual((actual_before, actual_after), (before, after))
                self.assertIsNone(report)


if __name__ == "__main__":
    unittest.main()
