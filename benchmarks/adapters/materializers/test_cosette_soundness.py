#!/usr/bin/env python3
import json
import sys
import tempfile
import unittest
from pathlib import Path


MATERIALIZERS = Path(__file__).resolve().parent
if str(MATERIALIZERS) not in sys.path:
    sys.path.insert(0, str(MATERIALIZERS))

import materialize_cosette as cosette  # noqa: E402


class CosetteSoundnessTests(unittest.TestCase):
    def test_risky_sql_is_preserved_and_flagged_instead_of_rewritten(self) -> None:
        cases = (
            ("SELECT CAST(2147483648 AS INTEGER)", "CAST expressions"),
            ("SELECT 2147483647 + 1", "Integer arithmetic"),
            ("SELECT CASE WHEN TRUE THEN 1 ELSE 2 END", "CASE expressions"),
            ("SELECT id FROM t ORDER BY 1 / 0", "ORDER BY is unsupported"),
            ("SELECT id FROM t WHERE id IN (1, 2)", "IN predicates"),
        )
        for sql, blocker in cases:
            with self.subTest(sql=sql):
                result = cosette.materialize_query(sql)
                self.assertEqual(result.sql, sql)
                self.assertTrue(
                    any(blocker in message for message in result.blockers),
                    result.blockers,
                )

    def test_wildcards_are_not_mistaken_for_integer_arithmetic(self) -> None:
        for sql in ("SELECT * FROM t", "SELECT t.* FROM t"):
            with self.subTest(sql=sql):
                result = cosette.materialize_query(sql)
                self.assertEqual(result.sql, sql)
                self.assertFalse(
                    any("Integer arithmetic" in message for message in result.blockers),
                    result.blockers,
                )

    def test_parser_schema_constraints_are_semantic_profile_blockers(self) -> None:
        blockers = cosette.detect_authoritative_constraint_blockers(
            {"constraints": []},
            "CREATE TABLE t (id INTEGER NOT NULL, PRIMARY KEY (id));",
        )
        self.assertTrue(any("parser-facing schema DDL" in item for item in blockers))

        protected_only = cosette.detect_authoritative_constraint_blockers(
            {"constraints": []},
            "CREATE TABLE t (note TEXT DEFAULT 'PRIMARY KEY (id)');",
        )
        self.assertFalse(protected_only)

    def test_materialized_case_reports_syntax_and_semantics_separately(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            case = root / "suite__case"
            target = root / "out"
            case.mkdir()
            (case / "schema.sql").write_text(
                "CREATE TABLE t (id INTEGER NOT NULL, PRIMARY KEY (id));\n"
            )
            (case / "sql1.sql").write_text("SELECT x.id FROM t AS x;\n")
            (case / "sql2.sql").write_text("SELECT x.id FROM t AS x;\n")
            (case / "metadata.json").write_text(
                json.dumps(
                    {
                        "constraints": [],
                        "nullSemantics": "cosette-null-free",
                    }
                )
            )

            compatibility = cosette.materialize_case(root, case, target)
            metadata = json.loads((target / "metadata.json").read_text())

            self.assertEqual(compatibility.syntax_compatibility, "compatible")
            self.assertEqual(
                compatibility.semantic_profile_compatibility,
                "flagged",
            )
            self.assertEqual(metadata["syntaxCompatibility"], "compatible")
            self.assertEqual(metadata["semanticProfileCompatibility"], "flagged")
            self.assertIn(
                "query q1 `SELECT x.id FROM t AS x`;",
                (target / "case.cos").read_text(),
            )


if __name__ == "__main__":
    unittest.main()
