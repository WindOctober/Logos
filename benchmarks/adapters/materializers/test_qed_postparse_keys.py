#!/usr/bin/env python3
import hashlib
import json
import sys
import tempfile
import unittest
from pathlib import Path


MATERIALIZERS = Path(__file__).resolve().parent
if str(MATERIALIZERS) not in sys.path:
    sys.path.insert(0, str(MATERIALIZERS))

import materialize_qed as qed  # noqa: E402


class QedPostParseKeyTests(unittest.TestCase):
    def test_parser_ddl_withholds_keys_but_attests_post_parse_keys(self) -> None:
        ddl, coverage = qed.render_qed_schema(
            """
            CREATE TABLE t (
              b INTEGER NOT NULL,
              a INTEGER NOT NULL,
              PRIMARY KEY (b),
              UNIQUE (a)
            );
            """,
            "SELECT DISTINCT a FROM t; SELECT DISTINCT b FROM t;",
            quote_identifiers=False,
        )

        self.assertNotRegex(ddl, r"(?i)\bPRIMARY\s+KEY\b|\bUNIQUE\s*\(")
        self.assertIn("NOT NULL", ddl)
        self.assertEqual(coverage["keyApplicationStage"], "post-parse-json")
        self.assertEqual(coverage["postParseKeys"], coverage["renderedKeys"])
        self.assertEqual(
            {(key["kind"], tuple(key["columns"])) for key in coverage["postParseKeys"]},
            {("primary", ("b",)), ("unique", ("a",))},
        )

    def test_repair_clears_parser_keys_and_injects_by_field_name(self) -> None:
        document = {
            "schemas": [
                {
                    "name": "t",
                    "fields": ["a", "b"],
                    "nullable": [False, False],
                    "key": [[0]],
                }
            ]
        }
        expected = [
            {"kind": "primary", "table": "t", "columns": ["b"]},
            {"kind": "unique", "table": "t", "columns": ["a"]},
        ]
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "qed.json"
            path.write_text(json.dumps(document))
            first = qed.repair_qed_json(path, expected_table_keys=expected)
            first_hash = hashlib.sha256(path.read_bytes()).hexdigest()
            second = qed.repair_qed_json(path, expected_table_keys=expected)
            second_hash = hashlib.sha256(path.read_bytes()).hexdigest()

            repaired = json.loads(path.read_text())
            self.assertEqual(repaired["schemas"][0]["key"], [[0], [1]])
            self.assertEqual(first, second)
            self.assertEqual(first_hash, second_hash)

    def test_repair_drops_pruned_table_and_column_conservatively(self) -> None:
        document = {
            "schemas": [
                {
                    "name": "present",
                    "fields": ["a"],
                    "nullable": [False],
                    "key": [],
                }
            ]
        }
        expected = [
            {"kind": "primary", "table": "present", "columns": ["missing"]},
            {"kind": "primary", "table": "absent", "columns": ["id"]},
        ]
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "qed.json"
            path.write_text(json.dumps(document))
            attestation = qed.repair_qed_json(path, expected_table_keys=expected)

        self.assertEqual(
            {drop["reason"] for drop in attestation["droppedKeys"]},
            {
                "qed-json-pruned-rendered-key-column",
                "qed-json-pruned-rendered-key-table",
            },
        )

    def test_repair_rejects_malformed_parser_key_field(self) -> None:
        document = {
            "schemas": [
                {
                    "name": "t",
                    "fields": ["id"],
                    "nullable": [False],
                    "key": "not-a-list",
                }
            ]
        }
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "qed.json"
            path.write_text(json.dumps(document))
            with self.assertRaises(qed.QedJsonRepairError):
                qed.repair_qed_json(path, expected_table_keys=[])


if __name__ == "__main__":
    unittest.main()
