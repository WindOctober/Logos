#!/usr/bin/env python3
import copy
import hashlib
import json
import sys
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest import mock


MATERIALIZERS = Path(__file__).resolve().parent
if str(MATERIALIZERS) not in sys.path:
    sys.path.insert(0, str(MATERIALIZERS))

import materialize_qed as qed  # noqa: E402


class QedPostParseKeyTests(unittest.TestCase):
    @staticmethod
    def complete_document(
        query0=None,
        query1=None,
        *,
        fields=None,
        types=None,
        keys=None,
    ):
        fields = fields or ["a"]
        types = types or ["INTEGER"]
        scan = {"scan": 0}
        return {
            "schemas": [
                {
                    "name": "t",
                    "fields": fields,
                    "types": types,
                    "nullable": [False] * len(fields),
                    "key": keys or [],
                }
            ],
            "queries": [query0 or scan, query1 or scan],
            "help": ["LogicalTableScan(table=[[Qed, t]])"] * 2,
        }

    @staticmethod
    def empty_coverage(applied=None):
        return {
            "compatibility": "exact",
            "policy": "test",
            "applied": applied or [],
            "omitted": [],
            "postParseKeys": [],
            "renderedKeys": [],
            "keyApplicationStage": "post-parse-json",
        }

    @staticmethod
    def source_star_report(*rewritten_queries, output_arity=None):
        queries = [
            (
                {
                    "status": "verified-source-top-level-unqualified-star",
                    "rewrittenSql": query,
                    "outputs": [],
                    "calciteValidation": {
                        "status": "verified-calcite-direct-output-provenance"
                    },
                }
                if isinstance(query, str)
                else None
            )
            for query in rewritten_queries
        ]
        report = {
            "status": "verified-source-star-provenance-pair",
            "starSideCount": sum(query is not None for query in queries),
            "queries": queries,
        }
        if output_arity is not None:
            report["outputArity"] = output_arity
        return report

    @staticmethod
    def write_calcite_ir(
        root: Path,
        side: str,
        *,
        row_type: list[dict],
        sql: str = "SELECT v FROM t",
    ) -> None:
        target = (
            root
            / "benchmarks/core/.generated/calcite-ir/bench/case"
            / f"{side}.calcite-ir.json"
        )
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(
            json.dumps(
                {
                    "schema": [
                        {
                            "name": "t",
                            "columns": [{"name": "v", "type": "VARCHAR"}],
                        }
                    ],
                    "queries": [
                        {
                            "sql": sql,
                            "rel": {"rowType": row_type},
                        }
                    ],
                }
            )
        )

    def test_calcite_output_attestation_preserves_typmods(self) -> None:
        before = {
            "name": "v",
            "type": "VARCHAR",
            "nullable": True,
            "precision": 8,
        }
        after = {**before, "nullable": False, "precision": 9}
        table = qed.Table(
            "t",
            [qed.Column("v", "VARCHAR(255)", False)],
        )
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.write_calcite_ir(root, "before", row_type=[before])
            self.write_calcite_ir(root, "after", row_type=[after])
            with mock.patch.object(qed, "ROOT", root), self.assertRaisesRegex(
                qed.QedJsonValidationError,
                "ordered Calcite output signatures disagree",
            ):
                qed.load_qed_calcite_output_attestation(
                    "bench",
                    "case",
                    ["SELECT v FROM t", "SELECT v FROM t"],
                    [table],
                )

            after["precision"] = 8
            self.write_calcite_ir(root, "after", row_type=[after])
            with mock.patch.object(qed, "ROOT", root):
                attestation = qed.load_qed_calcite_output_attestation(
                    "bench",
                    "case",
                    ["SELECT v FROM t", "SELECT v FROM t"],
                    [table],
                )

        self.assertTrue(attestation["orderedTypesEqual"])
        self.assertEqual(
            attestation["sourceOutputSignature"],
            [
                {
                    "nullable": True,
                    "precision": 8,
                    "type": "VARCHAR",
                }
            ],
        )
        self.assertEqual(
            attestation["sides"][1]["outputSignature"][0]["nullable"],
            False,
        )

    def test_projected_calcite_binding_uses_raw_types_and_ir_name_order(self) -> None:
        raw = qed.build_qed_source_schema_type_authority(
            "CREATE TABLE t (id INTEGER, dead CHAR(4));"
        )
        projected = [qed.Table("t", [qed.Column("id", "INTEGER", False)])]
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            case = root / "benchmarks/core/.generated/calcite-ir/bench/case"
            case.mkdir(parents=True)
            for side in ("before", "after"):
                (case / f"{side}.calcite-ir.json").write_text(
                    json.dumps(
                        {
                            # Simulate the clean Java frontend reporting a raw
                            # CHAR declaration as VARCHAR. Names/order remain
                            # useful; this inferred family is not authority.
                            "schema": [
                                {
                                    "name": "t",
                                    "columns": [
                                        {"name": "id", "type": "INTEGER"},
                                        {"name": "dead", "type": "VARCHAR"},
                                    ],
                                }
                            ],
                            "queries": [
                                {
                                    "sql": "SELECT id FROM t",
                                    "rel": {
                                        "rowType": [
                                            {
                                                "name": "id",
                                                "type": "INTEGER",
                                                "nullable": True,
                                            }
                                        ]
                                    },
                                }
                            ],
                        }
                    )
                )
            with mock.patch.object(qed, "ROOT", root):
                attestation = qed.load_qed_calcite_output_attestation(
                    "bench",
                    "case",
                    ["SELECT id FROM t", "SELECT id FROM t"],
                    projected,
                    raw_source_schema_authority=raw,
                )

        self.assertEqual(
            attestation["schemaTypeAuthority"], "digest-bound-raw-source-ddl"
        )
        self.assertEqual(
            attestation["sides"][0]["schemaBindingPolicy"],
            "raw-source-type-digest-plus-exact-ir-name-order",
        )

    def test_materializer_rejects_raw_multi_statement_query_sides(self) -> None:
        config = {
            "defaults": {
                "adapter": "sqlglot",
                "semanticProfile": "postgres",
                "bagSemantics": "bag",
                "nullSemantics": "three-valued",
            }
        }
        case = SimpleNamespace(
            benchmark={
                "id": "bench",
                "adapter": "sqlglot",
                "schemaScope": "per-case",
                "constraintScope": "none",
            },
            case_id="multi",
            before_sql="SELECT id FROM t; SELECT id FROM t;",
            after_sql="SELECT id FROM t; SELECT id FROM t;",
            schema_sql="CREATE TABLE t (id INTEGER);",
            constraints=[],
            read_dialect=None,
            source_dialect=None,
            source_metadata={},
            feature_tags=[],
        )
        with tempfile.TemporaryDirectory() as directory, mock.patch.object(
            qed, "normalize_query"
        ) as normalize, mock.patch.object(qed, "run_qed_parser") as parser:
            output = Path(directory)
            status = qed.materialize_case(config, case, output, skip_parser=False)
            metadata_path = next(output.rglob("metadata.json"))
            metadata = json.loads(metadata_path.read_text())

        normalize.assert_not_called()
        parser.assert_not_called()
        self.assertEqual(status, "parser-error")
        self.assertEqual(
            metadata["parserProblem"]["kind"],
            "multi-statement-query-side",
        )
        self.assertEqual(
            metadata["qedPairStatementAttestation"]["rawStatementCounts"],
            {"before": 2, "after": 2},
        )
        self.assertEqual(
            metadata["qedPairStatementAttestation"]["status"],
            "unsupported-multi-statement-query-side",
        )
        self.assertIsNone(metadata["qedEquivalenceFallback"])

    def test_all_fallback_creators_reject_four_query_packaging(self) -> None:
        sql = (
            "CREATE TABLE t (id INTEGER); "
            "SELECT id FROM t; SELECT id FROM t; "
            "SELECT id FROM t; SELECT id FROM t;"
        )
        with tempfile.TemporaryDirectory() as directory, mock.patch.object(
            qed, "analyze_qed_projection_dependencies"
        ) as projection_analyzer, mock.patch.object(
            qed, "analyze_qed_opaque_string_abstraction"
        ) as opaque_analyzer, mock.patch.object(
            qed, "load_qed_calcite_output_attestation"
        ) as authority:
            root = Path(directory)
            source = root / "qed.sql"
            source.write_text(sql)
            creators = {
                "projection": lambda: qed.create_qed_projection_equivalence_fallback(
                    source,
                    root / "projection.sql",
                    self.empty_coverage(),
                ),
                "star": lambda: qed.create_qed_star_expansion_equivalence_fallback(
                    source,
                    root / "star.sql",
                    self.empty_coverage(),
                    "bench",
                    "case",
                ),
                "opaque": lambda: qed.create_qed_opaque_string_equivalence_fallback(
                    source,
                    root / "opaque.sql",
                    self.empty_coverage(),
                    "bench",
                    "case",
                ),
            }
            for name, create in creators.items():
                with self.subTest(name=name), self.assertRaisesRegex(
                    qed.QedJsonValidationError,
                    "exactly two non-DDL query statements; found 4",
                ):
                    create()

        projection_analyzer.assert_not_called()
        opaque_analyzer.assert_not_called()
        authority.assert_not_called()

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

    def test_complete_json_validation_attests_full_select_star_signature(self) -> None:
        document = self.complete_document(
            fields=["a", "payload", "marker"],
            types=["INTEGER", "VARCHAR", "BOOLEAN"],
        )
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "qed.json"
            path.write_text(json.dumps(document))
            attestation = qed.validate_qed_json(path)

        self.assertEqual(attestation["queryCount"], 2)
        self.assertEqual(attestation["outputArity"], 3)
        self.assertEqual(attestation["outputTypes"], ["INTEGER", "VARCHAR", "BOOLEAN"])

    def test_complete_json_validation_rejects_partial_or_mismatched_pair(self) -> None:
        one_query = self.complete_document()
        one_query["queries"] = one_query["queries"][:1]
        one_query["help"] = one_query["help"][:1]
        mismatched = self.complete_document(
            query1={
                "project": {
                    "source": {"scan": 0},
                    "target": [{"column": 0, "type": "VARCHAR"}],
                }
            }
        )
        for name, document in (("one", one_query), ("mismatch", mismatched)):
            with self.subTest(name=name), tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / "qed.json"
                path.write_text(json.dumps(document))
                with self.assertRaises(qed.QedJsonValidationError):
                    qed.validate_qed_json(path)

    def test_complete_json_validation_handles_semi_join_left_row_type(self) -> None:
        semi = {
            "join": {
                "kind": "SEMI",
                "left": {"scan": 0},
                "right": {"scan": 0},
                "condition": {"operator": "true", "operand": [], "type": "BOOLEAN"},
            }
        }
        document = self.complete_document(query0=semi, query1={"scan": 0})
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "qed.json"
            path.write_text(json.dumps(document))
            attestation = qed.validate_qed_json(path)

        self.assertEqual(attestation["outputArity"], 1)

    def test_complete_json_validation_rejects_missing_filter_join_or_sort_fields(
        self,
    ) -> None:
        malformed = {
            "filter": {"filter": {"source": {"scan": 0}}},
            "join": {
                "join": {
                    "kind": "INNER",
                    "left": {"scan": 0},
                    "right": {"scan": 0},
                }
            },
            "sort": {
                "sort": {
                    "source": {"scan": 0},
                    "collation": [],
                    "offset": None,
                }
            },
        }
        for name, relation in malformed.items():
            with self.subTest(name=name), tempfile.TemporaryDirectory() as directory:
                document = self.complete_document(query0=relation)
                path = Path(directory) / "qed.json"
                path.write_text(json.dumps(document))
                with self.assertRaises(qed.QedJsonValidationError):
                    qed.validate_qed_json(path)

    def test_valid_fresh_json_turns_racket_failure_into_warning(self) -> None:
        status = {
            "artifactsClearedBeforeRun": True,
            "jsonValidation": {"status": "verified-complete-query-pair"},
            "stderrTail": (
                "java.lang.UnsupportedOperationException: "
                "Not implemented: LogicalIntersect"
            ),
        }

        self.assertIsNone(qed.classify_qed_parser_problem(status))
        self.assertEqual(
            qed.classify_qed_parser_warning(status)["kind"],
            "post-json-racket-export-warning",
        )

    def test_varchar_relaxation_keeps_every_column_and_only_drops_constraint(
        self,
    ) -> None:
        ddl = """
            CREATE TABLE t (
              id INTEGER NOT NULL,
              label VARCHAR(40) NOT NULL,
              payload INTEGER
            );
        """
        exact, _ = qed.render_qed_schema(ddl, "SELECT * FROM t;", False)
        relaxed, coverage = qed.render_qed_schema(
            ddl,
            "SELECT * FROM t;",
            False,
            relax_not_null_varchar=True,
        )

        self.assertIn("id INTEGER NOT NULL", relaxed)
        self.assertIn("label VARCHAR(255)", relaxed)
        self.assertNotIn("label VARCHAR(255) NOT NULL", relaxed)
        self.assertEqual(exact.count("\n  "), relaxed.count("\n  "))
        self.assertEqual(coverage["equivalenceOnlyRelaxation"]["acceptedResult"], "EQ")

    def test_keyless_variant_preserves_queries_and_full_output(self) -> None:
        document = self.complete_document(
            fields=["id", "payload"],
            types=["INTEGER", "VARCHAR"],
            keys=[[0]],
        )
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "qed.json"
            target = Path(directory) / "qed-equivalence-keyless.json"
            source.write_text(json.dumps(document))
            attestation = qed.write_qed_keyless_equivalence_variant(source, target)
            keyless = json.loads(target.read_text())

        self.assertTrue(attestation["changed"])
        self.assertEqual(attestation["outputArity"], 2)
        self.assertEqual(keyless["queries"], document["queries"])
        self.assertEqual(keyless["schemas"][0]["fields"], ["id", "payload"])
        self.assertEqual(keyless["schemas"][0]["key"], [])

    def test_reusable_json_is_bound_to_source_and_variant_sql_digests(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "qed.sql"
            variant = root / "qed-equivalence-projected.sql"
            source.write_text("SELECT * FROM t; SELECT * FROM t;")
            variant.write_text("SELECT t.a FROM t; SELECT t.a FROM t;")
            metadata = {
                "qedInput": source.name,
                "qedInputSha256": qed.sha256_path(source),
                "qedProjectionEquivalenceFallback": {
                    "id": "ast-column-projected-equivalence",
                    "input": variant.name,
                    "inputSha256": qed.sha256_path(variant),
                    "sourceInput": source.name,
                    "sourceInputSha256": qed.sha256_path(source),
                    "resultPolicy": "accept-eq-only",
                },
            }
            metadata_path = root / "metadata.json"
            metadata_path.write_text(json.dumps(metadata))

            binding = qed.validate_qed_input_bindings(
                metadata_path,
                "ast-column-projected-equivalence",
            )
            self.assertEqual(binding["variant"]["input"], variant.name)
            source.write_text("SELECT 1; SELECT 1;")
            with self.assertRaisesRegex(qed.QedJsonValidationError, "digest"):
                qed.validate_qed_input_bindings(
                    metadata_path,
                    "ast-column-projected-equivalence",
                )

    def test_calcite_authority_binding_rejects_ir_byte_mutation(self) -> None:
        query = "SELECT * FROM t"
        row_type = [
            {
                "name": "v",
                "type": "VARCHAR",
                "nullable": True,
                "precision": 8,
            }
        ]
        with tempfile.TemporaryDirectory() as directory:
            workspace = Path(directory)
            case_dir = workspace / "case"
            case_dir.mkdir()
            source = case_dir / "qed.sql"
            variant = case_dir / "qed-equivalence-star-expanded.sql"
            source.write_text(
                "CREATE TABLE t (v VARCHAR(255));\n" "SELECT * FROM t; SELECT * FROM t;"
            )
            variant.write_text(
                "CREATE TABLE t (v VARCHAR(255));\n"
                "SELECT t.v FROM t; SELECT t.v FROM t;"
            )
            self.write_calcite_ir(
                workspace,
                "before",
                sql=query,
                row_type=row_type,
            )
            self.write_calcite_ir(
                workspace,
                "after",
                sql=query,
                row_type=row_type,
            )
            with mock.patch.object(qed, "ROOT", workspace):
                authority = qed.load_qed_calcite_output_attestation(
                    "bench",
                    "case",
                    [query, query],
                    [qed.Table("t", [qed.Column("v", "VARCHAR(255)", False)])],
                )
                source_star = self.source_star_report(
                    "SELECT t.v FROM t",
                    "SELECT t.v FROM t",
                    output_arity=1,
                )
                metadata_path = case_dir / "metadata.json"
                metadata_path.write_text(
                    json.dumps(
                        {
                            "sourceBenchmark": "bench",
                            "sourceCase": "case",
                            "qedInput": source.name,
                            "qedInputSha256": qed.sha256_path(source),
                            "qedStarExpansionEquivalenceFallback": {
                                "id": "ast-star-expanded-equivalence",
                                "input": variant.name,
                                "inputSha256": qed.sha256_path(variant),
                                "sourceInput": source.name,
                                "sourceInputSha256": qed.sha256_path(source),
                                "resultPolicy": "accept-eq-only",
                                "calciteAuthority": authority,
                                "expectedOutputTypes": ["VARCHAR"],
                                "sourceStarProvenance": source_star,
                            },
                        }
                    )
                )
                with mock.patch.object(
                    qed,
                    "analyze_qed_source_star_provenance",
                    return_value=copy.deepcopy(source_star),
                ):
                    qed.validate_qed_input_bindings(
                        metadata_path,
                        "ast-star-expanded-equivalence",
                    )
                ir_path = (
                    workspace / "benchmarks/core/.generated/calcite-ir/bench/case/"
                    "before.calcite-ir.json"
                )
                ir_path.write_text(ir_path.read_text() + "\n")
                with self.assertRaisesRegex(
                    qed.QedJsonValidationError,
                    "authority is stale",
                ):
                    qed.validate_qed_input_bindings(
                        metadata_path,
                        "ast-star-expanded-equivalence",
                    )

    def test_metadata_repair_synchronizes_active_fallback_coverage(self) -> None:
        document = self.complete_document(fields=["id"], types=["INTEGER"])
        coverage = self.empty_coverage()
        coverage["postParseKeys"] = [
            {"kind": "primary", "table": "missing", "columns": ["id"]}
        ]
        coverage["renderedKeys"] = list(coverage["postParseKeys"])
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            json_path = root / "qed.json"
            json_path.write_text(json.dumps(document))
            metadata_path = root / "metadata.json"
            metadata_path.write_text(
                json.dumps(
                    {
                        "activeQEDVariant": "ast-star-expanded-equivalence",
                        "constraintCoverage": coverage,
                        "qedStarExpansionEquivalenceFallback": {
                            "id": "ast-star-expanded-equivalence",
                            "constraintCoverage": coverage,
                        },
                    }
                )
            )
            qed.repair_qed_json(json_path, metadata_path)
            repaired = json.loads(metadata_path.read_text())

        self.assertEqual(
            repaired["constraintCoverage"],
            repaired["qedStarExpansionEquivalenceFallback"]["constraintCoverage"],
        )
        self.assertEqual(repaired["constraintCompatibility"], "conservative-relaxation")

    def test_tsql_day_alias_pair_is_repaired_only_with_exact_pair_attestation(
        self,
    ) -> None:
        before = (
            "SELECT 1 WHERE d BETWEEN CAST('1998-08-04' AS DATE) "
            "AND (CAST('1998-08-04' AS DATE) + 30 AS \"days\")"
        )
        after = (
            "SELECT 1 WHERE d BETWEEN CAST('1998-08-04' AS DATE) "
            "AND (CAST('1998-08-04' AS DATE) + 30)"
        )
        patched_before, patched_after, report = qed.patch_qed_tsql_date_day_pair(
            before,
            after,
            "SELECT 1 WHERE d BETWEEN CAST('1998-08-04' AS DATE) "
            "AND (CAST('1998-08-04' AS DATE) + 30 days)",
            "SELECT 1 WHERE d BETWEEN CAST('1998-08-04' AS DATE) "
            "AND (CAST('1998-08-04' AS DATE) + 30)",
            "tsql",
        )

        self.assertEqual(report["occurrencesPerQuery"], 1)
        self.assertIn("INTERVAL '30' DAY", patched_before)
        self.assertIn("INTERVAL '30' DAY", patched_after)
        self.assertNotIn('AS "days"', patched_before)

        untouched = qed.patch_qed_tsql_date_day_pair(
            before,
            after.replace("+ 30)", "+ 31)"),
            "SELECT 1 WHERE d BETWEEN CAST('1998-08-04' AS DATE) "
            "AND (CAST('1998-08-04' AS DATE) + 30 days)",
            "SELECT 1 WHERE d BETWEEN CAST('1998-08-04' AS DATE) "
            "AND (CAST('1998-08-04' AS DATE) + 31)",
            "tsql",
        )
        self.assertIsNone(untouched[2])
        self.assertEqual(untouched[0], before)

    def test_tsql_day_alias_pair_rejects_protected_predicate_lookalikes(self) -> None:
        source_before = (
            "SELECT 1 WHERE d BETWEEN CAST('1998-08-04' AS DATE) "
            "AND (CAST('1998-08-04' AS DATE) + 30 days)"
        )
        source_after = source_before.replace(" 30 days)", " 30)")
        normalized_predicate_before = (
            "BETWEEN CAST('1998-08-04' AS DATE) "
            "AND (CAST('1998-08-04' AS DATE) + 30 AS \"days\")"
        )
        normalized_predicate_after = normalized_predicate_before.replace(
            ' AS "days"', ""
        )
        protected_pairs = (
            (
                "SELECT [" + normalized_predicate_before + "] FROM d",
                "SELECT [" + normalized_predicate_after + "] FROM d",
                "SELECT [" + source_before + "] FROM d",
                "SELECT [" + source_after + "] FROM d",
            ),
            (
                "-- " + normalized_predicate_before + "\nSELECT 1",
                "-- " + normalized_predicate_after + "\nSELECT 1",
                source_before,
                source_after,
            ),
            (
                "SELECT $$" + normalized_predicate_before + "$$ AS payload",
                "SELECT $$" + normalized_predicate_after + "$$ AS payload",
                source_before,
                source_after,
            ),
        )

        for before, after, raw_before, raw_after in protected_pairs:
            with self.subTest(before=before):
                actual_before, actual_after, report = qed.patch_qed_tsql_date_day_pair(
                    before,
                    after,
                    raw_before,
                    raw_after,
                    "tsql",
                )
                self.assertEqual((actual_before, actual_after), (before, after))
                self.assertIsNone(report)

    def test_tsql_day_alias_pair_rejects_incomplete_unit_or_alias_side(self) -> None:
        source_site = (
            "d BETWEEN CAST('1998-08-04' AS DATE) "
            "AND (CAST('1998-08-04' AS DATE) + 30{unit})"
        )
        normalized_site = (
            "d BETWEEN CAST('1998-08-04' AS DATE) "
            "AND (CAST('1998-08-04' AS DATE) + 30{alias})"
        )
        source_plain = source_site.format(unit="")
        normalized_plain = normalized_site.format(alias="")
        normalized_alias = normalized_site.format(alias=' AS "days"')
        rejected = (
            # A side with only some `days` tokens is not a complete unit side.
            (
                "SELECT 1 WHERE "
                + source_site.format(unit=" days")
                + " OR "
                + source_plain,
                "SELECT 1 WHERE " + source_plain + " OR " + source_plain,
                "SELECT 1 WHERE " + normalized_alias + " OR " + normalized_plain,
                "SELECT 1 WHERE " + normalized_plain + " OR " + normalized_plain,
            ),
            # Even a complete source side is rejected if SQLGlot did not emit
            # the corresponding alias at every normalized site.
            (
                "SELECT 1 WHERE "
                + source_site.format(unit=" days")
                + " OR "
                + source_site.format(unit=" days"),
                "SELECT 1 WHERE " + source_plain + " OR " + source_plain,
                "SELECT 1 WHERE " + normalized_alias + " OR " + normalized_plain,
                "SELECT 1 WHERE " + normalized_plain + " OR " + normalized_plain,
            ),
        )

        for raw_before, raw_after, before, after in rejected:
            with self.subTest(raw_before=raw_before, before=before):
                actual_before, actual_after, report = qed.patch_qed_tsql_date_day_pair(
                    before,
                    after,
                    raw_before,
                    raw_after,
                    "tsql",
                )
                self.assertEqual((actual_before, actual_after), (before, after))
                self.assertIsNone(report)

    def test_tsql_day_alias_pair_requires_equal_date_bounds(self) -> None:
        raw_before = (
            "SELECT 1 WHERE d BETWEEN CAST('1998-08-04' AS DATE) "
            "AND (CAST('1998-08-05' AS DATE) + 30 days)"
        )
        raw_after = raw_before.replace(" 30 days)", " 30)")
        before = raw_before.replace(" 30 days)", ' 30 AS "days")')
        after = raw_after

        actual_before, actual_after, report = qed.patch_qed_tsql_date_day_pair(
            before,
            after,
            raw_before,
            raw_after,
            "tsql",
        )

        self.assertEqual((actual_before, actual_after), (before, after))
        self.assertIsNone(report)

    def test_tsql_day_alias_pair_preserves_protected_lookalike_next_to_real_site(
        self,
    ) -> None:
        source_before = (
            "SELECT 1 WHERE d BETWEEN CAST('1998-08-04' AS DATE) "
            "AND (CAST('1998-08-04' AS DATE) + 30 days)"
        )
        source_after = source_before.replace(" 30 days)", " 30)")
        normalized_before = source_before.replace(" 30 days)", ' 30 AS "days")')
        normalized_after = source_after
        fake = (
            "BETWEEN CAST('1999-01-01' AS DATE) "
            "AND (CAST('1999-01-01' AS DATE) + 99)"
        )
        before = normalized_before + " /* " + fake + " */"
        after = normalized_after + " /* " + fake + " */"

        patched_before, patched_after, report = qed.patch_qed_tsql_date_day_pair(
            before,
            after,
            source_before,
            source_after,
            "tsql",
        )

        self.assertIsNotNone(report)
        self.assertIn("INTERVAL '30' DAY", patched_before)
        self.assertIn("INTERVAL '30' DAY", patched_after)
        self.assertTrue(patched_before.endswith("/* " + fake + " */"))
        self.assertTrue(patched_after.endswith("/* " + fake + " */"))

    def test_set_null_type_repair_is_typed_and_idempotently_attested(self) -> None:
        column_project = {
            "project": {
                "source": {"scan": 0},
                "target": [{"column": 0, "type": "VARCHAR"}],
            }
        }
        null_project = {
            "project": {
                "source": {"scan": 0},
                "target": [{"operator": "NULL", "operand": [], "type": "NULL"}],
            }
        }
        document = self.complete_document(
            query0={"union": [column_project, null_project]},
            query1=column_project,
            fields=["payload"],
            types=["VARCHAR"],
        )
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "qed.json"
            path.write_text(json.dumps(document))
            first = qed.repair_qed_json(path, expected_table_keys=[])
            first_hash = hashlib.sha256(path.read_bytes()).hexdigest()
            second = qed.repair_qed_json(path, expected_table_keys=[])
            second_hash = hashlib.sha256(path.read_bytes()).hexdigest()
            repaired = json.loads(path.read_text())

        self.assertEqual(
            repaired["queries"][0]["union"][1]["project"]["target"][0]["type"],
            "VARCHAR",
        )
        self.assertEqual(first["setNullTypeRepairs"], second["setNullTypeRepairs"])
        self.assertEqual(first_hash, second_hash)

    def test_set_common_type_rejects_time_date_mixture(self) -> None:
        with self.assertRaises(qed.QedJsonValidationError):
            qed._qed_set_common_signature([["TIME"], ["DATE"]], "test.union")

    def test_raw_source_schema_authority_preserves_char_varchar_families(self) -> None:
        schema = """
            CREATE TABLE t (
              fixed CHAR(3) NOT NULL,
              varying CHARACTER VARYING(9),
              payload INTEGER
            );
        """
        authority = qed.build_qed_source_schema_type_authority(schema)
        columns = authority["tables"][0]["columns"]

        self.assertEqual(
            authority["schemaSha256"], hashlib.sha256(schema.encode()).hexdigest()
        )
        self.assertEqual(
            [(column["name"], column["typeFamily"]) for column in columns],
            [("fixed", "char"), ("varying", "varchar"), ("payload", "non-character")],
        )
        self.assertEqual(
            qed.normalize_type_for_qed(columns[0]["declaredType"]), "VARCHAR(255)"
        )
        self.assertEqual(
            qed.normalize_type_for_qed(columns[1]["declaredType"]), "VARCHAR(255)"
        )

    def test_base_use_closure_keeps_grouped_query_bytes_and_live_columns(self) -> None:
        tables = [
            qed.Table(
                "customer",
                [
                    qed.Column("c_custkey", "INTEGER", True),
                    qed.Column("dead_char", "VARCHAR(255)", True),
                ],
            ),
            qed.Table(
                "orders",
                [
                    qed.Column("o_orderkey", "INTEGER", True),
                    qed.Column("o_custkey", "INTEGER", True),
                    qed.Column("o_comment", "VARCHAR(255)", True),
                ],
            ),
        ]
        query = """
            SELECT c_count, COUNT(*) AS custdist
            FROM (
              SELECT c_custkey, COUNT(o_orderkey)
              FROM customer LEFT JOIN orders
                ON c_custkey = o_custkey
               AND o_comment NOT LIKE '%pending%accounts%'
              GROUP BY c_custkey
            ) AS c_orders(c_custkey, c_count)
            GROUP BY c_count
        """
        report = qed.analyze_qed_base_use_closure(tables, [query, query])

        self.assertTrue(report["queryBytesPreserved"])
        self.assertEqual(report["baseColumns"]["customer"], ["c_custkey"])
        self.assertEqual(
            set(report["baseColumns"]["orders"]),
            {"o_orderkey", "o_custkey", "o_comment"},
        )
        self.assertNotIn("dead_char", report["baseColumns"]["customer"])

    def test_live_raw_char_is_rejected_even_if_qed_calls_it_varchar(self) -> None:
        tables = [
            qed.Table(
                "item",
                [
                    qed.Column("id", "INTEGER", False),
                    qed.Column("category", "VARCHAR(255)", False),
                ],
            )
        ]
        raw = qed.build_qed_source_schema_type_authority(
            "CREATE TABLE item (id INTEGER, category CHAR(50));"
        )
        raw_tables = qed._align_qed_tables_with_raw_source_authority(tables, raw)
        closure = {
            "referencedTables": ["item"],
            "baseColumns": {"item": ["id", "category"]},
        }
        with self.assertRaisesRegex(
            qed.QedJsonValidationError,
            "live non-VARCHAR source column: item.category",
        ):
            qed._project_opaque_tables_to_live_base_columns(tables, raw_tables, closure)

    def test_dead_raw_char_projection_is_exact_and_live_char_fails_closed(self) -> None:
        tables = [
            qed.Table(
                "item",
                [
                    qed.Column("id", "INTEGER", False),
                    qed.Column("dead_fixed", "VARCHAR(255)", False),
                    qed.Column("live_varying", "VARCHAR(255)", False),
                ],
            )
        ]
        raw = qed.build_qed_source_schema_type_authority(
            "CREATE TABLE item ("
            "id INTEGER, dead_fixed CHAR(50), live_varying VARCHAR(50));"
        )
        raw_tables = qed._align_qed_tables_with_raw_source_authority(tables, raw)
        closure = {
            "referencedTables": ["item"],
            "baseColumns": {"item": ["id", "live_varying"]},
        }

        projected, report, retained = qed._project_opaque_tables_to_live_base_columns(
            tables,
            raw_tables,
            closure,
        )

        self.assertEqual(
            [column.name for column in projected[0].columns],
            ["id", "live_varying"],
        )
        self.assertEqual(retained, {"item": {"id", "live_varying"}})
        self.assertTrue(report["queryBytesPreserved"])
        self.assertTrue(report["bagMultiplicityPreserved"])
        self.assertEqual(
            report["omitted"],
            [
                {
                    "table": "item",
                    "column": "dead_fixed",
                    "sourceTypeFamily": "char",
                    "qedNormalizedType": "VARCHAR",
                }
            ],
        )

        live_char_closure = copy.deepcopy(closure)
        live_char_closure["baseColumns"]["item"].append("dead_fixed")
        with self.assertRaisesRegex(
            qed.QedJsonValidationError,
            "live non-VARCHAR source column: item.dead_fixed",
        ):
            qed._project_opaque_tables_to_live_base_columns(
                tables,
                raw_tables,
                live_char_closure,
            )

    def test_raw_schema_authority_replay_rejects_digest_drift(self) -> None:
        canonical = qed.build_qed_source_schema_type_authority(
            "CREATE TABLE t (v VARCHAR(9));"
        )
        stale = copy.deepcopy(canonical)
        stale["schemaSha256"] = "0" * 64
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "qed.sql").write_text(
                "CREATE TABLE t (v VARCHAR(255)); SELECT v FROM t; SELECT v FROM t;"
            )
            metadata = {
                "sourceBenchmark": "bench",
                "sourceCase": "case",
                "sourceSchemaTypeAuthority": stale,
                "qedInput": "qed.sql",
                "qedInputSha256": qed.sha256_path(root / "qed.sql"),
            }
            path = root / "metadata.json"
            path.write_text(json.dumps(metadata))
            with mock.patch.object(
                qed,
                "load_canonical_qed_source_schema_type_authority",
                return_value=canonical,
            ), self.assertRaisesRegex(
                qed.QedJsonValidationError,
                "raw source schema type authority is stale",
            ):
                qed.validate_qed_input_bindings(path)

    def test_ast_projection_never_truncates_top_level_star(self) -> None:
        sql = """
            CREATE TABLE t (
              id INTEGER NOT NULL,
              payload VARCHAR(255),
              marker BOOLEAN
            );
            SELECT * FROM t;
            SELECT * FROM t;
        """
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "qed.sql"
            target = Path(directory) / "qed-equivalence-projected.sql"
            source.write_text(sql)
            fallback = qed.create_qed_projection_equivalence_fallback(
                source, target, self.empty_coverage()
            )
            rendered = target.read_text()

        self.assertEqual(fallback["dependencyAttestation"]["outputArity"], 3)
        self.assertEqual(fallback["removedColumns"], [])
        for column in ("id", "payload", "marker"):
            self.assertIn(f'"{column}"', rendered)

    def test_ast_projection_preserves_query_text_without_derived_removal(self) -> None:
        sql = """
            CREATE TABLE t (
              id INTEGER,
              d DATE,
              dead VARCHAR(255)
            );
            SELECT id FROM t WHERE d > DATE '2000-01-01' + INTERVAL '3' DAY;
            SELECT id FROM t WHERE d > DATE '2000-01-01' + INTERVAL '3' DAY;
        """
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "qed.sql"
            target = Path(directory) / "qed-equivalence-projected.sql"
            source.write_text(sql)
            qed.create_qed_projection_equivalence_fallback(
                source, target, self.empty_coverage()
            )
            rendered = target.read_text()

        self.assertIn("INTERVAL '3' DAY", rendered)
        self.assertNotIn("INTERVAL '3 DAY'", rendered)

    def test_ast_projection_keeps_all_semantic_dependencies_and_witness(self) -> None:
        sql = """
            CREATE TABLE t (
              id INTEGER NOT NULL,
              join_id INTEGER,
              ord INTEGER,
              dead VARCHAR(255) NOT NULL
            );
            CREATE TABLE u (
              uid INTEGER,
              dead_u VARCHAR(255)
            );
            CREATE TABLE v (
              witness INTEGER,
              dead_v VARCHAR(255)
            );
            SELECT t.id
              FROM t JOIN u ON t.join_id = u.uid CROSS JOIN v
             WHERE EXISTS (SELECT 1 FROM u AS u2 WHERE u2.uid = t.id)
             GROUP BY t.id, t.ord
             ORDER BY t.ord;
            SELECT t.id
              FROM t JOIN u ON t.join_id = u.uid CROSS JOIN v
             WHERE EXISTS (SELECT 1 FROM u AS u2 WHERE u2.uid = t.id)
             GROUP BY t.id, t.ord
             ORDER BY t.ord;
        """
        applied = [
            {
                "kind": "not_null",
                "source": "test",
                "table": "t",
                "columns": ["dead"],
            }
        ]
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "qed.sql"
            target = Path(directory) / "qed-equivalence-projected.sql"
            source.write_text(sql)
            fallback = qed.create_qed_projection_equivalence_fallback(
                source, target, self.empty_coverage(applied)
            )

        self.assertEqual(fallback["dependencyAttestation"]["outputArity"], 1)
        self.assertEqual(
            set(fallback["dependencyAttestation"]["baseColumns"]["t"]),
            {"id", "join_id", "ord"},
        )
        self.assertEqual(fallback["dependencyAttestation"]["baseColumns"]["u"], ["uid"])
        self.assertEqual(
            fallback["cardinalityWitnessColumns"],
            [{"table": "v", "column": "witness"}],
        )
        self.assertIn(
            "constraint-column-outside-attested-dependency-closure",
            {
                entry.get("reason")
                for entry in fallback["constraintCoverage"]["omitted"]
            },
        )

    def test_ast_projection_fails_closed_on_ambiguous_column(self) -> None:
        tables = [
            qed.Table("t", [qed.Column("id", "INTEGER", False)]),
            qed.Table("u", [qed.Column("id", "INTEGER", False)]),
        ]
        with self.assertRaises(qed.QedJsonValidationError):
            qed.analyze_qed_projection_dependencies(
                tables,
                [
                    "SELECT id FROM t JOIN u ON t.id = u.id",
                    "SELECT id FROM t JOIN u ON t.id = u.id",
                ],
            )

    def test_ast_projection_rejects_whole_rows_and_natural_join(self) -> None:
        tables = [
            qed.Table(
                "t",
                [
                    qed.Column("id", "INTEGER", False),
                    qed.Column("payload", "VARCHAR(255)", False),
                ],
            ),
            qed.Table(
                "u",
                [
                    qed.Column("id", "INTEGER", False),
                    qed.Column("payload", "VARCHAR(255)", False),
                ],
            ),
        ]
        unsafe = (
            "SELECT t FROM t",
            "SELECT t IS NULL FROM t",
            "SELECT 1 FROM t NATURAL JOIN u",
            "SELECT t.* FROM t LEFT JOIN u USING (id)",
        )
        for query in unsafe:
            with self.subTest(query=query), self.assertRaises(
                qed.QedJsonValidationError
            ):
                qed.analyze_qed_projection_dependencies(tables, [query, query])

    def test_ast_projection_rewrites_only_dead_direct_derived_columns(self) -> None:
        sql = """
            CREATE TABLE EMP (
              EMPNO INTEGER NOT NULL,
              DEPTNO INTEGER NOT NULL,
              ENAME VARCHAR(255),
              JOB VARCHAR(255),
              SAL INTEGER
            );
            CREATE TABLE DEPT (
              DEPTNO INTEGER NOT NULL
            );
            SELECT DEPT.DEPTNO, EMP.EMPNO
              FROM DEPT RIGHT JOIN EMP ON DEPT.DEPTNO = EMP.DEPTNO
              OFFSET 2 ROWS FETCH NEXT 10 ROWS ONLY;
            SELECT DEPT0.DEPTNO, t1.EMPNO
              FROM DEPT AS DEPT0 RIGHT JOIN
                   (SELECT EMPNO, ENAME, JOB, SAL, DEPTNO FROM EMP
                    OFFSET 2 ROWS FETCH NEXT 10 ROWS ONLY) AS t1
                ON DEPT0.DEPTNO = t1.DEPTNO
              OFFSET 2 ROWS FETCH NEXT 10 ROWS ONLY;
        """
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "qed.sql"
            target = Path(directory) / "qed-equivalence-projected.sql"
            source.write_text(sql)
            fallback = qed.create_qed_projection_equivalence_fallback(
                source, target, self.empty_coverage()
            )
            rendered = target.read_text()

        self.assertNotIn('"ENAME"', rendered)
        self.assertNotIn('"JOB"', rendered)
        self.assertNotIn('"SAL"', rendered)
        self.assertIn('."EMPNO" AS "empno"', rendered)
        self.assertIn('."DEPTNO" AS "deptno"', rendered)
        removed = [
            item
            for query in fallback["dependencyAttestation"]["queries"]
            for item in query["projectionRewrite"]["removedSelections"]
        ]
        self.assertEqual({item["column"] for item in removed}, {"ENAME", "JOB", "SAL"})

    def test_ast_projection_does_not_erase_dangerous_expression(self) -> None:
        sql = """
            CREATE TABLE t (
              id INTEGER,
              divisor INTEGER,
              dead VARCHAR(255)
            );
            SELECT x.id FROM
              (SELECT id, dead, 1 / divisor AS dangerous FROM t) AS x;
            SELECT x.id FROM
              (SELECT id, dead, 1 / divisor AS dangerous FROM t) AS x;
        """
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "qed.sql"
            target = Path(directory) / "qed-equivalence-projected.sql"
            source.write_text(sql)
            with self.assertRaises(qed.QedJsonValidationError):
                qed.create_qed_projection_equivalence_fallback(
                    source, target, self.empty_coverage()
                )

    def test_projection_rejects_star_combined_with_nested_dead_column(self) -> None:
        sql = """
            CREATE TABLE t (id INTEGER, dead VARCHAR(255));
            CREATE TABLE u (id INTEGER);
            SELECT *
              FROM (SELECT id FROM (SELECT id, dead FROM t) AS inner_t) AS x
              JOIN u ON x.id = u.id;
            SELECT *
              FROM (SELECT id FROM (SELECT id, dead FROM t) AS inner_t) AS x
              JOIN u ON x.id = u.id;
        """
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "qed.sql"
            target = Path(directory) / "qed-equivalence-projected.sql"
            source.write_text(sql)
            with self.assertRaisesRegex(
                qed.QedJsonValidationError,
                "relational source star.*dead-column rewriting",
            ):
                qed.create_qed_projection_equivalence_fallback(
                    source,
                    target,
                    self.empty_coverage(),
                )

    def test_star_expansion_makes_source_output_order_explicit(self) -> None:
        sql = """
            CREATE TABLE EMP (
              EMPNO INTEGER,
              DEPTNO INTEGER,
              ENAME VARCHAR(255)
            );
            CREATE TABLE DEPT (
              DEPTNO INTEGER,
              NAME VARCHAR(255)
            );
            SELECT * FROM EMP LEFT JOIN DEPT ON EMP.DEPTNO = DEPT.DEPTNO;
            SELECT EMP.EMPNO, EMP.DEPTNO, EMP.ENAME,
                   DEPT.DEPTNO AS DEPTNO0, DEPT.NAME
              FROM EMP LEFT JOIN DEPT ON EMP.DEPTNO = DEPT.DEPTNO;
        """
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "qed-equivalence-relaxed.sql"
            target = Path(directory) / "qed-equivalence-star-expanded.sql"
            source.write_text(sql)
            source_star = self.source_star_report(
                "SELECT EMP.EMPNO, EMP.DEPTNO, EMP.ENAME, "
                "DEPT.DEPTNO, DEPT.NAME FROM EMP LEFT JOIN DEPT "
                "ON EMP.DEPTNO = DEPT.DEPTNO",
                None,
            )
            with mock.patch.object(
                qed,
                "load_qed_calcite_output_attestation",
                return_value={
                    "outputArity": 5,
                    "sourceOutputTypes": [
                        "INTEGER",
                        "INTEGER",
                        "VARCHAR",
                        "INTEGER",
                        "VARCHAR",
                    ],
                },
            ), mock.patch.object(
                qed,
                "analyze_qed_source_star_provenance",
                return_value=source_star,
            ):
                fallback = qed.create_qed_star_expansion_equivalence_fallback(
                    source,
                    target,
                    self.empty_coverage(),
                    "bench",
                    "case",
                )
            rendered = target.read_text()

        self.assertNotIn("SELECT *", rendered.upper())
        self.assertLess(rendered.index("EMP.EMPNO"), rendered.index("EMP.DEPTNO"))
        self.assertEqual(fallback["dependencyAttestation"]["outputArity"], 5)
        self.assertEqual(
            fallback["queryRewritePolicy"],
            "exact-source-span-root-star-expansion-only",
        )

    def test_star_expansion_attests_right_join_output_order(self) -> None:
        sql = """
            CREATE TABLE EMP (EMPNO INTEGER, DEPTNO INTEGER);
            CREATE TABLE DEPT (DEPTNO INTEGER, NAME VARCHAR(255));
            SELECT * FROM EMP RIGHT JOIN DEPT
              ON EMP.DEPTNO = DEPT.DEPTNO;
            SELECT * FROM (SELECT * FROM EMP) AS e RIGHT JOIN DEPT
              ON e.DEPTNO = DEPT.DEPTNO;
        """
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "qed.sql"
            target = Path(directory) / "qed-equivalence-star-expanded.sql"
            source.write_text(sql)
            source_star = self.source_star_report(
                "SELECT EMP.EMPNO, EMP.DEPTNO, DEPT.DEPTNO, DEPT.NAME "
                "FROM EMP RIGHT JOIN DEPT ON EMP.DEPTNO = DEPT.DEPTNO",
                "SELECT e.EMPNO, e.DEPTNO, DEPT.DEPTNO, DEPT.NAME "
                "FROM (SELECT * FROM EMP) AS e RIGHT JOIN DEPT "
                "ON e.DEPTNO = DEPT.DEPTNO",
            )
            with mock.patch.object(
                qed,
                "load_qed_calcite_output_attestation",
                return_value={
                    "outputArity": 4,
                    "sourceOutputTypes": [
                        "INTEGER",
                        "INTEGER",
                        "INTEGER",
                        "VARCHAR",
                    ],
                },
            ), mock.patch.object(
                qed,
                "analyze_qed_source_star_provenance",
                return_value=source_star,
            ):
                fallback = qed.create_qed_star_expansion_equivalence_fallback(
                    source,
                    target,
                    self.empty_coverage(),
                    "bench",
                    "case",
                )
            rendered = target.read_text()

        self.assertEqual(fallback["sourceStarProvenance"]["starSideCount"], 2)
        e_position = rendered.index("e.EMPNO")
        self.assertLess(
            e_position,
            rendered.index("DEPT.DEPTNO", e_position),
        )

    def test_star_expansion_attests_derived_left_inner_join_order(self) -> None:
        sql = """
            CREATE TABLE EMP (EMPNO INTEGER, DEPTNO INTEGER);
            CREATE TABLE DEPT (DEPTNO INTEGER, NAME VARCHAR(255));
            SELECT * FROM (SELECT * FROM EMP) AS e JOIN DEPT
              ON e.DEPTNO = DEPT.DEPTNO;
            SELECT * FROM (SELECT * FROM EMP) AS e JOIN DEPT
              ON e.DEPTNO = DEPT.DEPTNO;
        """
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "qed.sql"
            target = Path(directory) / "qed-equivalence-star-expanded.sql"
            source.write_text(sql)
            rewritten = (
                "SELECT e.EMPNO, e.DEPTNO, DEPT.DEPTNO, DEPT.NAME "
                "FROM (SELECT * FROM EMP) AS e JOIN DEPT "
                "ON e.DEPTNO = DEPT.DEPTNO"
            )
            source_star = self.source_star_report(rewritten, rewritten)
            with mock.patch.object(
                qed,
                "load_qed_calcite_output_attestation",
                return_value={
                    "outputArity": 4,
                    "sourceOutputTypes": [
                        "INTEGER",
                        "INTEGER",
                        "INTEGER",
                        "VARCHAR",
                    ],
                },
            ), mock.patch.object(
                qed,
                "analyze_qed_source_star_provenance",
                return_value=source_star,
            ):
                fallback = qed.create_qed_star_expansion_equivalence_fallback(
                    source,
                    target,
                    self.empty_coverage(),
                    "bench",
                    "case",
                )
        self.assertEqual(fallback["sourceStarProvenance"]["starSideCount"], 2)

    def test_star_expansion_attests_base_derived_base_order(self) -> None:
        sql = """
            CREATE TABLE A (id INTEGER);
            CREATE TABLE B (id INTEGER);
            CREATE TABLE C (id INTEGER);
            SELECT * FROM A
              JOIN (SELECT * FROM B) AS db ON A.id = db.id
              JOIN C ON db.id = C.id;
            SELECT * FROM A
              JOIN (SELECT * FROM B) AS db ON A.id = db.id
              JOIN C ON db.id = C.id;
        """
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "qed.sql"
            target = Path(directory) / "qed-equivalence-star-expanded.sql"
            source.write_text(sql)
            rewritten = (
                "SELECT A.id, db.id, C.id FROM A "
                "JOIN (SELECT * FROM B) AS db ON A.id = db.id "
                "JOIN C ON db.id = C.id"
            )
            source_star = self.source_star_report(rewritten, rewritten)
            with mock.patch.object(
                qed,
                "load_qed_calcite_output_attestation",
                return_value={
                    "outputArity": 3,
                    "sourceOutputTypes": ["INTEGER", "INTEGER", "INTEGER"],
                },
            ), mock.patch.object(
                qed,
                "analyze_qed_source_star_provenance",
                return_value=source_star,
            ):
                fallback = qed.create_qed_star_expansion_equivalence_fallback(
                    source,
                    target,
                    self.empty_coverage(),
                    "bench",
                    "case",
                )
        self.assertEqual(fallback["sourceStarProvenance"]["starSideCount"], 2)

    def test_star_validator_requires_authoritative_ordered_types(self) -> None:
        document = self.complete_document(fields=["id"], types=["INTEGER"])
        with tempfile.TemporaryDirectory() as directory:
            json_path = Path(directory) / "qed.json"
            json_path.write_text(json.dumps(document))
            with self.assertRaisesRegex(
                qed.QedJsonValidationError,
                "authoritative source signature",
            ):
                qed.validate_qed_star_expansion_result(
                    json_path,
                    {
                        "id": "ast-star-expanded-equivalence",
                        "dependencyAttestation": {"outputArity": 1},
                        "expectedOutputTypes": ["VARCHAR"],
                    },
                )

    def test_opaque_varchar_like_uses_nullable_uninterpreted_predicate(self) -> None:
        tables = [
            qed.Table(
                "orders",
                [
                    qed.Column("id", "INTEGER", False),
                    qed.Column("comment", "VARCHAR(255)", False),
                ],
            )
        ]
        query = "SELECT id FROM orders WHERE comment NOT LIKE '%pending%'"
        report = qed.analyze_qed_opaque_string_abstraction(tables, [query, query])

        self.assertEqual(
            report["declarations"],
            [
                "DECLARE SCALAR FUNCTION QED_VARCHAR_LIKE "
                "(INTEGER, INTEGER) RETURNS BOOLEAN"
            ],
        )
        self.assertIn(
            "NOT QED_VARCHAR_LIKE(comment, 1000000)",
            report["queries"][0]["transformedSql"],
        )
        self.assertEqual(report["queries"][0]["likeUdfRewrites"][0]["negated"], True)
        self.assertEqual(
            report["likeUdfAbstraction"]["semanticPolicy"],
            "arbitrary-nullable-uninterpreted-function",
        )

    def test_opaque_varchar_like_rejects_escape_and_ilike(self) -> None:
        tables = [
            qed.Table(
                "orders",
                [qed.Column("comment", "VARCHAR(255)", False)],
            )
        ]
        unsafe = (
            "SELECT 1 FROM orders WHERE comment LIKE 'x%' ESCAPE '!'",
            "SELECT 1 FROM orders WHERE comment ILIKE 'x%'",
            r"SELECT 1 FROM orders WHERE comment LIKE 'x\\%'",
            "SELECT 1 FROM orders WHERE comment LIKE comment",
        )
        for query in unsafe:
            with self.subTest(query=query), self.assertRaises(
                qed.QedJsonValidationError
            ):
                qed.analyze_qed_opaque_string_abstraction(tables, [query, query])

    def test_opaque_varchar_rejects_name_sorted_relational_star(self) -> None:
        tables = [
            qed.Table(
                "t",
                [
                    qed.Column("z", "VARCHAR(255)", False),
                    qed.Column("a", "VARCHAR(255)", False),
                ],
            )
        ]
        with self.assertRaisesRegex(
            qed.QedJsonValidationError,
            "explicit relational output list",
        ):
            qed.analyze_qed_opaque_string_abstraction(
                tables,
                ["SELECT * FROM t", "SELECT * FROM t"],
            )

    def test_opaque_nested_direct_base_star_is_safe_but_join_star_needs_bridge(
        self,
    ) -> None:
        tables = [
            qed.Table(
                "t",
                [
                    qed.Column("id", "INTEGER", False),
                    qed.Column("label", "VARCHAR(255)", False),
                ],
            )
        ]
        query = "SELECT d.label FROM (SELECT * FROM t) AS d"

        report = qed.analyze_qed_opaque_string_abstraction(
            tables,
            [query, query],
        )
        self.assertTrue(report["queries"][0]["sourceHadStar"])
        self.assertFalse(report["queries"][0]["sourceHadTopLevelStar"])
        self.assertTrue(report["queries"][0]["nestedStarsDirectBasePassThrough"])

        joined_tables = tables + [qed.Table("u", [qed.Column("id", "INTEGER", False)])]
        unsafe = "SELECT d.label FROM " "(SELECT * FROM t JOIN u ON t.id = u.id) AS d"
        with self.assertRaisesRegex(
            qed.QedJsonValidationError,
            "unattested nested relational star",
        ):
            qed.analyze_qed_opaque_string_abstraction(
                joined_tables,
                [unsafe, unsafe],
            )

        unsafe_aliases = (
            "SELECT d.label FROM " "(SELECT * FROM t AS x(id, label)) AS d",
            "SELECT d.label FROM " "(SELECT * FROM t) AS d(id, label)",
        )
        for unsafe_alias in unsafe_aliases:
            with self.subTest(query=unsafe_alias), self.assertRaisesRegex(
                qed.QedJsonValidationError,
                "unattested nested relational star",
            ):
                qed.analyze_qed_opaque_string_abstraction(
                    tables,
                    [unsafe_alias, unsafe_alias],
                )

        whole_row = "SELECT d FROM (SELECT * FROM t) AS d"
        with self.assertRaises(qed.QedJsonValidationError):
            qed.analyze_qed_opaque_string_abstraction(
                tables,
                [whole_row, whole_row],
            )

        duplicate_columns = [
            qed.Table(
                "t",
                [
                    qed.Column("label", "VARCHAR(255)", False),
                    qed.Column("LABEL", "VARCHAR(255)", False),
                ],
            )
        ]
        with self.assertRaisesRegex(
            qed.QedJsonValidationError,
            "duplicate column names",
        ):
            qed.analyze_qed_opaque_string_abstraction(
                duplicate_columns,
                [query, query],
            )

    def test_opaque_star_validator_rejects_same_typed_qed_permutation(self) -> None:
        direct = {
            "project": {
                "source": {"scan": 0},
                "target": [
                    {"column": 1, "type": "INTEGER"},
                    {"column": 0, "type": "INTEGER"},
                ],
            }
        }
        document = self.complete_document(
            query0=direct,
            query1=direct,
            fields=["A", "Z"],
            types=["INTEGER", "INTEGER"],
        )
        source_outputs = [
            {
                "sourceType": "VARCHAR",
                "origin": {
                    "scanOccurrence": 0,
                    "table": "t",
                    "column": "Z",
                    "columnOrdinal": 0,
                },
            },
            {
                "sourceType": "VARCHAR",
                "origin": {
                    "scanOccurrence": 0,
                    "table": "t",
                    "column": "A",
                    "columnOrdinal": 1,
                },
            },
        ]
        source_star = {
            "status": "verified-source-star-provenance-pair",
            "starSideCount": 2,
            "queries": [
                {"outputs": source_outputs},
                {"outputs": source_outputs},
            ],
        }
        fallback = {
            "expectedTransformedOutputTypes": ["INTEGER", "INTEGER"],
            "sourceStarProvenance": source_star,
        }
        with tempfile.TemporaryDirectory() as directory:
            json_path = Path(directory) / "qed.json"
            json_path.write_text(json.dumps(document))
            validation = qed.validate_qed_opaque_string_result(
                json_path,
                fallback,
            )
            self.assertEqual(
                validation["sourceStarProvenanceValidation"]["status"],
                "verified-qed-source-star-provenance-pair",
            )

            swapped = copy.deepcopy(document)
            for query in swapped["queries"]:
                query["project"]["target"] = [
                    {"column": 0, "type": "INTEGER"},
                    {"column": 1, "type": "INTEGER"},
                ]
            json_path.write_text(json.dumps(swapped))
            with self.assertRaisesRegex(
                qed.QedJsonValidationError,
                "provenance analysis failed",
            ):
                qed.validate_qed_opaque_string_result(json_path, fallback)

    def test_opaque_binding_rebuilds_and_compares_source_star_report(self) -> None:
        query = "SELECT * FROM t"
        row_type = [{"name": "v", "type": "VARCHAR", "nullable": True}]
        rebuilt_source_star = {
            "status": "verified-source-star-provenance-pair",
            "starSideCount": 2,
            "queries": [{"outputs": []}, {"outputs": []}],
        }
        with tempfile.TemporaryDirectory() as directory:
            workspace = Path(directory)
            case_dir = workspace / "case"
            case_dir.mkdir()
            source = case_dir / "qed.sql"
            variant = case_dir / "qed-equivalence-opaque-string.sql"
            source.write_text(
                "CREATE TABLE t (v VARCHAR(255));\n" "SELECT * FROM t; SELECT * FROM t;"
            )
            variant.write_text(
                "CREATE TABLE t (v INTEGER);\n" "SELECT t.v FROM t; SELECT t.v FROM t;"
            )
            self.write_calcite_ir(
                workspace,
                "before",
                sql=query,
                row_type=row_type,
            )
            self.write_calcite_ir(
                workspace,
                "after",
                sql=query,
                row_type=row_type,
            )
            raw_authority = qed.build_qed_source_schema_type_authority(
                "CREATE TABLE t (v VARCHAR(255));"
            )
            with mock.patch.object(qed, "ROOT", workspace):
                authority = qed.load_qed_calcite_output_attestation(
                    "bench",
                    "case",
                    [query, query],
                    [qed.Table("t", [qed.Column("v", "VARCHAR(255)", False)])],
                )
                metadata = {
                    "sourceBenchmark": "bench",
                    "sourceCase": "case",
                    "sourceSchemaTypeAuthority": raw_authority,
                    "sourceConstraintCoverage": self.empty_coverage(),
                    "qedInput": source.name,
                    "qedInputSha256": qed.sha256_path(source),
                    "qedOpaqueStringEquivalenceFallback": {
                        "id": "opaque-varchar-equality-integer-abstraction",
                        "input": variant.name,
                        "inputSha256": qed.sha256_path(variant),
                        "sourceInput": source.name,
                        "sourceInputSha256": qed.sha256_path(source),
                        "resultPolicy": "accept-eq-only",
                        "calciteAuthority": authority,
                        "expectedTransformedOutputTypes": ["INTEGER"],
                        "sourceStarProvenance": rebuilt_source_star,
                        "sourceSchemaTypeAuthority": raw_authority,
                        "sourceColumnUseClosure": None,
                        "sourceColumnProjection": None,
                        "constraintCoverage": self.empty_coverage(),
                    },
                }
                metadata_path = case_dir / "metadata.json"
                metadata_path.write_text(json.dumps(metadata))
                with mock.patch.object(
                    qed,
                    "load_canonical_qed_source_schema_type_authority",
                    return_value=raw_authority,
                ), mock.patch.object(
                    qed,
                    "analyze_qed_base_use_closure",
                    side_effect=qed.QedJsonValidationError(
                        "base-use closure does not admit a relational source star"
                    ),
                ), mock.patch.object(
                    qed,
                    "analyze_qed_source_star_provenance",
                    return_value=rebuilt_source_star,
                ):
                    qed.validate_qed_input_bindings(
                        metadata_path,
                        "opaque-varchar-equality-integer-abstraction",
                    )
                    metadata["qedOpaqueStringEquivalenceFallback"][
                        "sourceStarProvenance"
                    ] = {"tampered": True}
                    metadata_path.write_text(json.dumps(metadata))
                    with self.assertRaisesRegex(
                        qed.QedJsonValidationError,
                        "source-star provenance is stale",
                    ):
                        qed.validate_qed_input_bindings(
                            metadata_path,
                            "opaque-varchar-equality-integer-abstraction",
                        )

    def test_opaque_projection_binding_replays_and_rejects_attestation_drift(
        self,
    ) -> None:
        query = "SELECT v FROM t"
        source_ddl = "CREATE TABLE t (" "id INTEGER, dead_fixed CHAR(4), v VARCHAR(9));"
        qed_ddl = (
            "CREATE TABLE t (" "id INTEGER, dead_fixed VARCHAR(255), v VARCHAR(255));"
        )
        raw_authority = qed.build_qed_source_schema_type_authority(source_ddl)
        closure_query = {
            "inputSha256": hashlib.sha256(query.encode()).hexdigest(),
            "queryBytesPreserved": True,
            "outputArity": 1,
            "referencedTables": ["t"],
            "baseColumns": {"t": ["v"]},
        }
        base_use_closure = {
            "status": "verified-exact-base-column-use-closure",
            "sqlglotVersion": "test",
            "policy": "qualify-original-query-without-projection-or-rewrite",
            "queries": [closure_query, copy.deepcopy(closure_query)],
            "outputArity": 1,
            "queryBytesPreserved": True,
            "referencedTables": ["t"],
            "baseColumns": {"t": ["v"]},
        }
        no_source_star = {
            "status": "verified-source-star-provenance-pair",
            "starSideCount": 0,
            "queries": [None, None],
        }
        source_coverage = self.empty_coverage()

        with tempfile.TemporaryDirectory() as directory:
            workspace = Path(directory)
            case_dir = workspace / "case"
            case_dir.mkdir()
            source = case_dir / "qed.sql"
            variant = case_dir / "qed-equivalence-opaque-string.sql"
            source.write_text(qed_ddl + "\n" + f"{query};\n{query};\n")
            variant.write_text(
                "CREATE TABLE t (v INTEGER);\n" "SELECT v FROM t;\nSELECT v FROM t;\n"
            )
            generated = workspace / "benchmarks/core/.generated/calcite-ir/bench/case"
            generated.mkdir(parents=True)
            for side in ("before", "after"):
                (generated / f"{side}.calcite-ir.json").write_text(
                    json.dumps(
                        {
                            "schema": [
                                {
                                    "name": "t",
                                    "columns": [
                                        {"name": "id", "type": "INTEGER"},
                                        {
                                            "name": "dead_fixed",
                                            "type": "VARCHAR",
                                        },
                                        {"name": "v", "type": "VARCHAR"},
                                    ],
                                }
                            ],
                            "queries": [
                                {
                                    "sql": query,
                                    "rel": {
                                        "rowType": [
                                            {
                                                "name": "v",
                                                "type": "VARCHAR",
                                                "nullable": True,
                                            }
                                        ]
                                    },
                                }
                            ],
                        }
                    )
                )

            with mock.patch.object(qed, "ROOT", workspace), mock.patch.object(
                qed,
                "load_canonical_qed_source_schema_type_authority",
                return_value=raw_authority,
            ), mock.patch.object(
                qed,
                "analyze_qed_base_use_closure",
                return_value=base_use_closure,
            ), mock.patch.object(
                qed,
                "analyze_qed_source_star_provenance",
                return_value=no_source_star,
            ):
                source_tables = qed.parse_schema(
                    qed_ddl,
                    clean_identifier=qed.clean_identifier,
                    parse_table=qed.parse_table,
                )
                admission = qed.build_qed_opaque_source_admission(
                    source_tables,
                    [query, query],
                    source_coverage,
                    "bench",
                    "case",
                )
                fallback = {
                    "id": "opaque-varchar-equality-integer-abstraction",
                    "input": variant.name,
                    "inputSha256": qed.sha256_path(variant),
                    "sourceInput": source.name,
                    "sourceInputSha256": qed.sha256_path(source),
                    "resultPolicy": "accept-eq-only",
                    "calciteAuthority": admission["calciteAuthority"],
                    "expectedTransformedOutputTypes": ["INTEGER"],
                    "sourceStarProvenance": None,
                    "sourceSchemaTypeAuthority": admission["rawSourceSchemaAuthority"],
                    "sourceColumnUseClosure": admission["baseUseClosure"],
                    "sourceColumnProjection": admission["sourceColumnProjection"],
                    "constraintCoverage": admission["constraintCoverage"],
                }
                metadata = {
                    "sourceBenchmark": "bench",
                    "sourceCase": "case",
                    "sourceSchemaTypeAuthority": raw_authority,
                    "sourceConstraintCoverage": source_coverage,
                    "qedInput": source.name,
                    "qedInputSha256": qed.sha256_path(source),
                    "qedOpaqueStringEquivalenceFallback": fallback,
                }
                metadata_path = case_dir / "metadata.json"
                metadata_path.write_text(json.dumps(metadata))

                binding = qed.validate_qed_input_bindings(
                    metadata_path,
                    "opaque-varchar-equality-integer-abstraction",
                )
                self.assertEqual(
                    binding["calciteAuthority"]["schemaTypeAuthority"],
                    "digest-bound-raw-source-ddl",
                )
                self.assertEqual(
                    fallback["sourceColumnProjection"]["retained"],
                    [{"table": "t", "columns": ["v"]}],
                )
                self.assertEqual(
                    fallback["constraintCoverage"]["equivalenceOnlyProjection"][
                        "acceptedResult"
                    ],
                    "EQ",
                )

                for field in (
                    "sourceSchemaTypeAuthority",
                    "sourceColumnUseClosure",
                    "sourceColumnProjection",
                    "constraintCoverage",
                ):
                    with self.subTest(field=field):
                        tampered = copy.deepcopy(metadata)
                        tampered["qedOpaqueStringEquivalenceFallback"][field] = {
                            "tampered": True
                        }
                        metadata_path.write_text(json.dumps(tampered))
                        with self.assertRaisesRegex(
                            qed.QedJsonValidationError,
                            "opaque raw-type/use-closure admission is stale",
                        ):
                            qed.validate_qed_input_bindings(
                                metadata_path,
                                "opaque-varchar-equality-integer-abstraction",
                            )

                non_eq = copy.deepcopy(metadata)
                non_eq["qedOpaqueStringEquivalenceFallback"]["resultPolicy"] = (
                    "accept-any-result"
                )
                metadata_path.write_text(json.dumps(non_eq))
                with self.assertRaisesRegex(
                    qed.QedJsonValidationError,
                    "lacks EQ-only variant",
                ):
                    qed.validate_qed_input_bindings(
                        metadata_path,
                        "opaque-varchar-equality-integer-abstraction",
                    )


if __name__ == "__main__":
    unittest.main()
