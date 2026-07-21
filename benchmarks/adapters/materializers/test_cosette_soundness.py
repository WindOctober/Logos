#!/usr/bin/env python3
import hashlib
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


MATERIALIZERS = Path(__file__).resolve().parent
if str(MATERIALIZERS) not in sys.path:
    sys.path.insert(0, str(MATERIALIZERS))

import materialize_cosette as cosette  # noqa: E402


class CosetteSoundnessTests(unittest.TestCase):
    @staticmethod
    def row(name: str, type_name: str = "INTEGER", nullable: bool = True) -> dict:
        return {"name": name, "type": type_name, "nullable": nullable}

    def simple_scan(self) -> dict:
        return {
            "type": "LogicalTableScan",
            "table": ["t"],
            "inputs": [],
            "rowType": [self.row("x")],
        }

    def filtered_projection(self, project: str) -> dict:
        scan = self.simple_scan()
        return {
            "type": "LogicalProject",
            "projects": [project],
            "inputs": [
                {
                    "type": "LogicalFilter",
                    "condition": "=($0, 10)",
                    "inputs": [scan],
                    "rowType": [self.row("x")],
                }
            ],
            "rowType": [self.row("x", nullable=project.startswith("$"))],
        }

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

    def test_materialized_case_binds_output_and_raw_source_bytes(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            case = root / "suite__case"
            target = root / "out"
            case.mkdir()
            source_files = {
                "schema.sql": b"CREATE TABLE t (id INTEGER);\n",
                "sql1.sql": b"SELECT x.id FROM t AS x;\n",
                "sql2.sql": b"SELECT x.id FROM t AS x;\n",
            }
            for name, payload in source_files.items():
                (case / name).write_bytes(payload)
            (case / "metadata.json").write_text(
                json.dumps({"constraints": [], "nullSemantics": "cosette-null-free"})
            )

            cosette.materialize_case(root, case, target)
            metadata = json.loads((target / "metadata.json").read_text())
            self.assertEqual(
                metadata["cosetteFileSha256"],
                hashlib.sha256((target / "case.cos").read_bytes()).hexdigest(),
            )
            for field, name in (
                ("sourceSchemaSha256", "schema.sql"),
                ("sourceSql1Sha256", "sql1.sql"),
                ("sourceSql2Sha256", "sql2.sql"),
            ):
                self.assertEqual(
                    metadata[field],
                    hashlib.sha256(source_files[name]).hexdigest(),
                )

            (target / "case.cos").write_text("mutated\n")
            (case / "sql1.sql").write_text("SELECT 0;\n")
            self.assertNotEqual(
                metadata["cosetteFileSha256"],
                hashlib.sha256((target / "case.cos").read_bytes()).hexdigest(),
            )
            self.assertNotEqual(
                metadata["sourceSql1Sha256"],
                hashlib.sha256((case / "sql1.sql").read_bytes()).hexdigest(),
            )

    def test_calcite_rex_lowering_folds_only_checked_integer_constants(self) -> None:
        fields = [cosette.IrField("t0.x", "INTEGER", True)]
        attestations: list[dict] = []
        exact = cosette.render_rex_value(
            "CAST(+($0, /(10, 2))):INTEGER",
            fields,
            attestations,
        )
        self.assertIsNotNone(exact)
        self.assertEqual(exact.expression, "(t0.x + 5)")
        self.assertIn(
            "checked-integer-literal-fold",
            {item["rule"] for item in attestations},
        )
        self.assertIn(
            "same-type-integer-cast-erasure",
            {item["rule"] for item in attestations},
        )
        self.assertIsNone(cosette.render_rex_value("/($0, 2)", fields, []))
        self.assertIsNone(cosette.render_rex_value("/(10, 0)", fields, []))
        self.assertIsNone(
            cosette.render_rex_value("CAST($0):BIGINT", fields, [])
        )
        count_star = cosette.render_aggregate_call("COUNT()", fields)
        self.assertIsNotNone(count_star)
        self.assertEqual(count_star.expression, "COUNT(*)")

    def test_nonconstant_integer_error_obligation_requires_identical_pair(self) -> None:
        tables = [
            cosette.Table(
                "t",
                [cosette.Column("x", "int", "INTEGER")],
            )
        ]
        plus_one = {
            "type": "LogicalProject",
            "projects": ["+($0, 1)"],
            "inputs": [self.simple_scan()],
            "rowType": [self.row("x")],
        }
        plus_two = {
            "type": "LogicalProject",
            "projects": ["+($0, 2)"],
            "inputs": [self.simple_scan()],
            "rowType": [self.row("x")],
        }
        left = cosette.compile_cosette_candidate(plus_one, tables, "SELECT x + 1 FROM t")
        same = cosette.compile_cosette_candidate(plus_one, tables, "SELECT x + 1 FROM t")
        different = cosette.compile_cosette_candidate(plus_two, tables, "SELECT x + 2 FROM t")
        self.assertIsNotNone(left)
        self.assertIsNotNone(same)
        self.assertIsNotNone(different)
        self.assertEqual(
            cosette.attest_lowered_pair_safety(plus_one, plus_one, left, same)["rule"],
            "identical-lowered-query-error-and-null-closure",
        )
        self.assertIsNone(
            cosette.attest_lowered_pair_safety(plus_one, plus_two, left, different)
        )

        filtered = {
            "type": "LogicalFilter",
            "condition": ">(+($0, 1), 0)",
            "inputs": [self.simple_scan()],
            "rowType": [self.row("x")],
        }
        compiled_filter = cosette.compile_cosette_candidate(
            filtered, tables, "SELECT x FROM t WHERE x + 1 > 0"
        )
        self.assertIsNotNone(compiled_filter)
        self.assertIn(
            "pair-safety-obligation",
            {item["kind"] for item in compiled_filter.attestations},
        )

    def test_where_equality_projection_substitution_closes_unknown_rows(self) -> None:
        tables = [
            cosette.Table(
                "t",
                [cosette.Column("x", "int", "INTEGER")],
            )
        ]
        field_rel = self.filtered_projection("$0")
        literal_rel = self.filtered_projection("10")
        field_query = cosette.compile_cosette_candidate(
            field_rel, tables, "SELECT x FROM t WHERE x = 10"
        )
        literal_query = cosette.compile_cosette_candidate(
            literal_rel, tables, "SELECT 10 FROM t WHERE x = 10"
        )
        self.assertIsNotNone(field_query)
        self.assertIsNotNone(literal_query)
        attestation = cosette.attest_lowered_pair_safety(
            field_rel,
            literal_rel,
            field_query,
            literal_query,
        )
        self.assertIsNotNone(attestation)
        self.assertEqual(
            attestation["rule"],
            "filter-equality-projection-substitution",
        )
        self.assertTrue(attestation["sideConditions"]["UNKNOWNRowsRejectedByWhere"])

    def test_filter_equality_normalizes_ordered_post_filter_projections(self) -> None:
        row = self.row
        scan = {
            "type": "LogicalTableScan",
            "table": ["t"],
            "inputs": [],
            "rowType": [row("d"), row("e")],
        }

        def program(projects: list[str], literal: str = "10") -> dict:
            return {
                "type": "LogicalProject",
                "projects": projects,
                "inputs": [
                    {
                        "type": "LogicalFilter",
                        "condition": f"=($0, {literal})",
                        "inputs": [scan],
                        "rowType": [row("d"), row("e")],
                    }
                ],
                "rowType": [row(f"c{index}") for index in range(len(projects))],
            }

        left_rel = program(["$0", "+($0, 1)", "+($1, $0)"])
        right_rel = program(["10", "11", "+($1, 10)"])
        tables = [
            cosette.Table(
                "t",
                [
                    cosette.Column("d", "int", "INTEGER"),
                    cosette.Column("e", "int", "INTEGER"),
                ],
            )
        ]
        left = cosette.compile_cosette_candidate(
            left_rel,
            tables,
            "SELECT d, d + 1, e + d FROM t WHERE d = 10",
        )
        right = cosette.compile_cosette_candidate(
            right_rel,
            tables,
            "SELECT 10, 11, e + 10 FROM t WHERE d = 10",
        )
        self.assertIsNotNone(left)
        self.assertIsNotNone(right)
        attestation = cosette.attest_lowered_pair_safety(
            left_rel,
            right_rel,
            left,
            right,
        )
        self.assertIsNotNone(attestation)
        self.assertEqual(
            attestation["rule"],
            "filter-equality-projection-substitution",
        )
        self.assertTrue(
            attestation["sideConditions"][
                "projectionEvaluatedOnlyAfterFilterAcceptance"
            ]
        )

        different = program(["10", "11", "+($1, 11)"])
        different_query = cosette.compile_cosette_candidate(
            different,
            tables,
            "SELECT 10, 11, e + 11 FROM t WHERE d = 10",
        )
        self.assertIsNotNone(different_query)
        self.assertIsNone(
            cosette.attest_lowered_pair_safety(
                left_rel,
                different,
                left,
                different_query,
            )
        )

        overflow_left = program(["+($0, 1)"], "2147483647")
        overflow_right = program(["-2147483648"], "2147483647")
        self.assertIsNone(
            cosette.attest_filter_equality_projection_substitution(
                overflow_left,
                overflow_right,
            )
        )

    def test_union_all_compiler_distributes_only_closed_safe_branches(self) -> None:
        row = self.row
        tables = [
            cosette.Table(
                "t",
                [
                    cosette.Column("x", "int", "INTEGER"),
                    cosette.Column("y", "int", "INTEGER"),
                ],
            )
        ]

        def scan() -> dict:
            return {
                "type": "LogicalTableScan",
                "table": ["t"],
                "inputs": [],
                "rowType": [row("x"), row("y")],
            }

        def project(child: dict, digest: str) -> dict:
            return {
                "type": "LogicalProject",
                "projects": [digest],
                "inputs": [child],
                "rowType": [row("y")],
            }

        union = {
            "type": "LogicalUnion",
            "setOp": "UNION",
            "all": True,
            "inputs": [scan(), scan()],
            "rowType": [row("x"), row("y")],
        }
        above = project(union, "$1")
        below = {
            "type": "LogicalUnion",
            "setOp": "UNION",
            "all": True,
            "inputs": [project(scan(), "$1"), project(scan(), "$1")],
            "rowType": [row("y")],
        }
        left = cosette.compile_union_all_candidate(
            above,
            tables,
            "SELECT y FROM (SELECT * FROM t UNION ALL SELECT * FROM t) AS u",
        )
        right = cosette.compile_union_all_candidate(
            below,
            tables,
            "SELECT y FROM t UNION ALL SELECT y FROM t",
        )
        self.assertIsNotNone(left)
        self.assertIsNotNone(right)
        self.assertEqual(left.sql, right.sql)
        self.assertIn(" UNION ALL ", left.sql)
        self.assertEqual(
            left.attestations[0]["rule"],
            "calcite-ir-union-all-branch-reserialization",
        )

        distinct = dict(union, all=False)
        self.assertIsNone(
            cosette.compile_union_all_candidate(
                project(distinct, "$1"),
                tables,
                "SELECT y FROM (SELECT * FROM t UNION SELECT * FROM t) AS u",
            )
        )

        unsafe_arithmetic = project(union, "+($0, 1)")
        self.assertIsNone(
            cosette.compile_union_all_candidate(
                unsafe_arithmetic,
                tables,
                "SELECT x + 1 FROM (SELECT * FROM t UNION ALL SELECT * FROM t) AS u",
            )
        )

        join_over_union = {
            "type": "LogicalJoin",
            "joinType": "INNER",
            "condition": "true",
            "inputs": [scan(), union],
            "rowType": [row("x"), row("y"), row("x0"), row("y0")],
        }
        projected_join = {
            "type": "LogicalProject",
            "projects": ["$0", "$2"],
            "inputs": [join_over_union],
            "rowType": [row("x"), row("x0")],
        }

        def joined_branch() -> dict:
            return {
                "type": "LogicalProject",
                "projects": ["$0", "$2"],
                "inputs": [
                    {
                        "type": "LogicalJoin",
                        "joinType": "INNER",
                        "condition": "true",
                        "inputs": [scan(), scan()],
                        "rowType": [
                            row("x"),
                            row("y"),
                            row("x0"),
                            row("y0"),
                        ],
                    }
                ],
                "rowType": [row("x"), row("x0")],
            }

        distributed_join = {
            "type": "LogicalUnion",
            "setOp": "UNION",
            "all": True,
            "inputs": [joined_branch(), joined_branch()],
            "rowType": [row("x"), row("x0")],
        }
        left_join = cosette.compile_union_all_candidate(
            projected_join,
            tables,
            "SELECT * FROM t a, (SELECT * FROM t UNION ALL SELECT * FROM t) b",
        )
        right_join = cosette.compile_union_all_candidate(
            distributed_join,
            tables,
            "(SELECT * FROM t a, t b) UNION ALL (SELECT * FROM t a, t b)",
        )
        self.assertIsNotNone(left_join)
        self.assertIsNotNone(right_join)
        self.assertEqual(left_join.sql, right_join.sql)

        outer_join = dict(join_over_union, joinType="LEFT")
        self.assertIsNone(
            cosette.compile_union_all_candidate(
                dict(projected_join, inputs=[outer_join]),
                tables,
                "SELECT * FROM t a LEFT JOIN (SELECT * FROM t UNION ALL SELECT * FROM t) b ON a.x = b.x",
            )
        )

    def test_source_scalar_normalization_is_closed_and_type_sensitive(self) -> None:
        self.assertIsNotNone(
            cosette.attest_source_scalar_normalization(
                "SELECT CAST(x + 10 / 2 AS INTEGER) FROM t"
            )
        )
        # Source text alone is not authority for a fold already performed by
        # the frontend.  The exact source CASE must be paired with a closed Rex
        # rewrite site from the bound tree.
        self.assertIsNone(
            cosette.attest_source_scalar_normalization(
                "SELECT x + CASE WHEN 'a' = 'a' THEN 1 ELSE NULL END FROM t"
            )
        )
        for unsafe in (
            "SELECT CASE WHEN FALSE THEN 2.1 ELSE 1 END FROM t",
            "SELECT CAST(x AS BIGINT) FROM t",
            "SELECT TRUE FROM t",
            "SELECT NULL FROM t",
            "SELECT x, SUM(x) FROM t GROUP BY GROUPING SETS ((x), ())",
        ):
            with self.subTest(sql=unsafe):
                self.assertIsNone(cosette.attest_source_scalar_normalization(unsafe))

    def test_output_signature_gate_preserves_exact_sql_types(self) -> None:
        decimal = {
            "rowType": [
                {
                    "name": "x",
                    "type": "DECIMAL",
                    "precision": 11,
                    "scale": 1,
                    "nullable": False,
                }
            ]
        }
        integer = {"rowType": [self.row("x", nullable=False)]}
        self.assertNotEqual(
            cosette.signature_types(cosette.output_type_signature(decimal)),
            cosette.signature_types(cosette.output_type_signature(integer)),
        )
        self.assertEqual(cosette.calcite_type_from_source("DECIMAL(15, 2)"), "DECIMAL")
        self.assertEqual(cosette.calcite_type_from_source("TIMESTAMP"), "TIMESTAMP")
        self.assertEqual(cosette.calcite_type_from_source("CHAR(10)"), "VARCHAR")
        self.assertEqual(cosette.calcite_type_from_source("TIME"), "ANY")

    def test_postgres_integer_sum_type_contract_is_fail_closed(self) -> None:
        scan = self.simple_scan()
        detail = {
            "approximate": False,
            "argList": [0],
            "collation": [],
            "distinct": False,
            "filterArg": -1,
            "fullType": "INTEGER",
            "function": "SUM",
            "ignoreNulls": False,
            "kind": "SUM",
            "text": "SUM($0)",
            "type": "INTEGER",
        }
        aggregate = {
            "type": "LogicalAggregate",
            "groupSet": [],
            "groupSets": [[]],
            "aggCalls": ["SUM($0)"],
            "aggCallDetails": [detail],
            "inputs": [scan],
            "rowType": [self.row("sum", "INTEGER")],
        }
        bound = cosette.bind_calcite_rel_representation(aggregate)
        self.assertIsNotNone(bound)
        view, _ = bound
        rejected = cosette.attest_postgres_aggregate_result_types(
            view,
            read_dialect="postgres",
        )
        self.assertEqual(rejected["status"], "rejected")
        self.assertEqual(
            rejected["rejection"]["reason"],
            "Calcite aggregate result type disagrees with PostgreSQL",
        )
        self.assertEqual(rejected["rejection"]["expectedResultType"], "BIGINT")
        self.assertEqual(
            rejected["checkedRelSha256"],
            hashlib.sha256(
                json.dumps(view, sort_keys=True, separators=(",", ":")).encode()
            ).hexdigest(),
        )

        # The compiler consumes the aggregate digest, while source typing uses
        # argList.  They must be exact redundant representations: otherwise a
        # SUM over INTEGER can be used to authorize rendering SUM over BIGINT.
        mixed_argument = json.loads(json.dumps(aggregate))
        mixed_argument["inputs"][0]["rowType"].append(
            self.row("y", "BIGINT")
        )
        mixed_argument["aggCalls"] = ["SUM($1)"]
        mixed_argument["aggCallDetails"][0]["text"] = "SUM($1)"
        mixed_argument["aggCallDetails"][0]["argList"] = [0]
        mixed_argument["aggCallDetails"][0]["type"] = "BIGINT"
        mixed_argument["aggCallDetails"][0]["fullType"] = "BIGINT"
        mixed_argument["rowType"][0]["type"] = "BIGINT"
        self.assertIsNone(
            cosette.bind_calcite_rel_representation(mixed_argument)
        )

        modifier_cases = []
        filtered = json.loads(json.dumps(aggregate))
        filtered["aggCalls"] = ["SUM($0) FILTER $1"]
        filtered["aggCallDetails"][0]["text"] = "SUM($0) FILTER $1"
        filtered["aggCallDetails"][0]["filterArg"] = 1
        modifier_cases.append(filtered)
        distinct = json.loads(json.dumps(aggregate))
        distinct["aggCalls"] = ["SUM(DISTINCT $0)"]
        distinct["aggCallDetails"][0]["text"] = "SUM(DISTINCT $0)"
        distinct["aggCallDetails"][0]["distinct"] = True
        modifier_cases.append(distinct)
        approximate = json.loads(json.dumps(aggregate))
        approximate["aggCallDetails"][0]["approximate"] = True
        modifier_cases.append(approximate)
        collated = json.loads(json.dumps(aggregate))
        collated["aggCallDetails"][0]["collation"] = [{"fieldIndex": 0}]
        modifier_cases.append(collated)
        for modified in modifier_cases:
            with self.subTest(modified=modified["aggCallDetails"][0]):
                self.assertIsNone(
                    cosette.bind_calcite_rel_representation(modified)
                )

        conflicting_type = json.loads(json.dumps(aggregate))
        conflicting_type["aggCallDetails"][0]["type"] = "BIGINT"
        conflicting_type["aggCallDetails"][0]["fullType"] = "INTEGER"
        self.assertIsNone(
            cosette.bind_calcite_rel_representation(conflicting_type)
        )
        self.assertTrue(
            cosette.closed_calcite_type_envelope_agrees(
                "BIGINT",
                "BIGINT NOT NULL",
            )
        )
        self.assertTrue(
            cosette.closed_calcite_type_envelope_agrees(
                "DECIMAL",
                "DECIMAL(19, 2)",
            )
        )
        for malformed_full_type in (
            "BIGINT ARRAY",
            "BIGINT(1)",
            "BIGINT bogus",
            "BIGINT NOT NULL garbage",
        ):
            malformed = json.loads(json.dumps(aggregate))
            malformed["aggCallDetails"][0]["type"] = "BIGINT"
            malformed["aggCallDetails"][0]["fullType"] = malformed_full_type
            with self.subTest(fullType=malformed_full_type):
                self.assertIsNone(
                    cosette.bind_calcite_rel_representation(malformed)
                )

        widened = json.loads(json.dumps(aggregate))
        widened["aggCallDetails"][0]["type"] = "BIGINT"
        widened["aggCallDetails"][0]["fullType"] = "BIGINT"
        widened["rowType"][0]["type"] = "BIGINT"
        widened_view, _ = cosette.bind_calcite_rel_representation(widened)
        verified = cosette.attest_postgres_aggregate_result_types(
            widened_view,
            read_dialect="postgres",
        )
        self.assertEqual(
            verified["status"],
            "verified-postgresql-aggregate-result-types",
        )
        self.assertEqual(verified["checkedCalls"][0]["postgresResultType"], "BIGINT")
        tables = [
            cosette.Table("t", [cosette.Column("x", "int", "INTEGER")])
        ]
        compiled = cosette.compile_cosette_candidate(
            widened_view,
            tables,
            "SELECT SUM(x) FROM t",
        )
        self.assertIsNotNone(compiled)
        self.assertEqual(compiled.sql, "SELECT SUM(t0.x) AS c0 FROM t AS t0")
        non_postgres = cosette.attest_postgres_aggregate_result_types(
            widened_view,
            read_dialect="mysql",
        )
        self.assertEqual(non_postgres["status"], "rejected")
        self.assertEqual(
            non_postgres["rejection"]["reason"],
            "source query read dialect is not PostgreSQL",
        )

        contradictory = json.loads(json.dumps(widened_view))
        contradictory["rowType"][0]["type"] = "INTEGER"
        self.assertEqual(
            cosette.attest_postgres_aggregate_result_types(
                contradictory,
                read_dialect="postgres",
            )[
                "rejection"
            ]["reason"],
            "aggregate detail and ordered output row type disagree",
        )

        bigint_input = json.loads(json.dumps(widened_view))
        bigint_input["inputs"][0]["rowType"][0]["type"] = "BIGINT"
        bigint_rejected = cosette.attest_postgres_aggregate_result_types(
            bigint_input,
            read_dialect="postgres",
        )
        self.assertEqual(bigint_rejected["status"], "rejected")
        self.assertEqual(
            bigint_rejected["rejection"]["expectedResultFamily"],
            "NUMERIC",
        )

    def test_pair_gate_preserves_raw_sql_for_mistyped_integer_sum(self) -> None:
        scan = self.simple_scan()
        aggregate = {
            "type": "LogicalAggregate",
            "groupSet": [],
            "groupSets": [[]],
            "aggCalls": ["SUM($0)"],
            "aggCallDetails": [
                {
                    "function": "SUM",
                    "argList": [0],
                    "type": "INTEGER",
                }
            ],
            "inputs": [scan],
            "rowType": [self.row("sum", "INTEGER")],
        }
        sql = "SELECT SUM(x) FROM t"
        tables = [
            cosette.Table("t", [cosette.Column("x", "int", "INTEGER")])
        ]
        source = mock.Mock(rel=aggregate)
        with mock.patch.object(
            cosette,
            "load_calcite_ir_pair",
            return_value=(source, source),
        ), mock.patch.object(
            cosette,
            "ir_source_metadata",
            return_value={"sha256": "a" * 64},
        ):
            q1, q2, metadata = cosette.materialize_pair(
                sql,
                sql,
                tables,
                {"bagSemantics": True, "readDialect": "postgres"},
            )
        self.assertEqual((q1.sql, q2.sql), (sql, sql))
        self.assertFalse(metadata["applied"])
        self.assertIn("PostgreSQL aggregate result-type", metadata["reason"])
        self.assertEqual(
            metadata["pairAdmission"]["sourceAggregateTyping"]["q1"]["status"],
            "rejected",
        )

    def test_pair_gate_applies_correctly_typed_integer_sum(self) -> None:
        scan = self.simple_scan()
        aggregate = {
            "type": "LogicalAggregate",
            "groupSet": [],
            "groupSets": [[]],
            "aggCalls": ["SUM($0)"],
            "aggCallDetails": [
                {
                    "function": "SUM",
                    "argList": [0],
                    "type": "BIGINT",
                }
            ],
            "inputs": [scan],
            "rowType": [self.row("sum", "BIGINT")],
        }
        sql = "SELECT SUM(x) FROM t"
        tables = [
            cosette.Table("t", [cosette.Column("x", "int", "INTEGER")])
        ]
        source = mock.Mock(rel=aggregate)
        with mock.patch.object(
            cosette,
            "load_calcite_ir_pair",
            return_value=(source, source),
        ), mock.patch.object(
            cosette,
            "ir_source_metadata",
            return_value={"sha256": "a" * 64},
        ):
            q1, q2, metadata = cosette.materialize_pair(
                sql,
                sql,
                tables,
                {"bagSemantics": True, "readDialect": "postgres"},
            )
        self.assertTrue(metadata["applied"])
        self.assertEqual(
            (q1.sql, q2.sql),
            (
                "SELECT SUM(t0.x) AS c0 FROM t AS t0",
                "SELECT SUM(t0.x) AS c0 FROM t AS t0",
            ),
        )
        self.assertEqual(
            metadata["pairAdmission"]["sourceAggregateTyping"]["q1"]["status"],
            "verified-postgresql-aggregate-result-types",
        )

    def test_singleton_values_group_rejects_unqualified_values_column(self) -> None:
        tables = [
            cosette.Table(
                "base",
                [
                    cosette.Column("k", "int", "INTEGER"),
                    cosette.Column("four", "int", "INTEGER"),
                ],
            )
        ]
        unsafe_queries = (
            "SELECT k, MAX(four) FROM base, (VALUES (4)) AS v (four) "
            "GROUP BY k, v.four",
            "SELECT base.k, MAX(base.four) FROM base, (VALUES (4)) AS v (four) "
            "GROUP BY base.k, four",
        )
        for sql in unsafe_queries:
            with self.subTest(sql=sql):
                self.assertIsNone(
                    cosette.parse_singleton_values_group_query(sql, tables)
                )
        safe = (
            "SELECT base.k, MAX(base.four) FROM base, (VALUES (4)) AS v (four) "
            "GROUP BY base.k, v.four"
        )
        self.assertIsNotNone(
            cosette.parse_singleton_values_group_query(safe, tables)
        )

    def test_calcite_ir_loader_binds_sql_schema_and_contained_path(self) -> None:
        tables = [
            cosette.Table(
                "t",
                [cosette.Column("x", "int", "INTEGER")],
            )
        ]
        rel = self.simple_scan()
        payload = {
            "schema": [
                {"name": "t", "columns": [{"name": "x", "type": "INTEGER"}]}
            ],
            "queries": [
                {
                    "sql": "SELECT x FROM t;",
                    "rel": rel,
                }
            ],
        }
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            case = root / "benchmarks/core/.generated/calcite-ir/suite/case"
            case.mkdir(parents=True)
            for side in ("before", "after"):
                (case / f"{side}.calcite-ir.json").write_text(json.dumps(payload))
            old_root = cosette.ROOT
            cosette.ROOT = root
            try:
                loaded = cosette.load_calcite_ir_pair(
                    {"sourceBenchmark": "suite", "sourceCase": "case"},
                    ("SELECT x FROM t", "SELECT x FROM t"),
                    tables,
                )
                self.assertIsNotNone(loaded)
                self.assertTrue(
                    cosette.ir_source_metadata(loaded[0])[
                        "normalizedSourceSqlMatchesEmbeddedIrSql"
                    ]
                )
                self.assertIsNone(
                    cosette.load_calcite_ir_pair(
                        {"sourceBenchmark": "suite", "sourceCase": "case"},
                        ("SELECT 1 FROM t", "SELECT x FROM t"),
                        tables,
                    )
                )
                self.assertIsNone(
                    cosette.load_calcite_ir_pair(
                        {"sourceBenchmark": "..", "sourceCase": "outside"},
                        ("SELECT x FROM t", "SELECT x FROM t"),
                        tables,
                    )
                )
                wrong_tables = [
                    cosette.Table(
                        "t",
                        [cosette.Column("x", "string", "TEXT")],
                    )
                ]
                self.assertIsNone(
                    cosette.load_calcite_ir_pair(
                        {"sourceBenchmark": "suite", "sourceCase": "case"},
                        ("SELECT x FROM t", "SELECT x FROM t"),
                        wrong_tables,
                    )
                )
            finally:
                cosette.ROOT = old_root

    def test_typed_calcite_rex_view_is_exact_and_fail_closed(self) -> None:
        ref = {
            "class": "RexInputRef",
            "kind": "INPUT_REF",
            "index": 0,
            "text": "$0",
            "type": "INTEGER",
            "fullType": "INTEGER",
            "nullable": True,
        }
        literal = {
            "class": "RexLiteral",
            "kind": "LITERAL",
            "literalTypeName": "DECIMAL",
            "text": "7",
            "type": "INTEGER",
            "fullType": "INTEGER NOT NULL",
            "nullable": False,
        }
        equality = {
            "class": "RexCall",
            "kind": "EQUALS",
            "opKind": "EQUALS",
            "operator": "=",
            "operands": [ref, literal],
            "text": "=($0, 7)",
            "type": "BOOLEAN",
            "fullType": "BOOLEAN",
            "nullable": True,
        }
        scan = self.simple_scan()
        relation = {
            "type": "LogicalProject",
            "projectRex": [ref],
            "inputs": [
                {
                    "type": "LogicalFilter",
                    "conditionRex": equality,
                    "inputs": [scan],
                    "rowType": scan["rowType"],
                }
            ],
            "rowType": [self.row("x")],
        }
        bound = cosette.bind_calcite_rel_representation(relation)
        self.assertIsNotNone(bound)
        view, attestation = bound
        self.assertEqual(view["projects"], ["$0"])
        self.assertEqual(view["inputs"][0]["condition"], "=($0, 7)")
        self.assertEqual(
            attestation["status"], "verified-typed-rex-digest-view"
        )
        self.assertEqual(
            attestation["aliasedFieldCounts"]["conditions"], 1
        )

        bad_ref = json.loads(json.dumps(relation))
        bad_ref["projectRex"][0]["text"] = "$1"
        self.assertIsNone(cosette.bind_calcite_rel_representation(bad_ref))

        conflicting = json.loads(json.dumps(relation))
        conflicting["projects"] = ["$1"]
        self.assertIsNone(cosette.bind_calcite_rel_representation(conflicting))

        symbol = {
            "class": "RexLiteral",
            "kind": "LITERAL",
            "literalTypeName": "SYMBOL",
            "literalValue2": "YEAR",
            "text": "FLAG(YEAR)",
            "type": "SYMBOL",
            "fullType": "SYMBOL NOT NULL",
            "nullable": False,
        }
        self.assertEqual(cosette.typed_rex_digest(symbol), "FLAG(YEAR)")
        symbol["text"] = "FLAG(MONTH)"
        self.assertIsNone(cosette.typed_rex_digest(symbol))

    def test_parse_group_set_accepts_checked_typed_ir_indexes(self) -> None:
        self.assertEqual(cosette.parse_group_set([0, 2]), [0, 2])
        self.assertIsNone(cosette.parse_group_set([0, True]))
        self.assertIsNone(cosette.parse_group_set([0, -1]))

    def test_tsql_date_day_binding_requires_complete_pair_attestation(self) -> None:
        date = "'1998-08-04'"
        raw_before = (
            "SELECT x AS days FROM t WHERE d BETWEEN CAST("
            f"{date} AS DATE) AND (CAST({date} AS DATE) + 2 days)"
        )
        raw_after = (
            "SELECT x AS days FROM t WHERE d BETWEEN CAST("
            f"{date} AS DATE) AND (CAST({date} AS DATE) + 2)"
        )
        generated_before = raw_before.replace("2 days", "2 AS days")
        generated_after = raw_after
        explicit = lambda sql: cosette.substitute_unprotected(  # noqa: E731
            cosette._TSQL_DATE_DAY_SOURCE,
            cosette._explicit_day_interval,
            sql,
            start_only=True,
        )
        pair = {
            "kind": "paired-tsql-between-date-day-unit",
            "sourceSideWithDayUnit": "before",
            "occurrencesPerSide": 1,
            "predicateOnly": True,
            "orderedQueryPairPreserved": True,
            "sourceSha256": {
                "before": hashlib.sha256(raw_before.encode()).hexdigest(),
                "after": hashlib.sha256(raw_after.encode()).hexdigest(),
            },
            "frontendInputSha256": {
                "before": hashlib.sha256(
                    cosette._ensure_sql_terminated(explicit(raw_before)).encode()
                ).hexdigest(),
                "after": hashlib.sha256(
                    cosette._ensure_sql_terminated(explicit(raw_after)).encode()
                ).hexdigest(),
            },
            "dateDayMultiset": [
                {
                    "lowerDateLiteral": date,
                    "upperDateLiteral": date,
                    "days": "2",
                    "count": 1,
                }
            ],
        }
        normalization = {
            "readDialect": "tsql",
            "writeDialect": "postgres",
            "identify": False,
            "pretty": False,
        }
        source_metadata = {
            "sourceBenchmark": "suite",
            "sourceCase": "case",
            "sourceDialect": "tsql_like",
            "readDialect": "tsql",
            "source": {"source": "benchmarks/raw", "case_id": "case"},
            "normalizationForSolverRun": {
                "before": normalization,
                "after": normalization,
            },
        }
        ir_metadata = {
            "sourceBenchmark": "suite",
            "sourceCase": "case",
            "frontendPairPreprocessing": [pair],
        }
        replay = {
            "status": "verified-sqlglot-source-normalization-replay",
            "canonicalTokenSha256": "a" * 64,
        }
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            raw_dir = root / "benchmarks/raw/case"
            raw_dir.mkdir(parents=True)
            (raw_dir / "case_0.sql").write_text(raw_before)
            (raw_dir / "case_1.sql").write_text(raw_after)
            old_root = cosette.ROOT
            cosette.ROOT = root
            try:
                with mock.patch.object(
                    cosette,
                    "attest_sqlglot_source_normalization_replay",
                    return_value=replay,
                ):
                    bound = cosette.bind_pair_attested_tsql_date_days(
                        source_metadata,
                        ir_metadata,
                        (generated_before, generated_after),
                    )
                    self.assertIsNotNone(bound)
                    self.assertIn("SELECT x AS days", bound[0][0])
                    self.assertNotIn("+ 2 AS days", bound[0][0])
                    self.assertIn("+ INTERVAL '2' DAY", bound[0][0])
                    self.assertTrue(
                        bound[1][0]["sideConditions"]["noOutputAliasWasRemoved"]
                    )

                    mismatched = generated_after.replace("+ 2)", "+ 3)")
                    self.assertIsNone(
                        cosette.bind_pair_attested_tsql_date_days(
                            source_metadata,
                            ir_metadata,
                            (generated_before, mismatched),
                        )
                    )
                    bad_ir = json.loads(json.dumps(ir_metadata))
                    bad_ir["frontendPairPreprocessing"][0]["dateDayMultiset"][0][
                        "days"
                    ] = "3"
                    self.assertIsNone(
                        cosette.bind_pair_attested_tsql_date_days(
                            source_metadata,
                            bad_ir,
                            (generated_before, generated_after),
                        )
                    )
            finally:
                cosette.ROOT = old_root

    def test_calcite_ir_loader_accepts_only_authoritative_identifier_alpha_rename(
        self,
    ) -> None:
        tables = [
            cosette.Table(
                "t",
                [cosette.Column("key_x", "int", "INTEGER")],
            )
        ]
        rel = {
            "type": "LogicalTableScan",
            "table": ["t"],
            "inputs": [],
            "rowType": [self.row("key", nullable=False)],
        }
        payload = {
            "schema": [
                {"name": "t", "columns": [{"name": "key", "type": "INTEGER"}]}
            ],
            "queries": [
                {
                    "sql": (
                        'SELECT "x"."key" FROM "t" AS "x" '
                        'WHERE "x"."key" = \'key\';'
                    ),
                    "rel": rel,
                }
            ],
        }
        metadata = {
            "sourceBenchmark": "suite",
            "sourceCase": "case",
            "renamedIdentifiers": {"key": "key_x"},
            "integrityContract": {
                "authoritativeForLogos": True,
                "identifierRenames": "metadata.json#/renamedIdentifiers",
                "parserFacingDdl": "schema.sql",
            },
        }
        source_sql = "SELECT x.key_x FROM t x WHERE x.key_x = 'key'"
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            case = root / "benchmarks/core/.generated/calcite-ir/suite/case"
            case.mkdir(parents=True)
            for side in ("before", "after"):
                (case / f"{side}.calcite-ir.json").write_text(json.dumps(payload))
            old_root = cosette.ROOT
            cosette.ROOT = root
            try:
                loaded = cosette.load_calcite_ir_pair(
                    metadata,
                    (source_sql, source_sql),
                    tables,
                )
                self.assertIsNotNone(loaded)
                binding = cosette.ir_source_metadata(loaded[0])
                self.assertFalse(
                    binding["normalizedSourceSqlMatchesEmbeddedIrSql"]
                )
                self.assertTrue(binding["normalizedSourceSqlMatchesBoundIrSql"])
                self.assertEqual(
                    binding["authorityBinding"]["query"]["status"],
                    "verified-authoritative-identifier-alpha-renaming",
                )
                self.assertEqual(
                    binding["authorityBinding"]["query"]
                    ["optionalAliasStyleAttestation"]["status"],
                    "verified-optional-alias-as-style",
                )
                self.assertEqual(
                    binding["authorityBinding"]["schema"]["status"],
                    "verified-complete-ordered-schema",
                )

                no_contract = dict(metadata)
                no_contract.pop("integrityContract")
                self.assertIsNone(
                    cosette.load_calcite_ir_pair(
                        no_contract,
                        (source_sql, source_sql),
                        tables,
                    )
                )
                # Identifier alpha-renaming must never rewrite string literals.
                self.assertIsNone(
                    cosette.load_calcite_ir_pair(
                        metadata,
                        (
                            "SELECT x.key_x FROM t x WHERE x.key_x = 'key_x'",
                            source_sql,
                        ),
                        tables,
                    )
                )
                # Nor may it conceal any relational/scalar SQL change.
                self.assertIsNone(
                    cosette.load_calcite_ir_pair(
                        metadata,
                        (
                            "SELECT x.key_x FROM t x WHERE x.key_x <> 'key'",
                            source_sql,
                        ),
                        tables,
                    )
                )
            finally:
                cosette.ROOT = old_root

    def test_authoritative_identifier_rename_map_must_be_injective_and_safe(
        self,
    ) -> None:
        contract = {
            "authoritativeForLogos": True,
            "identifierRenames": "metadata.json#/renamedIdentifiers",
            "parserFacingDdl": "schema.sql",
        }
        for renames in (
            {"key": "same", "value": "same"},
            {"Key": "first", "key": "second"},
            {"bad-key": "key_x"},
            {"key": "unsafe-name"},
        ):
            with self.subTest(renames=renames), self.assertRaises(ValueError):
                cosette.authoritative_identifier_renames(
                    {
                        "renamedIdentifiers": renames,
                        "integrityContract": contract,
                    }
                )

    def test_optional_alias_style_attestation_is_closed_over_non_as_tokens(
        self,
    ) -> None:
        accepted = cosette.attest_optional_alias_style_binding(
            "SELECT CAST(x AS INT) AS y FROM t AS a",
            "SELECT CAST(x AS INT) y FROM t a",
        )
        self.assertIsNotNone(accepted)
        self.assertEqual(
            accepted["status"], "verified-optional-alias-as-style"
        )
        case_only = cosette.attest_optional_alias_style_binding(
            "SELECT X FROM T",
            "select x from t",
        )
        self.assertIsNotNone(case_only)
        self.assertEqual(case_only["status"], "verified-unquoted-case-style")
        self.assertGreater(case_only["caseFoldedTokenCount"], 0)
        self.assertIsNone(
            cosette.attest_optional_alias_style_binding(
                "SELECT x <> 1 FROM t AS a",
                "SELECT x != 1 FROM t a",
            )
        )
        self.assertIsNone(
            cosette.attest_optional_alias_style_binding(
                "SELECT x FROM t AS a WHERE x = 'literal'",
                "SELECT x FROM t a WHERE x = 'changed'",
            )
        )
        self.assertIsNone(
            cosette.attest_optional_alias_style_binding(
                "SELECT x FROM t WHERE x = 'ABC'",
                "SELECT x FROM t WHERE x = 'abc'",
            )
        )

    def test_grouped_left_join_rule_requires_plain_safe_shape(self) -> None:
        row = self.row
        left = {
            "type": "LogicalTableScan",
            "table": ["l"],
            "inputs": [],
            "rowType": [row("x")],
        }
        right = {
            "type": "LogicalTableScan",
            "table": ["r"],
            "inputs": [],
            "rowType": [row("x")],
        }
        join = {
            "type": "LogicalJoin",
            "joinType": "LEFT",
            "condition": "=($0, $1)",
            "inputs": [left, right],
            "rowType": [row("x"), row("x0")],
        }
        rel = {
            "type": "LogicalAggregate",
            "aggCalls": [],
            "groupSet": "{0}",
            "inputs": [
                {
                    "type": "LogicalProject",
                    "projects": ["$0"],
                    "inputs": [join],
                    "rowType": [row("x")],
                }
            ],
            "rowType": [row("x")],
        }
        tables = [
            cosette.Table("l", [cosette.Column("x", "int", "INTEGER")]),
            cosette.Table("r", [cosette.Column("x", "int", "INTEGER")]),
        ]
        source = "SELECT l.x FROM l LEFT JOIN r ON l.x = r.x GROUP BY l.x"
        candidate = cosette.compile_grouped_unused_left_join(rel, tables, source)
        self.assertIsNotNone(candidate)
        self.assertEqual(
            candidate.attestations[0]["rule"],
            "grouped-unobserved-left-join-elimination",
        )
        unsafe_join = dict(join, condition="=($0, 1)")
        unsafe_rel = dict(
            rel,
            inputs=[dict(rel["inputs"][0], inputs=[unsafe_join])],
        )
        self.assertIsNone(
            cosette.compile_grouped_unused_left_join(unsafe_rel, tables, source)
        )
        self.assertIsNone(
            cosette.compile_grouped_unused_left_join(
                rel,
                tables,
                source + " GROUPING SETS ((l.x), ())",
            )
        )

    def test_intersect_empty_rule_uses_typed_canonical_integers(self) -> None:
        row = self.row
        tables = [
            cosette.Table("t", [cosette.Column("x", "int", "INTEGER")])
        ]

        def leaf(value: str, type_name: str = "INTEGER") -> dict:
            scan = {
                "type": "LogicalTableScan",
                "table": ["t"],
                "inputs": [],
                "rowType": [row("x", type_name)],
            }
            return {
                "type": "LogicalFilter",
                "condition": f"=($0, {value})",
                "inputs": [scan],
                "rowType": [row("x", type_name)],
            }

        rel = {
            "type": "LogicalIntersect",
            "all": False,
            "inputs": [leaf("1"), leaf("2")],
            "rowType": [row("x")],
        }
        self.assertIsNotNone(
            cosette.compile_contradictory_intersect(
                rel,
                tables,
                "SELECT x FROM t WHERE x = 1 INTERSECT SELECT x FROM t WHERE x = 2",
            )
        )
        plus_spelling = dict(rel, inputs=[leaf("1"), leaf("+1")])
        self.assertIsNone(
            cosette.compile_contradictory_intersect(
                plus_spelling,
                tables,
                "SELECT x FROM t WHERE x = 1 INTERSECT SELECT x FROM t WHERE x = +1",
            )
        )
        string_rel = dict(
            rel,
            inputs=[leaf("'a'", "VARCHAR"), leaf("'a '", "VARCHAR")],
            rowType=[row("x", "VARCHAR")],
        )
        self.assertIsNone(
            cosette.compile_contradictory_intersect(
                string_rel,
                [cosette.Table("t", [cosette.Column("x", "string", "TEXT")])],
                "SELECT x FROM t WHERE x = 'a' INTERSECT SELECT x FROM t WHERE x = 'a '",
            )
        )

    def test_fetch_zero_rule_rejects_expression_slicing(self) -> None:
        row = self.row
        scan = {
            "type": "LogicalTableScan",
            "table": ["t"],
            "inputs": [],
            "rowType": [row("x")],
        }
        rel = {
            "type": "LogicalSort",
            "fetch": "0",
            "offset": None,
            "collation": [{"fieldIndex": 0, "direction": "ASCENDING"}],
            "inputs": [scan],
            "rowType": [row("x")],
        }
        tables = [
            cosette.Table("t", [cosette.Column("x", "int", "INTEGER")])
        ]
        self.assertIsNotNone(
            cosette.compile_fetch_zero(
                rel,
                tables,
                "SELECT x FROM t ORDER BY x FETCH NEXT 0 ROWS ONLY",
            )
        )
        unsafe_child = dict(
            rel,
            fetch="1 + 1",
        )
        unsafe_root = dict(rel, inputs=[unsafe_child])
        self.assertIsNone(
            cosette.compile_fetch_zero(
                unsafe_root,
                tables,
                "SELECT x FROM t ORDER BY x FETCH NEXT 0 ROWS ONLY",
            )
        )

    def test_boolean_column_is_not_reinterpreted_as_cosette_int_predicate(self) -> None:
        scan = {
            "type": "LogicalTableScan",
            "table": ["t"],
            "inputs": [],
            "rowType": [self.row("b", "BOOLEAN")],
        }
        rel = {
            "type": "LogicalProject",
            "projects": ["$0"],
            "inputs": [
                {
                    "type": "LogicalFilter",
                    "condition": "$0",
                    "inputs": [scan],
                    "rowType": [self.row("b", "BOOLEAN")],
                }
            ],
            "rowType": [self.row("b", "BOOLEAN")],
        }
        tables = [
            cosette.Table("t", [cosette.Column("b", "int", "BOOLEAN")])
        ]
        self.assertIsNone(
            cosette.compile_cosette_candidate(
                rel,
                tables,
                "SELECT b FROM t WHERE b",
            )
        )

    def test_singleton_values_rule_has_empty_input_guard(self) -> None:
        row = self.row
        base_scan = {
            "type": "LogicalTableScan",
            "table": ["base"],
            "inputs": [],
            "rowType": [row("k"), row("v")],
        }
        values = {
            "type": "LogicalValues",
            "inputs": [],
            "rowType": [row("four", nullable=False)],
            "tuples": [[{"kind": "LITERAL", "type": "INTEGER"}]],
        }
        join = {
            "type": "LogicalJoin",
            "joinType": "INNER",
            "condition": "true",
            "inputs": [base_scan, values],
            "rowType": [row("k"), row("v"), row("four", nullable=False)],
        }
        project = {
            "type": "LogicalProject",
            "projects": ["$0", "$2", "$1"],
            "inputs": [join],
            "rowType": [row("k"), row("four", nullable=False), row("v")],
        }
        aggregate = {
            "type": "LogicalAggregate",
            "groupSet": "{0, 1}",
            "aggCalls": ["MAX($2)"],
            "inputs": [project],
            "rowType": [row("k"), row("four", nullable=False), row("m")],
        }
        rel = {
            "type": "LogicalProject",
            "projects": ["$0", "$2"],
            "inputs": [aggregate],
            "rowType": [row("k"), row("m")],
        }
        tables = [
            cosette.Table(
                "base",
                [
                    cosette.Column("k", "int", "INTEGER"),
                    cosette.Column("v", "int", "INTEGER"),
                ],
            )
        ]
        source = (
            "SELECT base.k, MAX(base.v) FROM base, (VALUES (4)) AS s (four) "
            "GROUP BY base.k, s.four"
        )
        candidate = cosette.compile_singleton_values_group(rel, tables, source)
        self.assertIsNotNone(candidate)
        self.assertTrue(
            candidate.attestations[0]["sideConditions"][
                "emptyBaseInputProducesNoGroupsOnBothSides"
            ]
        )
        self.assertIsNone(
            cosette.parse_singleton_values_group_query(
                "SELECT MAX(base.v) FROM base, (VALUES (4)) AS s (four) "
                "GROUP BY s.four",
                tables,
            )
        )

    def test_constant_only_group_key_is_not_dropped_on_empty_input(self) -> None:
        scan = self.simple_scan()
        projected = {
            "type": "LogicalProject",
            "projects": ["1", "$0"],
            "inputs": [scan],
            "rowType": [
                self.row("constant", nullable=False),
                self.row("x"),
            ],
        }
        aggregate = {
            "type": "LogicalAggregate",
            "groupSet": "{0}",
            "aggCalls": ["MAX($1)"],
            "inputs": [projected],
            "rowType": [
                self.row("constant", nullable=False),
                self.row("m"),
            ],
        }
        tables = [
            cosette.Table("t", [cosette.Column("x", "int", "INTEGER")])
        ]
        self.assertIsNone(cosette.compile_flat_rel(aggregate, tables, [0]))

    def test_flat_pair_attester_closes_only_the_equality_inner_fragment(self) -> None:
        fields = [
            cosette.IrField("t0.a", "INTEGER", True),
            cosette.IrField("t0.b", "INTEGER", True),
            cosette.IrField("t0.c", "INTEGER", True),
        ]
        left = cosette.CompiledCosetteQuery(
            "left",
            [],
            cosette.FlatCosettePlan(
                ["r AS t0"],
                ["(t0.a = t0.b)", "(t0.b = t0.c)"],
                fields,
                group_by=["t0.c", "t0.a", "t0.b"],
            ),
        )
        right = cosette.CompiledCosetteQuery(
            "right",
            [],
            cosette.FlatCosettePlan(
                ["r AS t0"],
                ["(t0.a = t0.c)", "(t0.a = t0.b)"],
                fields,
                group_by=["t0.b", "t0.c", "t0.a"],
            ),
        )
        attestation = cosette.attest_flat_inner_relational_equivalence(left, right)
        self.assertIsNotNone(attestation)
        self.assertEqual(attestation["rule"], "flat-inner-relational-equivalence")

        # A stronger inequality is not inferred from another inequality.
        right.flat_plan.predicates.append("(t0.a > 5)")
        self.assertIsNone(
            cosette.attest_flat_inner_relational_equivalence(left, right)
        )

    def test_flat_pair_attester_is_alias_and_inner_join_order_invariant(self) -> None:
        left = cosette.CompiledCosetteQuery(
            "left",
            [],
            cosette.FlatCosettePlan(
                ["a AS t0", "b AS t1"],
                ["(t0.k = t1.k)"],
                [
                    cosette.IrField("t0.v", "INTEGER", True),
                    cosette.IrField("t1.w", "INTEGER", True),
                ],
            ),
        )
        right = cosette.CompiledCosetteQuery(
            "right",
            [],
            cosette.FlatCosettePlan(
                ["b AS t0", "a AS t1"],
                ["(t1.k = t0.k)"],
                [
                    cosette.IrField("t1.v", "INTEGER", True),
                    cosette.IrField("t0.w", "INTEGER", True),
                ],
            ),
        )
        self.assertIsNotNone(
            cosette.attest_flat_inner_relational_equivalence(left, right)
        )

    def test_flat_pair_attester_does_not_erase_checked_arithmetic(self) -> None:
        obligation = {
            "kind": "pair-safety-obligation",
            "rule": "nonconstant-checked-integer-operation",
        }
        left = cosette.CompiledCosetteQuery(
            "left",
            [obligation],
            cosette.FlatCosettePlan(
                ["r AS t0"],
                ["(t0.d = 10)", "((t0.d + 5) > t0.e)"],
                [cosette.IrField("t0.e", "INTEGER", True)],
            ),
        )
        right = cosette.CompiledCosetteQuery(
            "right",
            [],
            cosette.FlatCosettePlan(
                ["r AS t0"],
                ["(t0.d = 10)", "(15 > t0.e)"],
                [cosette.IrField("t0.e", "INTEGER", True)],
            ),
        )
        self.assertIsNone(
            cosette.attest_flat_inner_relational_equivalence(left, right)
        )

        # Even identical flattened predicates cannot attest the original
        # evaluation stage (JOIN ON versus a filter above the join).
        same_flat_shape = cosette.CompiledCosetteQuery(
            "same-flat-shape",
            [obligation],
            cosette.FlatCosettePlan(
                ["r AS t0"],
                ["(t0.d = 10)", "((t0.d + 5) > t0.e)"],
                [cosette.IrField("t0.e", "INTEGER", True)],
            ),
        )
        self.assertIsNone(
            cosette.attest_flat_inner_relational_equivalence(left, same_flat_shape)
        )

        # Reordering a possibly failing arithmetic predicate can change whether
        # PostgreSQL observes that error, so conjunction canonicalization must
        # not silently identify these plans either.
        reordered = cosette.CompiledCosetteQuery(
            "reordered",
            [obligation],
            cosette.FlatCosettePlan(
                ["r AS t0"],
                ["((t0.d + 5) > t0.e)", "(t0.d = 10)"],
                [cosette.IrField("t0.e", "INTEGER", True)],
            ),
        )
        self.assertIsNone(
            cosette.attest_flat_inner_relational_equivalence(left, reordered)
        )

    def test_flat_pair_attester_removes_only_redundant_integer_bounds(self) -> None:
        field = [cosette.IrField("t0.a", "INTEGER", True)]
        stronger = cosette.CompiledCosetteQuery(
            "stronger",
            [],
            cosette.FlatCosettePlan(
                ["r AS t0"], ["(t0.a > 10)", "(t0.a > 5)"], field
            ),
        )
        reduced = cosette.CompiledCosetteQuery(
            "reduced",
            [],
            cosette.FlatCosettePlan(["r AS t0"], ["(t0.a > 10)"], field),
        )
        self.assertIsNotNone(
            cosette.attest_flat_inner_relational_equivalence(stronger, reduced)
        )

        different = cosette.CompiledCosetteQuery(
            "different",
            [],
            cosette.FlatCosettePlan(["r AS t0"], ["(t0.a > 11)"], field),
        )
        self.assertIsNone(
            cosette.attest_flat_inner_relational_equivalence(stronger, different)
        )

    def test_flat_pair_attester_does_not_remove_null_sensitive_self_join(self) -> None:
        left = cosette.CompiledCosetteQuery(
            "left",
            [],
            cosette.FlatCosettePlan(
                ["r AS t0", "r AS t1"],
                ["(t0.a = t1.a)"],
                [cosette.IrField("t1.a", "INTEGER", True)],
                group_by=["t1.a"],
            ),
        )
        right = cosette.CompiledCosetteQuery(
            "right",
            [],
            cosette.FlatCosettePlan(
                ["r AS t0"],
                [],
                [cosette.IrField("t0.a", "INTEGER", True)],
                group_by=["t0.a"],
            ),
        )
        self.assertIsNone(
            cosette.attest_flat_inner_relational_equivalence(left, right)
        )

    def test_filter_bool3_preprocessing_is_true_acceptance_only(self) -> None:
        scan = {
            "type": "LogicalTableScan",
            "table": ["t"],
            "inputs": [],
            "rowType": [self.row("x"), self.row("y")],
        }
        tautology = {
            "type": "LogicalFilter",
            "condition": "OR(IS NULL($0), IS NOT NULL($0))",
            "inputs": [scan],
            "rowType": scan["rowType"],
        }
        normalized, evidence = cosette.preprocess_cosette_rel(
            tautology, bag_observation=True
        )
        self.assertEqual(normalized["type"], "LogicalTableScan")
        self.assertIn(
            "bool3-null-partition-tautology",
            {item["rule"] for item in evidence},
        )

        different_fields = {
            **tautology,
            "condition": "OR(IS NULL($0), IS NOT NULL($1))",
        }
        normalized, _ = cosette.preprocess_cosette_rel(
            different_fields, bag_observation=True
        )
        self.assertEqual(normalized["type"], "LogicalFilter")

        composite = {
            **tautology,
            "condition": "OR(IS NULL(ROW($0, $1)), IS NOT NULL(ROW($0, $1)))",
        }
        normalized, _ = cosette.preprocess_cosette_rel(
            composite, bag_observation=True
        )
        self.assertEqual(normalized["type"], "LogicalFilter")

        redundant = {
            **tautology,
            "condition": "AND(=($0, 10), IS NOT NULL($0))",
        }
        normalized, _ = cosette.preprocess_cosette_rel(
            redundant, bag_observation=True
        )
        self.assertEqual(normalized["condition"], "=($0, 10)")

        not_distinct_literal = {
            **tautology,
            "condition": "OR(AND(IS NULL($0), IS NULL(10)), IS TRUE(=($0, 10)))",
        }
        normalized, _ = cosette.preprocess_cosette_rel(
            not_distinct_literal, bag_observation=True
        )
        self.assertEqual(normalized["condition"], "=($0, 10)")

        not_distinct_fields = {
            **tautology,
            "condition": "OR(AND(IS NULL($0), IS NULL($1)), IS TRUE(=($0, $1)))",
        }
        normalized, _ = cosette.preprocess_cosette_rel(
            not_distinct_fields, bag_observation=True
        )
        self.assertIn("IS NULL", normalized["condition"])

    def test_inner_join_not_null_elision_stops_at_error_boundaries(self) -> None:
        left_scan = self.simple_scan()
        right_scan = self.simple_scan()

        def not_null(source: dict) -> dict:
            return {
                "type": "LogicalFilter",
                "condition": "IS NOT NULL($0)",
                "inputs": [source],
                "rowType": source["rowType"],
            }

        join = {
            "type": "LogicalJoin",
            "joinType": "INNER",
            "condition": "=($0, $1)",
            "inputs": [not_null(left_scan), not_null(right_scan)],
            "rowType": [self.row("x"), self.row("x0")],
        }
        normalized, evidence = cosette.preprocess_cosette_rel(
            join, bag_observation=True
        )
        self.assertEqual(
            [child["type"] for child in normalized["inputs"]],
            ["LogicalTableScan", "LogicalTableScan"],
        )
        self.assertIn(
            "inner-comparison-implies-input-not-null",
            {item["rule"] for item in evidence},
        )

        outer = {**join, "joinType": "LEFT", "inputs": [not_null(left_scan), right_scan]}
        normalized, _ = cosette.preprocess_cosette_rel(
            outer, bag_observation=True
        )
        self.assertEqual(normalized["inputs"][0]["type"], "LogicalFilter")

        disjunctive = {
            **join,
            "condition": "OR(=($0, $1), =($0, 10))",
            "inputs": [not_null(left_scan), right_scan],
        }
        normalized, _ = cosette.preprocess_cosette_rel(
            disjunctive, bag_observation=True
        )
        self.assertEqual(normalized["inputs"][0]["type"], "LogicalFilter")

        checked_project = {
            "type": "LogicalProject",
            "projects": ["+($0, 1)"],
            "inputs": [not_null(self.simple_scan())],
            "rowType": [self.row("x")],
        }
        risky_join = {**join, "inputs": [checked_project, self.simple_scan()]}
        normalized, _ = cosette.preprocess_cosette_rel(
            risky_join, bag_observation=True
        )
        self.assertEqual(
            normalized["inputs"][0]["inputs"][0]["type"],
            "LogicalFilter",
        )

        unrelated_filter = {
            "type": "LogicalFilter",
            "condition": ">($0, 0)",
            "inputs": [not_null(self.simple_scan())],
            "rowType": [self.row("x")],
        }
        blocked_join = {**join, "inputs": [unrelated_filter, self.simple_scan()]}
        normalized, _ = cosette.preprocess_cosette_rel(
            blocked_join, bag_observation=True
        )
        self.assertEqual(
            normalized["inputs"][0]["inputs"][0]["type"],
            "LogicalFilter",
        )

    def test_nested_filter_equality_never_erases_checked_qual_errors(self) -> None:
        scan = {
            "type": "LogicalTableScan",
            "table": ["t"],
            "inputs": [],
            "rowType": [self.row("x"), self.row("y")],
        }

        def nested(value: int) -> dict:
            inner = {
                "type": "LogicalFilter",
                "condition": f"=($0, {value})",
                "inputs": [scan],
                "rowType": scan["rowType"],
            }
            identity = {
                "type": "LogicalProject",
                "projects": ["$0", "$1"],
                "inputs": [inner],
                "rowType": scan["rowType"],
            }
            return {
                "type": "LogicalFilter",
                "condition": ">(+($0, 5), $1)",
                "inputs": [identity],
                "rowType": scan["rowType"],
            }

        normalized, evidence = cosette.preprocess_cosette_rel(
            nested(10), bag_observation=True
        )
        self.assertEqual(normalized["condition"], ">(+($0, 5), $1)")
        self.assertNotIn(
            "accepted-equality-domain-checked-fold",
            {item["rule"] for item in evidence},
        )

        overflow = nested(2**31 - 1)
        overflow["condition"] = ">(+($0, 1), $1)"
        normalized, evidence = cosette.preprocess_cosette_rel(
            overflow, bag_observation=True
        )
        self.assertEqual(normalized["condition"], ">(+($0, 1), $1)")
        self.assertNotIn(
            "accepted-equality-domain-checked-fold",
            {item["rule"] for item in evidence},
        )

    def test_null_rejecting_where_strengthens_only_closed_outer_joins(self) -> None:
        left = self.simple_scan()
        right = {
            **self.simple_scan(),
            "table": ["u"],
            "rowType": [self.row("y")],
        }

        def filtered_join(
            join_type: str,
            condition: str,
            join_condition: str = "=($0, $1)",
        ) -> dict:
            join = {
                "type": "LogicalJoin",
                "joinType": join_type,
                "condition": join_condition,
                "inputs": [left, right],
                "rowType": left["rowType"] + right["rowType"],
            }
            return {
                "type": "LogicalFilter",
                "condition": condition,
                "inputs": [join],
                "rowType": join["rowType"],
            }

        for relation in (
            filtered_join("left", "=($1, 10)"),
            filtered_join("right", "=($0, 10)"),
            filtered_join("full", "AND(=($0, 10), >($1, 0))"),
        ):
            with self.subTest(relation=relation):
                normalized, evidence = cosette.preprocess_cosette_rel(
                    relation, bag_observation=True
                )
                self.assertEqual(normalized["inputs"][0]["joinType"], "inner")
                self.assertIn(
                    "null-rejecting-filter-strengthens-outer-join",
                    {item["rule"] for item in evidence},
                )

        unsafe = (
            # A left-side predicate does not reject a LEFT join's unmatched
            # rows, and one-sided rejection leaves a FULL join outer.
            filtered_join("left", "=($0, 10)"),
            filtered_join("full", "=($0, 10)"),
            # OR can accept through the preserved side.
            filtered_join("left", "OR(=($1, 10), =($0, 20))"),
            # Checked scalar evaluation and checked join conditions are kept
            # outside this error-preserving rule.
            filtered_join("left", ">(+($1, 1), 10)"),
            filtered_join("left", "=($1, 10)", ">(+($0, 1), $1)"),
            # IS NOT NULL is semantically null-rejecting, but is not silently
            # admitted into the public DSL by this direct-comparison gate.
            filtered_join("left", "IS NOT NULL($1)"),
        )
        for relation in unsafe:
            with self.subTest(relation=relation):
                normalized, evidence = cosette.preprocess_cosette_rel(
                    relation, bag_observation=True
                )
                self.assertEqual(
                    normalized["inputs"][0]["joinType"],
                    relation["inputs"][0]["joinType"],
                )
                self.assertNotIn(
                    "null-rejecting-filter-strengthens-outer-join",
                    {item["rule"] for item in evidence},
                )

    def test_bag_sort_erasure_requires_direct_scan_key_provenance(self) -> None:
        scan = self.simple_scan()

        def sort(source: dict, *, fetch=None) -> dict:
            return {
                "type": "LogicalSort",
                "collation": [{"fieldIndex": 0, "direction": "ASCENDING"}],
                "offset": None,
                "fetch": fetch,
                "inputs": [source],
                "rowType": source["rowType"],
            }

        normalized, evidence = cosette.preprocess_cosette_rel(
            sort(scan), bag_observation=True
        )
        self.assertEqual(normalized["type"], "LogicalTableScan")
        self.assertIn(
            "bag-only-bound-sort-erasure",
            {item["rule"] for item in evidence},
        )

        ordered, _ = cosette.preprocess_cosette_rel(
            sort(scan), bag_observation=False
        )
        self.assertEqual(ordered["type"], "LogicalSort")
        sliced, _ = cosette.preprocess_cosette_rel(
            sort(scan, fetch=0), bag_observation=True
        )
        self.assertEqual(sliced["type"], "LogicalSort")

        checked = {
            "type": "LogicalProject",
            "projects": ["+($0, 1)"],
            "inputs": [scan],
            "rowType": [self.row("x")],
        }
        risky, _ = cosette.preprocess_cosette_rel(
            sort(checked), bag_observation=True
        )
        self.assertEqual(risky["type"], "LogicalSort")

        # A keyless FETCH above an order-preserving Project consumes the
        # child's ordering even when the final observation is a bag.  Erasing
        # this inner sort would change which rows the slice selects.
        projected = {
            "type": "LogicalProject",
            "projects": ["$0"],
            "inputs": [sort(scan)],
            "rowType": scan["rowType"],
        }
        sliced_after_project = {
            "type": "LogicalSort",
            "collation": [],
            "offset": None,
            "fetch": 1,
            "inputs": [projected],
            "rowType": projected["rowType"],
        }
        retained, _ = cosette.preprocess_cosette_rel(
            sliced_after_project, bag_observation=True
        )
        self.assertEqual(
            retained["inputs"][0]["inputs"][0]["type"],
            "LogicalSort",
        )

    def test_root_bag_sort_erases_materialized_integer_aggregate_keys(self) -> None:
        scan = self.simple_scan()
        aggregate = {
            "type": "LogicalAggregate",
            "groupSet": "{0}",
            "aggCalls": ["COUNT()"],
            "inputs": [scan],
            "rowType": [self.row("x"), self.row("count", "BIGINT", False)],
        }
        ordered = {
            "type": "LogicalSort",
            "collation": [
                {"fieldIndex": 0, "direction": "ASCENDING"},
                {"fieldIndex": 1, "direction": "DESCENDING"},
            ],
            "offset": None,
            "fetch": None,
            "inputs": [aggregate],
            "rowType": aggregate["rowType"],
        }
        normalized, evidence = cosette.preprocess_cosette_rel(
            ordered, bag_observation=True
        )
        self.assertEqual(normalized["type"], "LogicalAggregate")
        self.assertIn(
            "bag-only-root-materialized-integer-sort-erasure",
            {item["rule"] for item in evidence},
        )

        string_scan = {
            **scan,
            "rowType": [self.row("x", "VARCHAR")],
        }
        string_aggregate = {
            **aggregate,
            "inputs": [string_scan],
            "rowType": [self.row("x", "VARCHAR"), self.row("count", "BIGINT", False)],
        }
        string_order = {
            **ordered,
            "collation": [{"fieldIndex": 0, "direction": "ASCENDING"}],
            "inputs": [string_aggregate],
            "rowType": string_aggregate["rowType"],
        }
        retained, _ = cosette.preprocess_cosette_rel(
            string_order, bag_observation=True
        )
        self.assertEqual(retained["type"], "LogicalSort")

    def test_list_boolean_normalization_is_closed_and_typed(self) -> None:
        integer_fields = [self.row("x")]
        left, _ = cosette.normalize_filter_condition(
            "AND(<>($0, 4), <>($0, 6))", integer_fields
        )
        right, _ = cosette.normalize_filter_condition(
            "NOT(OR(=($0, 4), =($0, 6)))", integer_fields
        )
        self.assertEqual(left, right)

        search, evidence = cosette.normalize_inner_join_condition(
            "AND(=($0, $1), SEARCH($0, Sarg[(-∞..4), (4..6), (6..+∞)]))",
            [self.row("x"), self.row("y")],
        )
        self.assertNotIn("SEARCH", search)
        self.assertIn(
            "finite-integer-exclusion-search-lowering",
            {item["rule"] for item in evidence},
        )

        integer_trichotomy, _ = cosette.normalize_filter_condition(
            "OR(<($0, 4), >($0, 4))", integer_fields
        )
        self.assertEqual(integer_trichotomy, "NOT(=($0, 4))")
        reordered, _ = cosette.normalize_filter_condition(
            "OR(=($0, 30), =($0, 10))", integer_fields
        )
        self.assertEqual(reordered, "OR(=($0, 10), =($0, 30))")
        string_trichotomy, _ = cosette.normalize_filter_condition(
            "OR(<($0, 'a'), >($0, 'a'))",
            [self.row("x", "VARCHAR")],
        )
        self.assertIn("OR", string_trichotomy)
        float_trichotomy, _ = cosette.normalize_filter_condition(
            "OR(<($0, 1), >($0, 1))",
            [self.row("x", "DOUBLE")],
        )
        self.assertIn("OR", float_trichotomy)

        malformed, _ = cosette.normalize_filter_condition(
            "SEARCH($0, Sarg[(-∞..4), (5..6), (6..+∞)])",
            integer_fields,
        )
        self.assertIn("SEARCH", malformed)
        null_as_true, _ = cosette.normalize_filter_condition(
            "SEARCH($0, Sarg[(-∞..4), (4..6), (6..+∞)]; NULL AS TRUE)",
            integer_fields,
        )
        self.assertIn("SEARCH", null_as_true)

    def test_nary_boolean_binarization_requires_error_free_direct_leaves(self) -> None:
        fields = [self.row("x"), self.row("y")]
        conjunction, evidence = cosette.normalize_filter_condition(
            "AND(=($0, 1), >($1, 2), <($0, 9))", fields
        )
        self.assertEqual(
            conjunction,
            "AND(AND(=($0, 1), >($1, 2)), <($0, 9))",
        )
        self.assertIn(
            "bool3-error-free-associative-binarization",
            {item["rule"] for item in evidence},
        )
        disjunction, _ = cosette.normalize_filter_condition(
            "OR(=($0, 1), =($0, 2), >($0, 9))", fields
        )
        self.assertEqual(
            disjunction,
            "OR(OR(=($0, 1), =($0, 2)), >($0, 9))",
        )

        checked = "OR(=($0, 1), >(+($0, 1), 2), =($1, 3))"
        retained, evidence = cosette.normalize_filter_condition(checked, fields)
        self.assertEqual(retained, checked)
        self.assertNotIn(
            "bool3-error-free-associative-binarization",
            {item["rule"] for item in evidence},
        )

    def test_paired_where_true_acceptance_is_exact_and_fail_closed(self) -> None:
        scan = {
            "type": "LogicalTableScan",
            "table": ["t"],
            "inputs": [],
            "rowType": [self.row("x"), self.row("y")],
        }

        def filtered(condition: str, source: dict | None = None) -> dict:
            child = source or scan
            return {
                "type": "LogicalFilter",
                "condition": condition,
                "inputs": [child],
                "rowType": child["rowType"],
            }

        excluded = filtered("OR(NOT(=($0, 7)), NOT(=($0, 8)))")
        nonnull = filtered("IS NOT NULL($0)")
        left, right, left_evidence, right_evidence = (
            cosette.preprocess_paired_where_true_acceptance(excluded, nonnull)
        )
        self.assertEqual(left["condition"], "true")
        self.assertEqual(right["condition"], "true")
        self.assertIn(
            "paired-where-bool3-true-acceptance-closure",
            {item["rule"] for item in left_evidence},
        )
        self.assertIn(
            "source-scalar-ir-rewrite-closure",
            {item["rule"] for item in right_evidence},
        )
        self.assertIsNotNone(
            cosette.attest_source_scalar_normalization(
                "SELECT x FROM t WHERE x IS NOT NULL",
                right_evidence,
            )
        )

        contradiction = filtered(
            "NOT(AND(=($0, 7), =($1, 8), =($0, 9)))"
        )
        explicit = filtered("OR(IS NOT NULL($0), NOT(=($1, 8)))")
        left, right, evidence, _ = (
            cosette.preprocess_paired_where_true_acceptance(
                contradiction, explicit
            )
        )
        self.assertEqual(left["condition"], "true")
        self.assertEqual(right["condition"], "true")
        self.assertTrue(evidence)

        varchar_scan = {
            **scan,
            "rowType": [self.row("x", "VARCHAR"), self.row("y")],
        }
        different_project = {
            "type": "LogicalProject",
            "projects": ["$0"],
            "inputs": [nonnull],
            "rowType": [self.row("x")],
        }
        nested_filter = filtered("=($1, 8)", nonnull)
        unsafe_pairs = (
            # Equal literals do not form a non-NULL tautology.
            (
                filtered("OR(NOT(=($0, 7)), NOT(=($0, 7)))"),
                nonnull,
            ),
            # The accepted non-NULL column must be the same.
            (excluded, filtered("IS NOT NULL($1)")),
            # Checked arithmetic and non-integer comparison domains are absent
            # from the closed acceptance proof.
            (
                filtered("NOT(AND(=(+($0, 1), 7), =($0, 8)))"),
                nonnull,
            ),
            (
                filtered(
                    "OR(NOT(=($0, 'a')), NOT(=($0, 'b')))",
                    varchar_scan,
                ),
                filtered("IS NOT NULL($0)", varchar_scan),
            ),
            # The whole relation apart from one corresponding WHERE condition
            # must match; nested/multiple filters and SELECT outputs are not
            # pair-normalized.
            (excluded, different_project),
            (excluded, nested_filter),
        )
        for unsafe_left, unsafe_right in unsafe_pairs:
            with self.subTest(left=unsafe_left, right=unsafe_right):
                retained_left, retained_right, left_evidence, right_evidence = (
                    cosette.preprocess_paired_where_true_acceptance(
                        unsafe_left, unsafe_right
                    )
                )
                self.assertEqual(retained_left, unsafe_left)
                self.assertEqual(retained_right, unsafe_right)
                self.assertFalse(left_evidence)
                self.assertFalse(right_evidence)

    def test_attested_nonnull_integer_contradiction_erases_only_safe_filter(
        self,
    ) -> None:
        scan = {
            "type": "LogicalTableScan",
            "table": ["t"],
            "inputs": [],
            "rowType": [self.row("x"), self.row("label", "VARCHAR")],
        }
        condition = "NOT(AND(=($0, 7), =($1, 'foo'), =($0, 8)))"
        filtered = {
            "type": "LogicalFilter",
            "condition": condition,
            "inputs": [scan],
            "rowType": scan["rowType"],
        }
        relation = {
            "type": "LogicalProject",
            "projects": ["$0"],
            "inputs": [filtered],
            "rowType": [self.row("x")],
        }
        tables = [
            cosette.Table(
                "t",
                [
                    cosette.Column("x", "int", "INTEGER"),
                    cosette.Column("label", "string", "VARCHAR"),
                ],
            )
        ]
        metadata = {"constraints": [{"not_null": {"value": "T__X"}}]}

        lowered, evidence = (
            cosette.preprocess_attested_nonnull_integer_contradiction_filter(
                relation,
                tables,
                metadata,
            )
        )
        self.assertEqual(lowered["inputs"], [scan])
        self.assertEqual(
            evidence[0]["rule"],
            "where-not-null-integer-contradiction-tautology",
        )
        self.assertTrue(
            evidence[0]["sideConditions"]["noShortCircuitOrEvaluationOrderAssumption"]
        )

        unsafe = (
            ({"constraints": []}, condition),
            (
                metadata,
                "NOT(AND(=(+($0, 1), 7), =($0, 8)))",
            ),
            (
                metadata,
                "NOT(AND(=($1, 'foo'), =($1, 'bar')))",
            ),
        )
        for unsafe_metadata, unsafe_condition in unsafe:
            with self.subTest(condition=unsafe_condition):
                candidate = json.loads(json.dumps(relation))
                candidate["inputs"][0]["condition"] = unsafe_condition
                retained, evidence = (
                    cosette.preprocess_attested_nonnull_integer_contradiction_filter(
                        candidate,
                        tables,
                        unsafe_metadata,
                    )
                )
                self.assertEqual(retained, candidate)
                self.assertFalse(evidence)

    def test_aggregate_pruning_never_hides_count_overflow_outcomes(self) -> None:
        condition = (
            "EXISTS({\n"
            "LogicalAggregate(group=[{}], EXPR$0=[COUNT()])\n"
            "  LogicalFilter(condition=[=($cor0.DEPTNO, $1)])\n"
            "    LogicalTableScan(table=[[EMP]])\n"
            "})"
        )
        normalized, evidence = cosette.normalize_filter_condition(
            condition, [self.row("x")]
        )
        # A global aggregate returns one row, but evaluating COUNT(*) can still
        # overflow PostgreSQL bigint.  Replacing EXISTS with TRUE would erase
        # that outcome in an evaluator that executes the aggregate.
        self.assertEqual(normalized, condition)
        self.assertFalse(evidence)

        scan = {
            "type": "LogicalTableScan",
            "table": ["t"],
            "inputs": [],
            "rowType": [self.row("x"), self.row("y")],
        }
        aggregate = {
            "type": "LogicalAggregate",
            "groupSet": "{1}",
            "aggCalls": ["COUNT()"],
            "inputs": [scan],
            "rowType": [self.row("y"), self.row("count", "BIGINT", False)],
        }
        having = {
            "type": "LogicalFilter",
            "condition": "=($0, 10)",
            "inputs": [aggregate],
            "rowType": aggregate["rowType"],
        }
        normalized, evidence = cosette.preprocess_cosette_rel(
            having, bag_observation=True
        )
        # Moving this HAVING below the aggregate would skip COUNT(*) for groups
        # rejected by the key predicate and could likewise hide overflow.
        self.assertEqual(normalized["type"], "LogicalFilter")
        self.assertEqual(normalized["inputs"][0]["type"], "LogicalAggregate")
        self.assertFalse(evidence)

    def test_union_all_branch_filters_remain_blocked_by_public_backend(self) -> None:
        tables = [cosette.Table("t", [cosette.Column("x", "int", "INTEGER")])]

        def branch(value: int, condition: str | None = None) -> dict:
            scan = self.simple_scan()
            return {
                "type": "LogicalFilter",
                "condition": condition or f"=($0, {value})",
                "inputs": [scan],
                "rowType": scan["rowType"],
            }

        plain_union = {
            "type": "LogicalUnion",
            "all": True,
            "setOp": "UNION",
            "inputs": [self.simple_scan(), self.simple_scan()],
            "rowType": [self.row("x")],
        }
        compiled = cosette.compile_union_all_candidate(
            plain_union,
            tables,
            "SELECT x FROM t UNION ALL SELECT x FROM t",
        )
        self.assertIsNotNone(compiled)

        # The branch compiler can construct these flat plans, and Cosette's
        # SQL parser accepts the emitted text, but the pinned public backend
        # fails in RosetteCodeGen at rosSelectList.  Do not advertise parser
        # acceptance as runnable tool compatibility.
        filtered_union = {
            **plain_union,
            "inputs": [branch(10), branch(20)],
        }
        self.assertIsNone(
            cosette.compile_union_all_candidate(
                filtered_union,
                tables,
                "SELECT x FROM t WHERE x = 10 UNION ALL SELECT x FROM t WHERE x = 20",
            )
        )

        checked = json.loads(json.dumps(filtered_union))
        checked["inputs"][0]["condition"] = ">(+($0, 1), 10)"
        self.assertIsNone(
            cosette.compile_union_all_candidate(
                checked,
                tables,
                "SELECT x FROM t WHERE x + 1 > 10 UNION ALL SELECT x FROM t WHERE x = 20",
            )
        )
        null_sensitive = json.loads(json.dumps(filtered_union))
        null_sensitive["inputs"][0]["condition"] = "IS NULL($0)"
        self.assertIsNone(
            cosette.compile_union_all_candidate(
                null_sensitive,
                tables,
                "SELECT x FROM t WHERE x IS NULL UNION ALL SELECT x FROM t WHERE x = 20",
            )
        )

    def test_case_acceptance_rules_reject_errorful_or_nonclosed_shapes(self) -> None:
        fields = [self.row("x"), self.row("y")]
        boolean_case, _ = cosette.normalize_filter_condition(
            "CASE(<($0, 10), true, false)", fields
        )
        self.assertEqual(boolean_case, "<($0, 10)")

        integer_case, _ = cosette.normalize_filter_condition(
            "=(CASE(=($0, 20), 2, =($0, 10), 1, 3), 1)", fields
        )
        self.assertEqual(integer_case, "=($0, 10)")

        duplicate_key, _ = cosette.normalize_filter_condition(
            "=(CASE(=($0, 10), 2, =($0, 10), 1, 3), 1)", fields
        )
        self.assertIn("CASE", duplicate_key)

        target_above_bound, _ = cosette.normalize_filter_condition(
            "=(CASE(>($0, 10), $1, $0), 11)", fields
        )
        self.assertIn("CASE", target_above_bound)

        null_case, _ = cosette.normalize_filter_condition(
            "OR(IS NULL(CASE(=($0, 10), null:INTEGER, 1)), "
            "IS NULL(CASE(=($0, 20), null:INTEGER, 1)))",
            fields,
        )
        self.assertEqual(null_case, "OR(=($0, 10), =($0, 20))")

        errorful_then, _ = cosette.normalize_filter_condition(
            "=(CASE(>($0, 1000), /($1, 0), $0), 1)", fields
        )
        self.assertIn("CASE", errorful_then)
        errorful_condition, _ = cosette.normalize_filter_condition(
            "IS NULL(CASE(>(/($0, 0), 1), null:INTEGER, 1))", fields
        )
        self.assertIn("CASE", errorful_condition)

    def test_source_scalar_waiver_requires_complete_exact_ir_occurrence_closure(self) -> None:
        scan = self.simple_scan()
        relation = {
            "type": "LogicalFilter",
            "condition": "CASE(<($0, 10), true, false)",
            "inputs": [scan],
            "rowType": scan["rowType"],
        }
        normalized, evidence = cosette.preprocess_cosette_rel(
            relation, bag_observation=True
        )
        self.assertEqual(normalized["condition"], "<($0, 10)")
        self.assertIsNotNone(
            cosette.attest_source_scalar_normalization(
                "SELECT x FROM t WHERE CASE WHEN x < 10 THEN TRUE ELSE FALSE END",
                evidence,
            )
        )
        closure = next(
            item
            for item in evidence
            if item["rule"] == "source-scalar-ir-rewrite-closure"
        )["sideConditions"]
        self.assertTrue(closure["closedRewriteSites"])
        self.assertTrue(
            all(
                site["beforeDigest"] != site["afterDigest"]
                for site in closure["closedRewriteSites"]
            )
        )
        self.assertIsNone(
            cosette.attest_source_scalar_normalization(
                "SELECT CASE WHEN x = 0 THEN 1 ELSE 2 END FROM t "
                "WHERE CASE WHEN x < 10 THEN TRUE ELSE FALSE END",
                evidence,
            )
        )

    def test_constant_case_requires_exact_source_to_rex_rewrite_binding(self) -> None:
        sql = "SELECT x + CASE WHEN 'a' = 'a' THEN 1 ELSE NULL END FROM t"
        before = "CASE(=('a', 'a'), 1, null:INTEGER)"
        closure = {
            "rule": "source-scalar-ir-rewrite-closure",
            "kind": "pair-safety",
            "sideConditions": {
                "originalRiskyOperatorCounts": {
                    "case": 1,
                    "null": 1,
                    "booleanTestOrLiteral": 0,
                },
                "remainingRiskyOperatorCounts": {
                    "case": 0,
                    "null": 0,
                    "booleanTestOrLiteral": 0,
                },
                "originalRiskyNodes": [
                    {
                        "feature": "case",
                        "path": "root.projects[0].args[1]",
                        "digest": before,
                    },
                    {
                        "feature": "null",
                        "path": "root.projects[0].args[1].args[2]",
                        "digest": "null:INTEGER",
                    },
                ],
                "remainingRiskyNodes": [],
                "closedRewriteSites": [
                    {
                        "path": "root.projects[0].args[1]",
                        "rule": "constant-true-integer-case-selection",
                        "beforeDigest": before,
                        "afterDigest": "1",
                    }
                ],
                "sourceBoundExactCalciteTree": True,
                "unhandledOperatorsRemainCompilerVisible": True,
            },
        }
        attested = cosette.attest_source_scalar_normalization(sql, [closure])
        self.assertIsNotNone(attested)
        evidence = next(
            item
            for item in attested
            if item["rule"] == "constant-true-integer-case-selection"
        )
        self.assertTrue(evidence["sideConditions"]["exactSourceAndRexRewrite"])
        self.assertEqual(evidence["sideConditions"]["rexBeforeDigest"], before)
        self.assertEqual(
            len(evidence["sideConditions"]["irRewriteClosureSha256"]),
            64,
        )

        # A folded RexLiteral carrying only sourceSql provenance is not an
        # auditable rewrite site.  This is the historical clean-Calcite shape.
        self.assertIsNone(cosette.attest_source_scalar_normalization(sql))
        incomplete = json.loads(json.dumps(closure))
        incomplete["sideConditions"]["closedRewriteSites"] = []
        self.assertIsNone(
            cosette.attest_source_scalar_normalization(sql, [incomplete])
        )
        wrong_rex = json.loads(json.dumps(closure))
        wrong_rex["sideConditions"]["closedRewriteSites"][0][
            "beforeDigest"
        ] = "CASE(=('a', 'b'), 1, null:INTEGER)"
        self.assertIsNone(
            cosette.attest_source_scalar_normalization(sql, [wrong_rex])
        )

        folded_project = {
            "type": "LogicalProject",
            "projects": ["+($0, 1)"],
            "inputs": [self.simple_scan()],
            "rowType": [self.row("newcol")],
        }
        tables = [
            cosette.Table("t", [cosette.Column("x", "int", "INTEGER")])
        ]
        self.assertIsNone(
            cosette.compile_cosette_candidate(folded_project, tables, sql)
        )


if __name__ == "__main__":
    unittest.main()
