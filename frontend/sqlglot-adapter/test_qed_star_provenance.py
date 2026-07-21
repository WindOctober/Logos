import copy
import unittest

import qed_projection as projection
import qed_star_provenance as provenance


def row_type(columns):
    return [
        {"name": name, "type": type_name, "nullable": True}
        for name, type_name in columns
    ]


def table_scan(table, columns):
    return {
        "type": "LogicalTableScan",
        "table": [table],
        "inputs": [],
        "rowType": row_type(columns),
    }


def direct_project(source, indexes, columns):
    return {
        "type": "LogicalProject",
        "inputs": [source],
        "projects": [f"${index}" for index in indexes],
        "rowType": row_type(columns),
    }


def typed_input_ref(index, type_name="INTEGER", nullable=True):
    return {
        "class": "RexInputRef",
        "kind": "INPUT_REF",
        "index": index,
        "text": f"${index}",
        "type": type_name,
        "fullType": type_name,
        "nullable": nullable,
    }


EMP_COLUMNS = [
    ("EMPNO", "INTEGER"),
    ("DEPTNO", "INTEGER"),
    ("ENAME", "VARCHAR"),
]
DEPT_COLUMNS = [("DEPTNO", "INTEGER"), ("NAME", "VARCHAR")]
CALCITE_SCHEMA = [
    {
        "name": "EMP",
        "columns": [
            {"name": name, "type": type_name} for name, type_name in EMP_COLUMNS
        ],
    },
    {
        "name": "DEPT",
        "columns": [
            {"name": name, "type": type_name} for name, type_name in DEPT_COLUMNS
        ],
    },
]


class BaseUseClosureTests(unittest.TestCase):
    def test_grouped_derived_output_is_not_rewritten(self) -> None:
        schema = {
            "customer": {"c_custkey": "INTEGER", "dead": "VARCHAR"},
            "orders": {
                "o_orderkey": "INTEGER",
                "o_custkey": "INTEGER",
                "o_comment": "VARCHAR",
            },
        }
        sql = (
            "SELECT c_count, COUNT(*) FROM ("
            "SELECT c_custkey, COUNT(o_orderkey) FROM customer LEFT JOIN orders "
            "ON c_custkey = o_custkey AND o_comment NOT LIKE '%pending%' "
            "GROUP BY c_custkey) AS c_orders(c_custkey, c_count) GROUP BY c_count"
        )

        report = projection.analyze_base_use_query(sql, schema)

        self.assertTrue(report["queryBytesPreserved"])
        self.assertEqual(report["baseColumns"]["customer"], ["c_custkey"])
        self.assertEqual(
            set(report["baseColumns"]["orders"]),
            {"o_orderkey", "o_custkey", "o_comment"},
        )
        self.assertNotIn("dead", report["baseColumns"]["customer"])

    def test_row_shape_sensitive_constructs_fail_closed(self) -> None:
        schema = {
            "t": {"id": "INTEGER", "payload": "VARCHAR"},
            "u": {"id": "INTEGER", "payload": "VARCHAR"},
        }
        unsafe = (
            "SELECT * FROM t",
            "SELECT t.* FROM t",
            "SELECT t FROM t",
            "SELECT 1 FROM t NATURAL JOIN u",
            "SELECT 1 FROM t JOIN u USING (id)",
            "WITH t AS (SELECT id FROM u) SELECT id FROM t",
        )
        for sql in unsafe:
            with self.subTest(sql=sql), self.assertRaises(ValueError):
                projection.analyze_base_use_query(sql, schema)


class SourceStarProvenanceTests(unittest.TestCase):
    def test_calcite58_like_right_join_uses_left_to_right_from_order(self) -> None:
        sql = (
            "SELECT * FROM "
            "(SELECT * FROM EMP WHERE DEPTNO = EMPNO) AS t0 "
            "RIGHT JOIN DEPT AS DEPT0 ON t0.DEPTNO = DEPT0.DEPTNO"
        )

        report = provenance.expand_top_level_unqualified_star(sql, CALCITE_SCHEMA)

        self.assertEqual(
            report["rewrittenSql"],
            "SELECT t0.EMPNO, t0.DEPTNO, t0.ENAME, "
            "DEPT0.DEPTNO, DEPT0.NAME FROM "
            "(SELECT * FROM EMP WHERE DEPTNO = EMPNO) AS t0 "
            "RIGHT JOIN DEPT AS DEPT0 ON t0.DEPTNO = DEPT0.DEPTNO",
        )
        self.assertEqual(report["sourceStar"], {"start": 7, "end": 7, "text": "*"})
        self.assertEqual(
            [output["sourceExpression"] for output in report["outputs"]],
            [
                "t0.EMPNO",
                "t0.DEPTNO",
                "t0.ENAME",
                "DEPT0.DEPTNO",
                "DEPT0.NAME",
            ],
        )
        self.assertEqual(report["outputs"][0]["aliasPath"], ["EMP", "t0"])
        self.assertEqual(
            [output["origin"]["scanOccurrence"] for output in report["outputs"]],
            [0, 0, 0, 1, 1],
        )
        self.assertEqual(
            [output["origin"]["column"] for output in report["outputs"]],
            ["EMPNO", "DEPTNO", "ENAME", "DEPTNO", "NAME"],
        )

    def test_only_root_star_span_changes_and_inner_star_is_preserved(self) -> None:
        sql = (
            "SELECT /* retain this */ *\n"
            "FROM (SELECT * FROM EMP WHERE DEPTNO = EMPNO) AS t0"
        )

        report = provenance.expand_top_level_unqualified_star(sql, CALCITE_SCHEMA)
        span = report["sourceStar"]
        replacement = "t0.EMPNO, t0.DEPTNO, t0.ENAME"

        self.assertEqual(
            report["rewrittenSql"],
            sql[: span["start"]] + replacement + sql[span["end"] + 1 :],
        )
        self.assertIn("/* retain this */", report["rewrittenSql"])
        self.assertIn("(SELECT * FROM EMP", report["rewrittenSql"])

    def test_every_ordinary_on_join_kind_and_cross_join_concatenate(self) -> None:
        schema = [
            {"name": "A", "columns": [{"name": "X", "type": "INTEGER"}]},
            {"name": "B", "columns": [{"name": "Y", "type": "INTEGER"}]},
        ]
        joins = (
            "JOIN B ON A.X = B.Y",
            "INNER JOIN B ON A.X = B.Y",
            "LEFT JOIN B ON A.X = B.Y",
            "RIGHT JOIN B ON A.X = B.Y",
            "FULL JOIN B ON A.X = B.Y",
            "CROSS JOIN B",
        )
        for join in joins:
            with self.subTest(join=join):
                report = provenance.expand_top_level_unqualified_star(
                    f"SELECT * FROM A {join}", schema
                )
                self.assertTrue(
                    report["rewrittenSql"].startswith("SELECT A.X, B.Y FROM")
                )
                self.assertEqual(
                    [
                        output["origin"]["scanOccurrence"]
                        for output in report["outputs"]
                    ],
                    [0, 1],
                )

    def test_direct_pass_through_alias_retains_base_lineage(self) -> None:
        report = provenance.expand_top_level_unqualified_star(
            "SELECT * FROM (SELECT EMPNO AS E, ENAME FROM EMP) AS d",
            CALCITE_SCHEMA,
        )

        self.assertEqual(
            report["rewrittenSql"],
            "SELECT d.E, d.ENAME FROM (SELECT EMPNO AS E, ENAME FROM EMP) AS d",
        )
        self.assertEqual(
            [output["origin"]["column"] for output in report["outputs"]],
            ["EMPNO", "ENAME"],
        )
        self.assertEqual(report["outputs"][0]["aliasPath"], ["EMP", "d"])

    def test_duplicate_derived_labels_are_rejected(self) -> None:
        with self.assertRaisesRegex(
            provenance.ProvenanceError, "duplicate output labels"
        ):
            provenance.expand_top_level_unqualified_star(
                "SELECT * FROM "
                "(SELECT EMPNO, DEPTNO AS EMPNO FROM EMP) AS duplicate_labels",
                CALCITE_SCHEMA,
            )

    def test_unsupported_surface_shapes_fail_closed(self) -> None:
        cases = {
            "using": "SELECT * FROM EMP JOIN DEPT USING (DEPTNO)",
            "natural": "SELECT * FROM EMP NATURAL JOIN DEPT",
            "cte": "WITH e AS (SELECT * FROM EMP) SELECT * FROM e",
            "set-op": "SELECT * FROM EMP UNION ALL SELECT * FROM EMP",
            "quoted": 'SELECT * FROM "EMP"',
            "computed-derived": (
                "SELECT * FROM (SELECT EMPNO + 1 AS EMPNO FROM EMP) AS e"
            ),
            "qualified-star": "SELECT EMP.* FROM EMP",
            "comma-join": "SELECT * FROM EMP, DEPT",
        }
        for name, sql in cases.items():
            with self.subTest(name=name), self.assertRaises(provenance.ProvenanceError):
                provenance.expand_top_level_unqualified_star(sql, CALCITE_SCHEMA)


class CalciteProvenanceTests(unittest.TestCase):
    @staticmethod
    def calcite58_like_rel():
        emp_scan = table_scan("EMP", EMP_COLUMNS)
        emp_filter = {
            "type": "LogicalFilter",
            "inputs": [emp_scan],
            "condition": "=($1, $0)",
            "rowType": row_type(EMP_COLUMNS),
        }
        derived = direct_project(emp_filter, [0, 1, 2], EMP_COLUMNS)
        dept_scan = table_scan("DEPT", DEPT_COLUMNS)
        join_columns = [
            ("EMPNO", "INTEGER"),
            ("DEPTNO", "INTEGER"),
            ("ENAME", "VARCHAR"),
            ("DEPTNO0", "INTEGER"),
            ("NAME", "VARCHAR"),
        ]
        join = {
            "type": "LogicalJoin",
            "inputs": [derived, dept_scan],
            "condition": "=($1, $3)",
            "joinType": "RIGHT",
            "rowType": row_type(join_columns),
        }
        return direct_project(join, [0, 1, 2, 3, 4], join_columns)

    def test_calcite58_like_direct_lineage_matches_source(self) -> None:
        source = provenance.expand_top_level_unqualified_star(
            "SELECT * FROM "
            "(SELECT * FROM EMP WHERE DEPTNO = EMPNO) AS t0 "
            "RIGHT JOIN DEPT AS DEPT0 ON t0.DEPTNO = DEPT0.DEPTNO",
            CALCITE_SCHEMA,
        )
        rel = self.calcite58_like_rel()
        original_rel = copy.deepcopy(rel)
        original_outputs = copy.deepcopy(source["outputs"])

        result = provenance.validate_calcite_rel_direct_provenance(
            rel, CALCITE_SCHEMA, source["outputs"]
        )

        self.assertEqual(result["status"], "verified-calcite-direct-output-provenance")
        self.assertEqual(
            [output["origin"] for output in result["outputs"]],
            [output["origin"] for output in source["outputs"]],
        )
        self.assertEqual(rel, original_rel)
        self.assertEqual(source["outputs"], original_outputs)

    def test_same_typed_calcite_reorder_is_rejected_by_provenance(self) -> None:
        schema = [
            {
                "name": "T",
                "columns": [
                    {"name": "A", "type": "INTEGER"},
                    {"name": "B", "type": "INTEGER"},
                ],
            }
        ]
        source = provenance.expand_top_level_unqualified_star(
            "SELECT * FROM T", schema
        )
        rel = direct_project(
            table_scan("T", [("A", "INTEGER"), ("B", "INTEGER")]),
            [1, 0],
            [("B", "INTEGER"), ("A", "INTEGER")],
        )

        with self.assertRaisesRegex(
            provenance.ProvenanceError, "provenance disagrees at ordinal 0"
        ):
            provenance.validate_calcite_rel_direct_provenance(
                rel, schema, source["outputs"]
            )

    def test_computed_calcite_project_is_rejected(self) -> None:
        schema = [
            {
                "name": "T",
                "columns": [
                    {"name": "A", "type": "INTEGER"},
                    {"name": "B", "type": "INTEGER"},
                ],
            }
        ]
        source = provenance.expand_top_level_unqualified_star(
            "SELECT * FROM T", schema
        )
        rel = direct_project(
            table_scan("T", [("A", "INTEGER"), ("B", "INTEGER")]),
            [0, 1],
            [("A", "INTEGER"), ("B", "INTEGER")],
        )
        rel["projects"][0] = "+($0, 1)"

        with self.assertRaisesRegex(provenance.ProvenanceError, "computed expression"):
            provenance.validate_calcite_rel_direct_provenance(
                rel, schema, source["outputs"]
            )

    def test_structured_calcite_rex_refs_are_direct_and_computed_rex_fails(
        self,
    ) -> None:
        schema = [
            {
                "name": "T",
                "columns": [
                    {"name": "A", "type": "INTEGER"},
                    {"name": "B", "type": "INTEGER"},
                ],
            }
        ]
        source = provenance.expand_top_level_unqualified_star(
            "SELECT * FROM T", schema
        )
        rel = direct_project(
            table_scan("T", [("A", "INTEGER"), ("B", "INTEGER")]),
            [0, 1],
            [("A", "INTEGER"), ("B", "INTEGER")],
        )
        rel.pop("projects")
        rel["projectRex"] = [
            typed_input_ref(index)
            for index in (0, 1)
        ]

        provenance.validate_calcite_rel_direct_provenance(
            rel,
            schema,
            source["outputs"],
        )
        rel["projectRex"][0] = {
            "class": "RexCall",
            "kind": "PLUS",
            "text": "+($0, 1)",
            "type": "INTEGER",
        }
        with self.assertRaisesRegex(
            provenance.ProvenanceError,
            "computed Rex expression",
        ):
            provenance.validate_calcite_rel_direct_provenance(
                rel,
                schema,
                source["outputs"],
            )

    def test_matching_legacy_and_typed_project_encodings_are_bound(self) -> None:
        schema = [
            {
                "name": "T",
                "columns": [
                    {"name": "A", "type": "INTEGER"},
                    {"name": "B", "type": "INTEGER"},
                ],
            }
        ]
        source = provenance.expand_top_level_unqualified_star("SELECT * FROM T", schema)
        rel = direct_project(
            table_scan("T", [("A", "INTEGER"), ("B", "INTEGER")]),
            [0, 1],
            [("A", "INTEGER"), ("B", "INTEGER")],
        )
        rel["projectRex"] = [typed_input_ref(0), typed_input_ref(1)]

        result = provenance.validate_calcite_rel_direct_provenance(
            rel, schema, source["outputs"]
        )

        self.assertEqual(
            result["status"], "verified-calcite-direct-output-provenance"
        )

    def test_dual_project_encodings_fail_closed_on_mismatch(self) -> None:
        schema = [
            {
                "name": "T",
                "columns": [
                    {"name": "A", "type": "INTEGER"},
                    {"name": "B", "type": "INTEGER"},
                ],
            }
        ]
        source = provenance.expand_top_level_unqualified_star("SELECT * FROM T", schema)

        for name, rex in (
            ("missing", [typed_input_ref(0)]),
            ("conflicting", [typed_input_ref(0), typed_input_ref(0)]),
            ("reordered", [typed_input_ref(1), typed_input_ref(0)]),
        ):
            with self.subTest(name=name):
                rel = direct_project(
                    table_scan("T", [("A", "INTEGER"), ("B", "INTEGER")]),
                    [0, 1],
                    [("A", "INTEGER"), ("B", "INTEGER")],
                )
                rel["projectRex"] = rex
                with self.assertRaisesRegex(
                    provenance.ProvenanceError,
                    "conflicting expression encodings",
                ):
                    provenance.validate_calcite_rel_direct_provenance(
                        rel, schema, source["outputs"]
                    )

    def test_typed_project_requires_complete_envelope(self) -> None:
        schema = [{"name": "T", "columns": [{"name": "A", "type": "INTEGER"}]}]
        source = provenance.expand_top_level_unqualified_star("SELECT * FROM T", schema)
        for field in ("type", "fullType", "nullable"):
            with self.subTest(field=field):
                rel = direct_project(
                    table_scan("T", [("A", "INTEGER")]),
                    [0],
                    [("A", "INTEGER")],
                )
                rel.pop("projects")
                expression = typed_input_ref(0)
                expression.pop(field)
                rel["projectRex"] = [expression]
                with self.assertRaisesRegex(
                    provenance.ProvenanceError,
                    "computed Rex expression",
                ):
                    provenance.validate_calcite_rel_direct_provenance(
                        rel, schema, source["outputs"]
                    )

    def test_root_sort_preserves_direct_project_provenance(self) -> None:
        schema = [
            {
                "name": "T",
                "columns": [
                    {"name": "A", "type": "INTEGER"},
                    {"name": "B", "type": "INTEGER"},
                ],
            }
        ]
        source = provenance.expand_top_level_unqualified_star(
            "SELECT * FROM T ORDER BY A FETCH NEXT 2 ROWS ONLY",
            schema,
        )
        project = direct_project(
            table_scan("T", [("A", "INTEGER"), ("B", "INTEGER")]),
            [0, 1],
            [("A", "INTEGER"), ("B", "INTEGER")],
        )
        rel = {
            "type": "LogicalSort",
            "inputs": [project],
            "rowType": row_type([("A", "INTEGER"), ("B", "INTEGER")]),
        }

        validation = provenance.validate_calcite_rel_direct_provenance(
            rel,
            schema,
            source["outputs"],
        )
        self.assertEqual(
            validation["status"],
            "verified-calcite-direct-output-provenance",
        )


class QedProvenanceTests(unittest.TestCase):
    def setUp(self) -> None:
        self.schema = [
            {
                "name": "EMP",
                "columns": [
                    {"name": "EMPNO", "type": "INTEGER"},
                    {"name": "DEPTNO", "type": "INTEGER"},
                    {"name": "COMM", "type": "INTEGER"},
                ],
            }
        ]
        self.source = provenance.expand_top_level_unqualified_star(
            "SELECT * FROM EMP", self.schema
        )
        self.qed_schemas = [
            {
                "name": "EMP",
                # QED stores the same declaration in name-sorted order.
                "fields": ["COMM", "DEPTNO", "EMPNO"],
                "types": ["INTEGER", "INTEGER", "INTEGER"],
            }
        ]

    @staticmethod
    def project(indexes):
        return {
            "project": {
                "source": {"scan": 0},
                "target": [{"column": index, "type": "INTEGER"} for index in indexes],
            }
        }

    def test_qed_name_sorted_schema_is_recovered_by_direct_targets(self) -> None:
        query = self.project([2, 1, 0])
        original_query = copy.deepcopy(query)

        result = provenance.validate_qed_json_direct_provenance(
            query,
            self.qed_schemas,
            self.source["outputs"],
            ["INTEGER", "INTEGER", "INTEGER"],
        )

        self.assertEqual(result["status"], "verified-qed-direct-output-provenance")
        self.assertEqual(
            [output["origin"]["column"] for output in result["outputs"]],
            ["EMPNO", "DEPTNO", "COMM"],
        )
        self.assertEqual(
            [output["origin"]["parserColumnOrdinal"] for output in result["outputs"]],
            [2, 1, 0],
        )
        self.assertEqual(query, original_query)

    def test_same_typed_qed_reorder_is_rejected_by_provenance(self) -> None:
        # A type-only check would accept this name-sorted [COMM, DEPTNO, EMPNO]
        # output because every field is INTEGER.
        query = self.project([0, 1, 2])

        with self.assertRaisesRegex(
            provenance.ProvenanceError, "provenance disagrees at ordinal 0"
        ):
            provenance.validate_qed_json_direct_provenance(
                query,
                self.qed_schemas,
                self.source["outputs"],
                ["INTEGER", "INTEGER", "INTEGER"],
            )

    def test_computed_qed_target_is_rejected(self) -> None:
        query = self.project([2, 1, 0])
        query["project"]["target"][0] = {
            "operator": "+",
            "operand": [],
            "type": "INTEGER",
        }

        with self.assertRaisesRegex(provenance.ProvenanceError, "not a direct column"):
            provenance.validate_qed_json_direct_provenance(
                query,
                self.qed_schemas,
                self.source["outputs"],
                ["INTEGER", "INTEGER", "INTEGER"],
            )

    def test_qed_sort_wrapper_preserves_direct_project_provenance(self) -> None:
        query = {
            "sort": {
                "source": self.project([2, 1, 0]),
                "collation": [[0, "ASCENDING", "LAST"]],
                "offset": None,
                "limit": None,
            }
        }

        validation = provenance.validate_qed_json_direct_provenance(
            query,
            self.qed_schemas,
            self.source["outputs"],
            ["INTEGER", "INTEGER", "INTEGER"],
        )
        self.assertEqual(
            validation["status"],
            "verified-qed-direct-output-provenance",
        )


if __name__ == "__main__":
    unittest.main()
