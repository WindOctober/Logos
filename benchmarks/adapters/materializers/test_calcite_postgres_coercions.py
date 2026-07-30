# ruff: noqa: E402

import hashlib
import json
import sys
import tempfile
import unittest
from pathlib import Path


MATERIALIZER_DIR = Path(__file__).resolve().parent
if str(MATERIALIZER_DIR) not in sys.path:
    sys.path.insert(0, str(MATERIALIZER_DIR))

from calcite_postgres_coercions import (
    CalciteCoercionError,
    materialize_calcite_coercions,
)


class CalcitePostgresCoercionTests(unittest.TestCase):
    benchmark_id = "verieql-calcite"
    case_id = "calcite-test"
    source_metadata = {
        "source": "benchmarks/core/verieql/calcite/calcite2.jsonlines",
        "line": 1,
        "benchmark": "Calcite-397",
        "name": None,
        "index": "test",
    }
    schema_sql = "CREATE TABLE DEPT (NAME VARCHAR);"

    def test_implicit_base_type_change_uses_exact_source_span(self) -> None:
        sql = "SELECT NAME IN (SELECT MGR FROM EMP) FROM DEPT"
        cast = self._implicit_cast(sql, "NAME", "VARCHAR", "INTEGER")

        materialized, report = self._materialize(sql, self._project(cast))

        self.assertEqual(
            materialized,
            "SELECT CAST(NAME AS INTEGER) IN (SELECT MGR FROM EMP) FROM DEPT",
        )
        self.assertIsNotNone(report)
        assert report is not None
        self.assertEqual(report["rewriteCount"], 1)
        self.assertEqual(report["rewrites"][0]["kind"], "calcite-implicit-rex-cast")
        self.assertNotIn("postgresNativeType", report["rewrites"][0])

    def test_null_coercions_keep_each_calcite_target_type(self) -> None:
        sql = "SELECT NULL AS n, NULL AS s"
        decimal = self._implicit_cast(
            sql,
            "NULL",
            "NULL",
            "DECIMAL",
            occurrence=0,
            precision=12,
            scale=2,
        )
        varchar = self._implicit_cast(
            sql,
            "NULL",
            "NULL",
            "VARCHAR",
            occurrence=1,
            precision=40,
        )

        materialized, report = self._materialize(sql, self._project(decimal, varchar))

        self.assertEqual(
            materialized,
            "SELECT CAST(NULL AS NUMERIC(12, 2)) AS n, "
            "CAST(NULL AS VARCHAR(40)) AS s",
        )
        assert report is not None
        self.assertEqual(report["rewriteCount"], 2)

    def test_aggregate_result_cast_restores_calcite_observable_type(self) -> None:
        sql = "SELECT SUM(total), AVG(quantity) FROM orders"
        aggregate = {
            "type": "LogicalAggregate",
            "inputs": [
                {
                    "rowType": [
                        {"name": "total", "type": "BIGINT"},
                        {"name": "quantity", "type": "INTEGER"},
                    ]
                }
            ],
            "aggCallDetails": [
                self._aggregate_call(sql, "SUM(total)", "SUM", "BIGINT", 0),
                self._aggregate_call(sql, "AVG(quantity)", "AVG", "INTEGER", 1),
            ],
        }

        materialized, report = self._materialize(sql, aggregate)

        self.assertEqual(
            materialized,
            "SELECT CAST(SUM(total) AS BIGINT), "
            "CAST(AVG(quantity) AS INTEGER) FROM orders",
        )
        assert report is not None
        self.assertEqual(
            [rewrite["postgresNativeType"] for rewrite in report["rewrites"]],
            ["NUMERIC", "NUMERIC"],
        )

    def test_common_aggregate_call_rewrites_every_source_occurrence(self) -> None:
        sql = "SELECT AVG(SAL), AVG(SAL) FROM EMP"
        aggregate_call = self._aggregate_call(sql, "AVG(SAL)", "AVG", "INTEGER", 0)
        second_occurrence = {
            "kind": "INPUT_REF",
            "type": "INTEGER",
            "sourceKind": "OTHER_FUNCTION",
            "sourceOperator": "AVG",
            "sourceNodeId": self._source_node_id(sql, "AVG(SAL)", 1),
            "sourceText": "AVG(SAL)",
        }
        relation = {
            "type": "LogicalProject",
            "projectRex": [aggregate_call, second_occurrence],
            "inputs": [
                {
                    "type": "LogicalAggregate",
                    "inputs": [{"rowType": [{"name": "sal", "type": "INTEGER"}]}],
                    "aggCallDetails": [aggregate_call],
                }
            ],
        }

        materialized, report = self._materialize(sql, relation)

        self.assertEqual(
            materialized,
            "SELECT CAST(AVG(SAL) AS INTEGER), " "CAST(AVG(SAL) AS INTEGER) FROM EMP",
        )
        assert report is not None
        self.assertEqual(report["rewriteCount"], 2)

    def test_decimal_and_numeric_aggregate_types_are_one_sql_family(self) -> None:
        sql = "SELECT SUM(amount) FROM orders"
        aggregate = {
            "type": "LogicalAggregate",
            "inputs": [{"rowType": [{"name": "amount", "type": "DECIMAL"}]}],
            "aggCallDetails": [
                self._aggregate_call(sql, "SUM(amount)", "SUM", "DECIMAL", 0)
            ],
        }

        materialized, report = self._materialize(sql, aggregate)

        self.assertEqual(materialized, sql)
        self.assertIsNone(report)

    def test_explicit_source_cast_is_not_materialized_again(self) -> None:
        sql = "SELECT CAST(NAME AS INTEGER) FROM DEPT"
        cast = self._implicit_cast(
            sql,
            "CAST(NAME AS INTEGER)",
            "VARCHAR",
            "INTEGER",
        )
        cast["sourceKind"] = "CAST"

        materialized, report = self._materialize(sql, self._project(cast))

        self.assertEqual(materialized, sql)
        self.assertIsNone(report)

    def test_nullability_only_cast_is_not_materialized(self) -> None:
        sql = "SELECT id FROM orders"
        cast = self._implicit_cast(sql, "id", "BIGINT", "BIGINT")
        cast.update({"precision": 19, "scale": 0, "nullable": False})
        cast["operands"][0].update({"precision": 19, "scale": 0, "nullable": True})

        materialized, report = self._materialize(sql, self._project(cast))

        self.assertEqual(materialized, sql)
        self.assertIsNone(report)

    def test_same_base_typmod_coercion_fails_closed(self) -> None:
        sql = "SELECT name FROM dept"
        cast = self._implicit_cast(
            sql,
            "name",
            "VARCHAR",
            "VARCHAR",
            precision=20,
        )
        cast["operands"][0]["precision"] = 10

        with self.assertRaisesRegex(
            CalciteCoercionError, "unsupported same-base typmod coercion"
        ):
            self._materialize(sql, self._project(cast))

    def test_stale_source_identity_fails_closed(self) -> None:
        sql = "SELECT NAME FROM DEPT"
        cast = self._implicit_cast(sql, "NAME", "VARCHAR", "INTEGER")
        cast["sourceText"] = "MGR"

        with self.assertRaisesRegex(CalciteCoercionError, "no longer matches"):
            self._materialize(sql, self._project(cast))

    def test_generated_query_text_must_match_current_source(self) -> None:
        sql = "SELECT NAME FROM DEPT"
        cast = self._implicit_cast(sql, "NAME", "VARCHAR", "INTEGER")

        with self.assertRaisesRegex(CalciteCoercionError, "does not describe"):
            self._materialize(
                sql,
                self._project(cast),
                submitted_sql="SELECT MGR FROM EMP",
            )

    def test_overlapping_rewrites_fail_closed(self) -> None:
        sql = "SELECT AVG(quantity) FROM orders"
        aggregate_call = self._aggregate_call(sql, "AVG(quantity)", "AVG", "INTEGER", 0)
        overlapping_cast = self._implicit_cast(sql, "quantity", "VARCHAR", "INTEGER")
        aggregate = {
            "type": "LogicalAggregate",
            "inputs": [{"rowType": [{"name": "quantity", "type": "INTEGER"}]}],
            "aggCallDetails": [aggregate_call],
            "nestedEvidence": overlapping_cast,
        }

        with self.assertRaisesRegex(CalciteCoercionError, "overlapping"):
            self._materialize(sql, aggregate)

    def test_unknown_target_type_fails_closed(self) -> None:
        sql = "SELECT x FROM t"
        cast = self._implicit_cast(sql, "x", "INTEGER", "ARRAY")

        with self.assertRaisesRegex(CalciteCoercionError, "unsupported.*ARRAY"):
            self._materialize(sql, self._project(cast))

    def test_unreviewed_source_target_pair_fails_closed(self) -> None:
        sql = "SELECT x FROM t"
        cast = self._implicit_cast(sql, "x", "ARRAY", "INTEGER")

        with self.assertRaisesRegex(
            CalciteCoercionError,
            "unsupported implicit Calcite coercion from ARRAY to INTEGER",
        ):
            self._materialize(sql, self._project(cast))

    def test_malformed_implicit_cast_fails_closed(self) -> None:
        sql = "SELECT x FROM t"
        cast = self._implicit_cast(sql, "x", "VARCHAR", "INTEGER")
        cast["operands"] = []

        with self.assertRaisesRegex(
            CalciteCoercionError, "malformed implicit Calcite CAST"
        ):
            self._materialize(sql, self._project(cast))

    def test_metadata_must_bind_the_original_case(self) -> None:
        sql = "SELECT NAME FROM DEPT"
        cast = self._implicit_cast(sql, "NAME", "VARCHAR", "INTEGER")

        with self.assertRaisesRegex(CalciteCoercionError, "source does not match"):
            self._materialize(
                sql,
                self._project(cast),
                metadata_source={**self.source_metadata, "line": 2},
            )

    def test_metadata_must_bind_the_source_schema(self) -> None:
        sql = "SELECT NAME FROM DEPT"
        cast = self._implicit_cast(sql, "NAME", "VARCHAR", "INTEGER")

        with self.assertRaisesRegex(CalciteCoercionError, "schema does not match"):
            self._materialize(
                sql,
                self._project(cast),
                metadata_schema="CREATE TABLE DEPT (NAME INTEGER);",
            )

    def test_other_benchmarks_are_unchanged_without_calcite_authority(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            sql = "SELECT x FROM t"
            materialized, report = materialize_calcite_coercions(
                repository_root=Path(tmp),
                authority_root=Path(tmp) / "missing",
                benchmark_id="verieql-literature",
                case_id="example",
                source_metadata={},
                schema_sql="CREATE TABLE t (x INTEGER);",
                side="before",
                sql=sql,
            )

        self.assertEqual(materialized, sql)
        self.assertIsNone(report)

    def _materialize(
        self,
        sql: str,
        relation: dict,
        *,
        submitted_sql: str | None = None,
        metadata_source: dict | None = None,
        metadata_schema: str | None = None,
    ):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            authority_root = root / "authority"
            case_root = authority_root / self.benchmark_id / self.case_id
            case_root.mkdir(parents=True)
            (case_root / "metadata.json").write_text(
                json.dumps(
                    {
                        "sourceBenchmark": self.benchmark_id,
                        "sourceCase": self.case_id,
                        "source": metadata_source or self.source_metadata,
                        "sourceSchemaSha256": hashlib.sha256(
                            (metadata_schema or self.schema_sql).encode()
                        ).hexdigest(),
                    }
                )
            )
            (case_root / "before.calcite-ir.json").write_text(
                json.dumps(
                    {
                        "queries": [
                            {
                                "sql": submitted_sql or sql,
                                "rel": relation,
                            }
                        ]
                    }
                )
            )
            return materialize_calcite_coercions(
                repository_root=root,
                authority_root=authority_root,
                benchmark_id=self.benchmark_id,
                case_id=self.case_id,
                source_metadata=self.source_metadata,
                schema_sql=self.schema_sql,
                side="before",
                sql=sql,
            )

    @staticmethod
    def _project(*expressions: dict) -> dict:
        return {"type": "LogicalProject", "projects": list(expressions)}

    @classmethod
    def _implicit_cast(
        cls,
        sql: str,
        source_text: str,
        source_type: str,
        target_type: str,
        *,
        occurrence: int = 0,
        precision: int | None = None,
        scale: int | None = None,
    ) -> dict:
        node = {
            "kind": "CAST",
            "type": target_type,
            "sourceKind": "IDENTIFIER",
            "sourceNodeId": cls._source_node_id(sql, source_text, occurrence),
            "sourceText": source_text,
            "operands": [{"kind": "INPUT_REF", "type": source_type}],
        }
        if precision is not None:
            node["precision"] = precision
        if scale is not None:
            node["scale"] = scale
        return node

    @classmethod
    def _aggregate_call(
        cls,
        sql: str,
        source_text: str,
        operator: str,
        result_type: str,
        argument: int,
    ) -> dict:
        return {
            "kind": operator,
            "function": operator,
            "type": result_type,
            "sourceKind": "OTHER_FUNCTION",
            "sourceOperator": operator,
            "sourceNodeId": cls._source_node_id(sql, source_text),
            "sourceText": source_text,
            "argList": [argument],
        }

    @staticmethod
    def _source_node_id(sql: str, text: str, occurrence: int = 0) -> str:
        start = -1
        for _ in range(occurrence + 1):
            start = sql.index(text, start + 1)
        end = start + len(text) - 1
        return f"1:{start + 1}-1:{end + 1}"


if __name__ == "__main__":
    unittest.main()
