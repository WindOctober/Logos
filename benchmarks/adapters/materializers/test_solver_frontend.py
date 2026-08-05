import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


MATERIALIZERS = Path(__file__).resolve().parent
if str(MATERIALIZERS) not in sys.path:
    sys.path.insert(0, str(MATERIALIZERS))

import solver_frontend  # noqa: E402


ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts"))
from logos_env import configured_path, load_logos_env  # noqa: E402

load_logos_env(ROOT)

PREFLIGHT = ROOT / "benchmarks/scripts/sqlsolver-preflight"
SQLSOLVER_JAR = configured_path(ROOT, "LOGOS_SQLSOLVER_JAR")
POLICY = solver_frontend.SQLSOLVER_POSTGRES_IDENTIFIER_POLICY


class SqlSolverBoundaryTest(unittest.TestCase):
    def materialize(self, sql: str, dialect: str = "postgres"):
        return solver_frontend.materialize_sqlsolver_query(
            sql,
            read_dialect=dialect,
            policy=POLICY,
        )

    def test_ordinary_and_correlated_identifiers_preserve_spelling(self) -> None:
        sql = (
            'SELECT "o"."id" FROM "orders" AS "o" '
            'WHERE EXISTS (SELECT 1 FROM "lineitem" AS "l" '
            'WHERE "l"."order_id" = "o"."id");'
        )
        output, report = self.materialize(sql)

        self.assertEqual(
            output,
            "SELECT o.id FROM orders AS o WHERE EXISTS "
            "(SELECT 1 FROM lineitem AS l WHERE l.order_id = o.id)\n",
        )
        self.assertTrue(report["semanticPreservation"]["established"])
        self.assertTrue(report["semanticPreservation"]["roleIndependent"])
        self.assertEqual(report["residualQuotedIdentifiers"], [])

    def test_reserved_case_sensitive_space_and_dollar_names_fail_closed(self) -> None:
        sql = (
            'SELECT "value", "system_user", "collation", "boolean" '
            'AS "Display Name", '
            '"MixedCase", "$f1" '
            'FROM "safe_table";'
        )
        output, report = self.materialize(sql)

        self.assertEqual(
            output,
            'SELECT "value", "system_user", "collation", "boolean" '
            'AS "Display Name", '
            '"MixedCase", "$f1" '
            "FROM safe_table\n",
        )
        self.assertFalse(report["semanticPreservation"]["established"])
        self.assertEqual(
            {
                (item["identifier"], item["reason"])
                for item in report["residualQuotedIdentifiers"]
            },
            {
                ("value", "source-or-target-keyword"),
                ("system_user", "source-or-target-keyword"),
                ("collation", "source-or-target-keyword"),
                ("boolean", "source-or-target-keyword"),
                ("Display Name", "not-simple-ascii-lowercase-identifier"),
                ("MixedCase", "not-simple-ascii-lowercase-identifier"),
                ("$f1", "not-simple-ascii-lowercase-identifier"),
            },
        )
        self.assertEqual(
            report["semanticPreservation"]["unsupportedDisposition"],
            "Unsupport: retain residual quotes and do not submit to prover",
        )

    def test_aggregate_and_alias_binding_are_not_rewritten_structurally(self) -> None:
        sql = (
            'SELECT "k", COALESCE(SUM("v"), 0) AS "total_v" '
            'FROM "t" GROUP BY "k" HAVING SUM("v") > 0 '
            'ORDER BY "total_v" DESC;'
        )
        output, report = self.materialize(sql)

        self.assertEqual(
            output,
            "SELECT k, COALESCE(SUM(v), 0) AS total_v FROM t GROUP BY k "
            "HAVING SUM(v) > 0 ORDER BY total_v DESC\n",
        )
        self.assertTrue(report["semanticPreservation"]["established"])
        self.assertTrue(report["semanticPreservation"]["outputLabelsPreserved"])
        self.assertTrue(report["semanticPreservation"]["bindingSpellingPreserved"])

    def test_rollup_set_operation_order_scope_and_null_ordering_survive(self) -> None:
        sql = (
            'SELECT "a", SUM("b") AS "s" FROM "t" GROUP BY ROLLUP ("a") '
            'UNION ALL SELECT "a", SUM("b") AS "s" FROM "u" GROUP BY "a" '
            'ORDER BY "a" NULLS LAST FETCH NEXT 5 ROWS ONLY;'
        )
        output, report = self.materialize(sql)

        self.assertEqual(
            output,
            "SELECT a, SUM(b) AS s FROM t GROUP BY ROLLUP (a) UNION ALL "
            "SELECT a, SUM(b) AS s FROM u GROUP BY a ORDER BY a NULLS LAST "
            "FETCH NEXT 5 ROWS ONLY\n",
        )
        self.assertTrue(report["semanticPreservation"]["established"])

    def test_cast_limit_fetch_and_quoted_literals_are_preserved(self) -> None:
        sql = (
            'SELECT CAST("amount" AS DECIMAL(12, 2)) AS "amount_cast", '
            '\'literal  with  spaces\' AS "label" FROM "sales" '
            'ORDER BY "amount_cast" NULLS FIRST LIMIT 10 OFFSET 2;'
        )
        output, report = self.materialize(sql)

        self.assertEqual(
            output,
            "SELECT CAST(amount AS DECIMAL(12, 2)) AS amount_cast, "
            "'literal  with  spaces' AS label FROM sales ORDER BY amount_cast "
            "NULLS FIRST LIMIT 10 OFFSET 2\n",
        )
        self.assertTrue(report["semanticPreservation"]["established"])

    def test_unattested_dialect_never_unquotes(self) -> None:
        output, report = self.materialize('SELECT "lower_name" FROM "t";', "mysql")

        self.assertEqual(output, 'SELECT "lower_name" FROM "t"\n')
        self.assertFalse(report["semanticPreservation"]["established"])
        self.assertTrue(
            all(
                item["reason"] == "dialect-has-no-attested-postgres-folding-contract"
                for item in report["residualQuotedIdentifiers"]
            )
        )

    def test_target_policy_is_independent_of_ingestion_adapter(self) -> None:
        benchmark = {
            "adapter": "none",
            "solverMaterialization": {
                "sqlsolver": {
                    "queryPolicy": POLICY,
                    "preflight": solver_frontend.SQLSOLVER_PREFLIGHT_POLICY,
                }
            },
        }
        self.assertEqual(
            solver_frontend.solver_materialization_config(benchmark, "sqlsolver"),
            benchmark["solverMaterialization"]["sqlsolver"],
        )
        self.assertIsNone(
            solver_frontend.solver_materialization_config(benchmark, "qed")
        )


@unittest.skipUnless(
    PREFLIGHT.is_file()
    and SQLSOLVER_JAR is not None
    and SQLSOLVER_JAR.is_file(),
    "SQLSolver frontend artifact is unavailable",
)
class ActualSqlSolverPreflightTest(unittest.TestCase):
    def run_preflight(
        self, sql1: str, sql2: str, *, timeout_seconds: int | None = None
    ) -> dict:
        with tempfile.TemporaryDirectory(prefix="sqlsolver-preflight-test-") as tmp:
            tmp_dir = Path(tmp)
            schema = tmp_dir / "schema.sql"
            before = tmp_dir / "sql1.sql"
            after = tmp_dir / "sql2.sql"
            schema.write_text("CREATE TABLE t (id INT);\n")
            before.write_text(sql1 + "\n")
            after.write_text(sql2 + "\n")
            command = [
                str(PREFLIGHT),
                "--schema",
                str(schema),
                "--sql1",
                str(before),
                "--sql2",
                str(after),
            ]
            if timeout_seconds is not None:
                command.extend(["--timeout-seconds", str(timeout_seconds)])
            completed = subprocess.run(
                command,
                cwd=ROOT,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                check=False,
            )
            self.assertEqual(completed.returncode, 0, completed.stderr)
            return json.loads(completed.stdout)

    def test_actual_target_parser_validator_and_planner_accept_pair(self) -> None:
        report = self.run_preflight("SELECT id FROM t", "SELECT t.id FROM t")

        self.assertEqual(report["status"], "planned")
        self.assertTrue(report["actualTargetFrontend"])
        self.assertFalse(report["proofSearchInvoked"])
        self.assertEqual(report["results"]["before"]["stage"], "planner")
        self.assertEqual(report["results"]["after"]["stage"], "planner")
        self.assertEqual(report["results"]["before"]["outputFields"], ["ID"])
        self.assertEqual(report["results"]["after"]["outputFields"], ["ID"])

    def test_validator_unsupported_is_not_reported_as_prover_unknown(self) -> None:
        report = self.run_preflight("SELECT id FROM t", "SELECT missing FROM t")

        self.assertEqual(report["status"], "unsupported")
        self.assertEqual(report["results"]["after"]["status"], "unsupported")
        self.assertEqual(report["results"]["after"]["stage"], "validator")

    def test_frontend_timeout_is_distinct_from_unknown(self) -> None:
        report = self.run_preflight(
            "SELECT id FROM t", "SELECT id FROM t", timeout_seconds=0
        )

        self.assertEqual(report["status"], "timeout")
        self.assertEqual(report["failureCategory"], "timeout-resource")
        self.assertFalse(report["proofSearchInvoked"])


if __name__ == "__main__":
    unittest.main()
