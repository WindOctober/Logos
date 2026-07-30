import unittest
from unittest import mock

import normalize


class CompatibilityPatchLexingTests(unittest.TestCase):
    def test_interval_patch_requires_a_standalone_postgres_keyword(self) -> None:
        normalizations: list[dict] = []

        patched = normalize.patch_calcite_interval_literals(
            "INTERVAL '14 DAYS'", normalizations
        )

        self.assertEqual(patched, "INTERVAL '14' DAY")
        self.assertEqual(len(normalizations), 1)
        self.assertEqual(normalizations[0]["kind"], "calcite_interval_literal")

    def test_interval_patch_rejects_identifier_and_non_ascii_adjacency(self) -> None:
        cases = (
            "myinterval '14 DAYS'",
            "interval_name '14 DAYS'",
            "interval$ '14 DAYS'",
            "interval.foo '14 DAYS'",
            "schema.interval '14 DAYS'",
            "$interval '14 DAYS'",
            "éinterval '14 DAYS'",
            "intervalé '14 DAYS'",
            "İNTERVAL '14 DAYS'",
            "ıNTERVAL '14 DAYS'",
            "INTERVAL\u00a0'14 DAYS'",
            "\u00a0INTERVAL '14 DAYS'",
        )
        for sql in cases:
            with self.subTest(sql=sql):
                normalizations: list[dict] = []

                patched = normalize.patch_calcite_interval_literals(
                    sql, normalizations
                )

                self.assertEqual(patched, sql)
                self.assertEqual(normalizations, [])

    def test_interval_patch_ignores_protected_regions(self) -> None:
        sql = (
            "INTERVAL '14 DAYS', "
            "'INTERVAL ''21 DAYS''', "
            '"INTERVAL \'28 DAYS\'", '
            "`INTERVAL '35 DAYS'`, "
            "ARRAY[INTERVAL '42 DAYS'], "
            "-- INTERVAL '49 DAYS'\n"
            "/* INTERVAL '56 DAYS' */ $$INTERVAL '63 DAYS'$$"
        )
        normalizations: list[dict] = []

        patched = normalize.patch_calcite_interval_literals(sql, normalizations)

        self.assertIn("INTERVAL '14' DAY", patched)
        self.assertIn("ARRAY[INTERVAL '42' DAY]", patched)
        for protected in (
            "INTERVAL ''21 DAYS''",
            "INTERVAL '28 DAYS'",
            "INTERVAL '35 DAYS'",
            "INTERVAL '49 DAYS'",
            "INTERVAL '56 DAYS'",
            "INTERVAL '63 DAYS'",
        ):
            self.assertIn(protected, patched)
        self.assertEqual(len(normalizations), 2)
        self.assertEqual(normalizations[0]["source"], "INTERVAL '14 DAYS'")

    def test_postgres_ordinary_quotes_do_not_enable_backslash_escapes(self) -> None:
        sql = (
            r'''SELECT '\' AS payload, "identifier\" AS label, '''
            r'''INTERVAL '14 DAYS', "INTERVAL '21 DAYS'"'''
        )
        normalizations: list[dict] = []

        patched = normalize.patch_calcite_interval_literals(sql, normalizations)

        self.assertEqual(
            patched,
            r'''SELECT '\' AS payload, "identifier\" AS label, '''
            r'''INTERVAL '14' DAY, "INTERVAL '21 DAYS'"''',
        )
        self.assertEqual(len(normalizations), 1)
        self.assertEqual(normalizations[0]["source"], "INTERVAL '14 DAYS'")

    def test_postgres_escape_string_keeps_backslash_escaped_quote_protected(self) -> None:
        sql = r'''SELECT E'protected \' tail' AS payload, INTERVAL '14 DAYS' '''
        normalizations: list[dict] = []

        patched = normalize.patch_calcite_interval_literals(sql, normalizations)

        self.assertEqual(
            patched,
            r'''SELECT E'protected \' tail' AS payload, INTERVAL '14' DAY ''',
        )
        self.assertEqual(len(normalizations), 1)

    def test_dollar_quote_opening_requires_postgres_identifier_boundary(self) -> None:
        for prefix in ("col", "é"):
            with self.subTest(prefix=prefix):
                sql = f"SELECT {prefix}$tag$, INTERVAL '14 DAYS'"
                normalizations: list[dict] = []

                patched = normalize.patch_calcite_interval_literals(
                    sql, normalizations
                )

                self.assertEqual(
                    patched,
                    f"SELECT {prefix}$tag$, INTERVAL '14' DAY",
                )
                self.assertEqual(len(normalizations), 1)

    def test_timestamptz_rendering_is_restricted_to_structured_type_nodes(self) -> None:
        cases = {
            "SELECT timestamptz FROM t": "SELECT timestamptz FROM t;\n",
            "SELECT timestamptzfoo FROM t": "SELECT timestamptzfoo FROM t;\n",
            "SELECT 1 AS timestamptz": "SELECT 1 AS timestamptz;\n",
            "CREATE TABLE t (timestamptz INTEGER)": (
                "CREATE TABLE t (timestamptz INT);\n"
            ),
        }
        for sql, expected in cases.items():
            with self.subTest(sql=sql):
                normalized, report = normalize.normalize_sql(
                    sql=sql,
                    read="postgres",
                    write="postgres",
                    identify=False,
                    pretty=False,
                    apply_patches=True,
                )
                self.assertFalse(report["errors"])
                self.assertEqual(normalized, expected)
                self.assertFalse(
                    any(
                        entry["kind"] == "calcite_timestamptz_type"
                        for entry in report["normalizations"]
                    )
                )

    def test_timestamptz_type_uses_calcite_spelling_without_eating_whitespace(self) -> None:
        normalized, report = normalize.normalize_sql(
            sql=(
                "SELECT CAST(x AS TIMESTAMP(3) WITH TIME ZONE) AS z "
                "FROM source_table"
            ),
            read="postgres",
            write="postgres",
            identify=False,
            pretty=False,
            apply_patches=True,
        )

        self.assertFalse(report["errors"])
        self.assertEqual(
            normalized,
            "SELECT CAST(x AS TIMESTAMP(3) WITH TIME ZONE) AS z FROM source_table;\n",
        )
        type_patches = [
            entry
            for entry in report["normalizations"]
            if entry["kind"] == "calcite_timestamptz_type"
        ]
        self.assertEqual(len(type_patches), 1)
        self.assertEqual(type_patches[0]["source"], "TIMESTAMPTZ(3)")
        self.assertEqual(
            type_patches[0]["target"], "TIMESTAMP(3) WITH TIME ZONE"
        )

    def test_timestamp_with_local_time_zone_is_rejected(self) -> None:
        normalized, report = normalize.normalize_sql(
            sql="SELECT CAST(x AS TIMESTAMP WITH LOCAL TIME ZONE) FROM t",
            read="postgres",
            write="postgres",
            identify=False,
            pretty=False,
            apply_patches=True,
        )

        self.assertEqual(normalized, "")
        self.assertEqual(
            report["errors"][0]["code"],
            "timestamp_with_local_time_zone_unsupported",
        )

    def test_source_local_time_zone_is_rejected_before_every_output_dialect(
        self,
    ) -> None:
        sources = (
            (
                "oracle",
                "SELECT 1 FROM dual; "
                "SELECT CAST(x AS TIMESTAMP WITH LOCAL TIME ZONE) FROM t",
            ),
            (
                "snowflake",
                "SELECT 1; SELECT CAST(x AS TIMESTAMP_LTZ) FROM t",
            ),
        )
        for read, sql in sources:
            for write in ("mysql", "tsql", "oracle", "duckdb", "postgres"):
                with self.subTest(read=read, write=write):
                    normalized, report = normalize.normalize_sql(
                        sql=sql,
                        read=read,
                        write=write,
                        identify=False,
                        pretty=False,
                        apply_patches=True,
                    )

                    self.assertEqual(normalized, "")
                    self.assertEqual(len(report["errors"]), 1)
                    self.assertEqual(
                        report["errors"][0],
                        {
                            "stage": "calcite_postgres_type_validation",
                            "type": "UnsupportedTypeSemantics",
                            "code": "timestamp_with_local_time_zone_unsupported",
                            "message": (
                                "TIMESTAMP WITH LOCAL TIME ZONE has distinct "
                                "session/database semantics and is not a spelling "
                                "variant of PostgreSQL timestamptz"
                            ),
                            "statement": 2,
                        },
                    )

    def test_source_timestamptz_remains_supported(self) -> None:
        for write, expected in (
            (
                "postgres",
                "SELECT CAST(x AS TIMESTAMP WITH TIME ZONE) FROM t;\n",
            ),
            ("duckdb", "SELECT CAST(x AS TIMESTAMPTZ) FROM t;\n"),
        ):
            with self.subTest(write=write):
                normalized, report = normalize.normalize_sql(
                    sql="SELECT CAST(x AS TIMESTAMPTZ) FROM t",
                    read="postgres",
                    write=write,
                    identify=False,
                    pretty=False,
                    apply_patches=True,
                )

                self.assertFalse(report["errors"])
                self.assertEqual(normalized, expected)
                type_patches = [
                    entry
                    for entry in report["normalizations"]
                    if entry["kind"] == "calcite_timestamptz_type"
                ]
                self.assertEqual(len(type_patches), int(write == "postgres"))

    def test_postgres_arithmetic_is_never_guessed_to_be_an_interval(self) -> None:
        for sql in (
            "SELECT 1 + 2 days",
            "SELECT d_date - 2 AS days FROM dates",
            "SELECT CAST('2020-01-01' AS DATE) + 1",
        ):
            with self.subTest(sql=sql):
                normalized, report = normalize.normalize_sql(
                    sql=sql,
                    read="postgres",
                    write="postgres",
                    identify=False,
                    pretty=False,
                    apply_patches=True,
                )
                self.assertFalse(report["errors"])
                self.assertNotIn("INTERVAL", normalized.upper())
                self.assertFalse(
                    any("interval" in entry["kind"] for entry in report["normalizations"])
                )


class PostgresOrderAliasExpressionTests(unittest.TestCase):
    def normalize(self, sql: str) -> tuple[str, dict]:
        return normalize.normalize_sql(
            sql=sql,
            read="tsql",
            write="postgres",
            identify=False,
            pretty=False,
            apply_patches=True,
        )

    def test_expands_tpcds_grouping_alias_inside_order_expression(self) -> None:
        normalized, report = self.normalize(
            "SELECT TOP 100 i_category, i_class, "
            "GROUPING(i_category) + GROUPING(i_class) AS lochierarchy "
            "FROM item GROUP BY ROLLUP(i_category, i_class) "
            "ORDER BY lochierarchy DESC, "
            "CASE WHEN lochierarchy = 0 THEN i_category END"
        )

        self.assertFalse(report["errors"])
        self.assertIn("ORDER BY lochierarchy DESC", normalized)
        self.assertIn(
            "CASE WHEN (GROUPING(i_category) + GROUPING(i_class)) = 0",
            normalized,
        )
        self.assertIn("LIMIT 100", normalized)
        rewrites = [
            entry
            for entry in report["normalizations"]
            if entry["kind"] == "postgres_order_alias_expression"
        ]
        self.assertEqual(len(rewrites), 1)
        self.assertEqual(rewrites[0]["aliases"], ["lochierarchy"])

    def test_leaves_standalone_order_alias_unchanged(self) -> None:
        normalized, report = self.normalize(
            "SELECT TOP 5 GROUPING(category) AS hierarchy "
            "FROM item GROUP BY ROLLUP(category) ORDER BY hierarchy DESC"
        )

        self.assertFalse(report["errors"])
        self.assertIn("ORDER BY hierarchy DESC", normalized)
        self.assertFalse(
            any(
                entry["kind"] == "postgres_order_alias_expression"
                for entry in report["normalizations"]
            )
        )

    def test_fails_closed_before_duplicating_unknown_function(self) -> None:
        normalized, report = self.normalize(
            "SELECT RAND() AS choice FROM item "
            "ORDER BY CASE WHEN choice > 0 THEN 1 ELSE 0 END"
        )

        self.assertEqual(normalized, "")
        self.assertEqual(len(report["errors"]), 1)
        self.assertEqual(
            report["errors"][0]["code"],
            "order_alias_expression_not_repeatable",
        )


class PostgresIdentifierFoldingTests(unittest.TestCase):
    def normalize(self, sql: str, *, identify: bool = True) -> tuple[str, dict]:
        return normalize.normalize_sql(
            sql=sql,
            read="postgres",
            write="postgres",
            identify=identify,
            pretty=False,
            apply_patches=False,
        )

    def test_identify_folds_only_unquoted_postgres_identifiers(self) -> None:
        source = (
            'SELECT DEPT.NAME AS MixedAlias, "DEPT"."NAME" AS "Exact Alias" '
            'FROM DEPT UpperAlias JOIN "DEPT" AS "ExactTable" ON TRUE'
        )

        normalized, report = self.normalize(source)

        self.assertFalse(report["errors"])
        self.assertIn('"dept"."name" AS "mixedalias"', normalized)
        self.assertIn('"DEPT"."NAME" AS "Exact Alias"', normalized)
        self.assertIn('FROM "dept" "upperalias"', normalized)
        self.assertIn('JOIN "DEPT" AS "ExactTable"', normalized)
        folding = [
            entry
            for entry in report["normalizations"]
            if entry["kind"] == "postgres_unquoted_identifier_folding"
        ]
        self.assertEqual(len(folding), 1)
        pairs = {
            (identifier["source"], identifier["target"])
            for identifier in folding[0]["identifiers"]
        }
        self.assertTrue(
            {
                ("DEPT", "dept"),
                ("NAME", "name"),
                ("MixedAlias", "mixedalias"),
                ("UpperAlias", "upperalias"),
            }.issubset(pairs)
        )
        self.assertNotIn(("ExactTable", "exacttable"), pairs)

        unidentified, unidentified_report = self.normalize(
            source, identify=False
        )
        self.assertFalse(unidentified_report["errors"])
        self.assertIn("DEPT.NAME AS MixedAlias", unidentified)
        self.assertIn('"DEPT"."NAME" AS "Exact Alias"', unidentified)

    def test_identifier_generation_audit_fails_closed(self) -> None:
        real_collect = normalize._collect_identifier_sites
        call_count = 0

        def corrupt_generated_sites(statement):
            nonlocal call_count
            call_count += 1
            sites = real_collect(statement)
            return sites[:-1] if call_count == 3 else sites

        with mock.patch.object(
            normalize,
            "_collect_identifier_sites",
            side_effect=corrupt_generated_sites,
        ):
            normalized, report = self.normalize("SELECT NAME FROM DEPT")

        self.assertEqual(normalized, "")
        self.assertEqual(len(report["errors"]), 1)
        self.assertEqual(report["errors"][0]["stage"], "postgres_identifier_folding")
        self.assertEqual(report["errors"][0]["code"], "identifier_count_changed")


class PostgresImplicitAliasStyleTests(unittest.TestCase):
    def normalize(self, sql: str, *, identify: bool) -> tuple[str, dict]:
        return normalize.normalize_sql(
            sql=sql,
            read="postgres",
            write="postgres",
            identify=identify,
            pretty=False,
            apply_patches=False,
        )

    def test_mixed_output_table_and_subquery_alias_styles(self) -> None:
        source = (
            "SELECT COUNT(*) implicit_count, x AS explicit_value "
            "FROM customer c "
            "JOIN (SELECT 1 nested_value) AS explicit_subquery ON TRUE "
            "JOIN (SELECT 2 AS nested_explicit) implicit_subquery ON TRUE"
        )

        for identify, quote in [(False, ""), (True, '"')]:
            with self.subTest(identify=identify):
                normalized, report = self.normalize(source, identify=identify)
                self.assertFalse(report["errors"])
                self.assertIn(f"COUNT(*) {quote}implicit_count{quote}", normalized)
                self.assertNotIn(f"COUNT(*) AS {quote}implicit_count{quote}", normalized)
                self.assertIn(f"AS {quote}explicit_value{quote}", normalized)
                relation = '"customer" "c"' if identify else "customer c"
                explicit_relation = (
                    '"customer" AS "c"' if identify else "customer AS c"
                )
                self.assertIn(relation, normalized)
                self.assertNotIn(explicit_relation, normalized)
                self.assertIn(f"AS {quote}explicit_subquery{quote}", normalized)
                self.assertIn(f") {quote}implicit_subquery{quote}", normalized)
                self.assertIn(f"1 {quote}nested_value{quote}", normalized)
                self.assertIn(f"2 AS {quote}nested_explicit{quote}", normalized)
                aliases = [
                    entry
                    for entry in report["normalizations"]
                    if entry["kind"] == "postgres_implicit_alias_style"
                ]
                self.assertEqual(len(aliases), 4)
                self.assertEqual(
                    sorted(entry["siteKind"] for entry in aliases),
                    [
                        "select_expression_alias",
                        "select_expression_alias",
                        "subquery_relation_alias",
                        "table_relation_alias",
                    ],
                )

    def test_nested_multistatement_and_quoted_implicit_aliases(self) -> None:
        source = (
            'SELECT (SELECT t.x inner_alias FROM tbl t) "Outer Alias"; '
            "SELECT q.inner_alias final_alias FROM "
            "(SELECT x inner_alias FROM tbl AS explicit_table) q"
        )

        for identify in (False, True):
            with self.subTest(identify=identify):
                normalized, report = self.normalize(source, identify=identify)
                self.assertFalse(report["errors"])
                self.assertEqual(report["statementCount"], 2)
                self.assertNotIn('AS "Outer Alias"', normalized)
                self.assertIn(') "Outer Alias"', normalized)
                self.assertIn('AS "explicit_table"' if identify else "AS explicit_table", normalized)
                self.assertNotIn('AS "q"' if identify else "AS q", normalized)
                statement_numbers = {
                    entry["statement"]
                    for entry in report["normalizations"]
                    if entry["kind"] == "postgres_implicit_alias_style"
                }
                self.assertEqual(statement_numbers, {1, 2})

    def test_only_alias_markers_are_removed(self) -> None:
        source = (
            "WITH cte AS (SELECT CAST(x AS INT) cast_value FROM source_table st) "
            "SELECT CAST(cast_value AS INT) final_value, "
            "'AS literal' AS explicit_literal "
            "FROM cte c WINDOW w AS (PARTITION BY cast_value) "
            "/* AS comment */"
        )
        normalized, report = self.normalize(source, identify=False)

        self.assertFalse(report["errors"])
        self.assertIn("cte AS (", normalized)
        self.assertEqual(normalized.count("CAST("), 2)
        self.assertEqual(normalized.count(" AS INT)"), 2)
        self.assertIn("WINDOW w AS (", normalized)
        self.assertIn("'AS literal' AS explicit_literal", normalized)
        self.assertIn("/* AS comment */", normalized)
        self.assertIn("CAST(x AS INT) cast_value", normalized)
        self.assertIn("CAST(cast_value AS INT) final_value", normalized)
        self.assertIn("FROM cte c", normalized)

        ddl, ddl_report = self.normalize(
            "CREATE VIEW v AS SELECT 1 implicit_inside_ddl", identify=False
        )
        self.assertFalse(ddl_report["errors"])
        self.assertIn("v AS SELECT", ddl)
        self.assertIn("1 AS implicit_inside_ddl", ddl)

    def test_alias_site_mapping_fails_closed(self) -> None:
        for label, generated in [
            ("renamed", ["SELECT 1 AS b, 2 AS a"]),
            ("missing", ["SELECT 1 AS a"]),
            ("reordered kind", ["SELECT 1 AS a FROM tbl AS b"]),
        ]:
            with self.subTest(label=label):
                with self.assertRaises(normalize.AliasStyleNormalizationError) as caught:
                    normalize.preserve_postgres_implicit_alias_style(
                        "SELECT 1 a, 2 b",
                        generated,
                        False,
                        [],
                    )
                self.assertIn(
                    caught.exception.code,
                    {"alias_site_count_mismatch", "alias_site_mismatch"},
                )

        with mock.patch.object(
            normalize,
            "_remove_generated_alias_as_tokens",
            return_value=("SELECT 2 a", []),
        ):
            with self.assertRaises(normalize.AliasStyleNormalizationError) as caught:
                normalize.preserve_postgres_implicit_alias_style(
                    "SELECT 1 a", ["SELECT 1 AS a"], False, []
                )
        self.assertEqual(caught.exception.code, "edited_ast_changed")

    def test_normalize_sql_reports_structured_alias_mapping_error(self) -> None:
        with mock.patch.object(
            normalize.sqlglot,
            "transpile",
            return_value=["SELECT 1 AS forged"],
        ):
            normalized, report = self.normalize("SELECT 1 original", identify=False)

        self.assertEqual(normalized, "")
        self.assertEqual(len(report["errors"]), 1)
        error = report["errors"][0]
        self.assertEqual(error["stage"], "postgres_implicit_alias_style")
        self.assertEqual(error["code"], "alias_site_mismatch")
        self.assertEqual(error["statement"], 1)


if __name__ == "__main__":
    unittest.main()
