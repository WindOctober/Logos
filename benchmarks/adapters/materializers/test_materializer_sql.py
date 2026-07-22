# ruff: noqa: E402

import importlib.util
import json
import re
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace


MATERIALIZER_DIR = Path(__file__).resolve().parent
if str(MATERIALIZER_DIR) not in sys.path:
    sys.path.insert(0, str(MATERIALIZER_DIR))

import materialize_cosette as cosette
import materialize_nonwetune_sqlsolver as nonwetune_sqlsolver
import materialize_qed as qed
import materialize_wetune_sqlsolver as wetune_sqlsolver
import materializer_sql
import sanitize_wetune_schema
import sqlsolver_schema_constraints as sqlsolver_constraints


REPO_ROOT = MATERIALIZER_DIR.parents[2]
COVERAGE_SCRIPT = REPO_ROOT / "scripts/generate-integrity-constraint-coverage.py"
coverage_spec = importlib.util.spec_from_file_location(
    "logos_integrity_coverage", COVERAGE_SCRIPT
)
if coverage_spec is None or coverage_spec.loader is None:
    raise RuntimeError(f"cannot import {COVERAGE_SCRIPT}")
integrity_coverage = importlib.util.module_from_spec(coverage_spec)
coverage_spec.loader.exec_module(integrity_coverage)


class SharedSqlLexingTests(unittest.TestCase):
    def test_comment_markers_inside_all_quote_forms_are_preserved(self) -> None:
        sql = (
            "SELECT '-- single', \"/* double */\", `-- backtick`, "
            "'it''s /* still quoted */'; -- line comment\n"
            "SELECT 1 /* block comment */ + 2"
        )

        stripped = materializer_sql.strip_sql_comments(sql)

        self.assertIn("'-- single'", stripped)
        self.assertIn('"/* double */"', stripped)
        self.assertIn("`-- backtick`", stripped)
        self.assertIn("'it''s /* still quoted */'", stripped)
        self.assertNotIn("line comment", stripped)
        self.assertNotIn("block comment", stripped)
        self.assertIn("\nSELECT 1", stripped)

    def test_dollar_quotes_survive_comment_stripping_and_nested_comments_do_not(
        self,
    ) -> None:
        dollar_body = """$procedure$
          -- part of the procedure body
          SELECT '/* still dollar quoted */', $$CREATE TABLE dollar_fake (x int);$$;
        $procedure$"""
        sql = (
            dollar_body
            + "\n/* outer comment\n"
            + "   /* nested comment with CREATE TABLE nested_fake (x int); */\n"
            + "   still outer\n"
            + "*/\nSELECT 1; -- trailing comment\n"
        )

        stripped = materializer_sql.strip_sql_comments(sql)

        self.assertEqual(len(stripped), len(sql))
        self.assertEqual(stripped.count("\n"), sql.count("\n"))
        self.assertIn(dollar_body, stripped)
        self.assertNotIn("outer comment", stripped)
        self.assertNotIn("nested_fake", stripped)
        self.assertNotIn("trailing comment", stripped)

    def test_top_level_comma_split_handles_escapes_and_nested_parentheses(self) -> None:
        text = "'a'',b', \"c\"\",d\", `e``,f`, " "outer(inner(1, 2), 'x,y'), tail"

        self.assertEqual(
            [part.strip() for part in materializer_sql.split_top_level_commas(text)],
            [
                "'a'',b'",
                '"c"",d"',
                "`e``,f`",
                "outer(inner(1, 2), 'x,y')",
                "tail",
            ],
        )
        self.assertEqual(
            [
                part.strip()
                for part in materializer_sql.split_top_level_commas(
                    r"'backslash\', final"
                )
            ],
            [r"'backslash\'", "final"],
            "a backslash in a standard-conforming PostgreSQL string must not swallow its closing quote",
        )

    def test_unquoted_search_and_matching_parenthesis_share_quote_policy(self) -> None:
        sql = (
            'CREATE TABLE "table(name)" '
            "(a int, b text DEFAULT 'not )', c int CHECK (c IN (1, 2))) trailing"
        )
        open_paren = materializer_sql.find_next_unquoted(sql, "(", len("CREATE TABLE"))
        close_paren = materializer_sql.find_matching_paren(sql, open_paren)

        self.assertEqual(sql[open_paren - 1 : open_paren + 1], " (")
        self.assertEqual(sql[close_paren + 1 :], " trailing")

    def test_statement_split_ignores_quoted_and_nested_semicolons(self) -> None:
        sql = "INSERT INTO t VALUES ('a;b', fn(1;2)); SELECT `x;y`;"

        self.assertEqual(
            materializer_sql.split_sql_statements(sql),
            ["INSERT INTO t VALUES ('a;b', fn(1;2))", "SELECT `x;y`"],
        )

    def test_statement_split_strips_only_ascii_sql_whitespace(self) -> None:
        sql = "\u00a0SELECT 1\u00a0; \t\nSELECT 2\r\f;"

        self.assertEqual(
            materializer_sql.split_sql_statements(sql),
            ["\u00a0SELECT 1\u00a0", "SELECT 2"],
        )

    def test_mysql_policy_shields_backslash_escaped_quote_delimiters(self) -> None:
        sql = (
            r"'one \' CREATE TABLE single_fake (x int)' "
            r'"two \" CREATE TABLE double_fake (x int)" '
            r"`three \` CREATE TABLE backtick_fake (x int)`"
        )

        self.assertEqual(
            [
                region.kind
                for region in materializer_sql.protected_sql_regions(
                    sql,
                    quote_policy=materializer_sql.MYSQL_MATERIALIZER_QUOTE_POLICY,
                )
            ],
            ["single_quote", "double_quote", "backtick_quote"],
        )

    def test_boundary_scanners_ignore_dollar_quotes_and_comments(self) -> None:
        columns = (
            "a text DEFAULT $value$x,y); CREATE TABLE fake (z int);$value$, "
            "b int /* comma, close ), semicolon; /* nested , */ */, c int"
        )

        self.assertEqual(
            [part.strip() for part in materializer_sql.split_top_level_commas(columns)],
            [
                "a text DEFAULT $value$x,y); CREATE TABLE fake (z int);$value$",
                "b int /* comma, close ), semicolon; /* nested , */ */",
                "c int",
            ],
        )
        self.assertEqual(
            materializer_sql.split_sql_statements(
                "DO $$BEGIN PERFORM ';'; END$$; /* ; */ SELECT 1;"
            ),
            ["DO $$BEGIN PERFORM ';'; END$$", "/* ; */ SELECT 1"],
        )

    def test_mask_tracks_e_strings_unicode_dollar_tags_and_identifier_adjacency(
        self,
    ) -> None:
        sql = "SELECT E'escaped \\' quote -- still text', $©_tag$/* text */$©_tag$, ©$tag$not_a_quote$tag$"
        masked = materializer_sql.mask_sql_regions(sql)

        self.assertEqual(len(masked), len(sql))
        self.assertEqual(masked.count("\n"), sql.count("\n"))
        self.assertNotIn("still text", masked)
        self.assertNotIn("/* text */", masked)
        self.assertIn("©$tag$not_a_quote$tag$", masked)
        self.assertEqual(
            [region.kind for region in materializer_sql.protected_sql_regions(sql)],
            ["single_quote", "dollar_quote"],
        )

    def test_shared_layout_normalizer_preserves_every_protected_byte(self) -> None:
        protected = (
            "'single  \n value', \"double  \n value\", `back  \t tick`, "
            "E'escape \\' quote  \n value', $é$ dollar  \n value $é$"
        )
        sql = f" \n SELECT   {protected}  ; /* nested /* comment */ gone */ "

        self.assertEqual(
            materializer_sql.normalize_sql_layout(
                sql,
                strip_trailing_semicolon=True,
            ),
            f"SELECT {protected}",
        )
        self.assertEqual(
            materializer_sql.normalize_sql_layout("SELECT\u00a0high_bit  \n FROM t"),
            "SELECT\u00a0high_bit FROM t",
            "NBSP is a high-bit SQL token byte, not layout whitespace",
        )
        self.assertEqual(
            materializer_sql.normalize_sql_layout(
                "SELECT\u00a0;",
                strip_trailing_semicolon=True,
            ),
            "SELECT\u00a0",
        )
        for malformed in (
            "SELECT 'unterminated;",
            'SELECT "unterminated;',
            "SELECT `unterminated;",
            "SELECT $tag$unterminated;",
        ):
            self.assertEqual(
                materializer_sql.normalize_sql_layout(
                    malformed,
                    strip_trailing_semicolon=True,
                ),
                malformed,
                "a protected final semicolon must not become structural punctuation",
            )

    def test_guarded_substitution_has_full_and_explicit_start_only_modes(self) -> None:
        pattern = re.compile(r"x\s*=\s*('[^']*'|\d+)")
        sql = "SELECT 'x = 1', $$x = '2'$$, x = '3', x = 4"

        self.assertEqual(
            materializer_sql.substitute_unprotected(pattern, "hit", sql),
            "SELECT 'x = 1', $$x = '2'$$, x = '3', hit",
        )
        self.assertEqual(
            materializer_sql.substitute_unprotected(
                pattern,
                lambda match: f"hit({match.group(1)})",
                sql,
                start_only=True,
            ),
            "SELECT 'x = 1', $$x = '2'$$, hit('3'), hit(4)",
        )

    def test_scripts_use_one_shared_lexical_authority(self) -> None:
        self.assertIs(cosette.find_matching_paren, materializer_sql.find_matching_paren)
        self.assertIs(
            cosette.split_top_level_commas,
            materializer_sql.split_top_level_commas,
        )
        self.assertIs(cosette.parse_schema, materializer_sql.parse_schema)
        self.assertIs(cosette.mask_sql_regions, materializer_sql.mask_sql_regions)
        self.assertIs(
            cosette.normalize_sql_layout,
            materializer_sql.normalize_sql_layout,
        )
        self.assertIs(
            nonwetune_sqlsolver.normalize_sql_layout,
            materializer_sql.normalize_sql_layout,
        )
        self.assertIs(qed.strip_sql_comments, materializer_sql.strip_sql_comments)
        self.assertIs(
            qed.substitute_unprotected,
            materializer_sql.substitute_unprotected,
        )
        self.assertIs(qed.parse_schema, materializer_sql.parse_schema)
        mysql_bindings = (
            (
                wetune_sqlsolver.find_matching_paren,
                materializer_sql.find_matching_paren,
            ),
            (wetune_sqlsolver.find_next_unquoted, materializer_sql.find_next_unquoted),
            (wetune_sqlsolver.parse_schema, materializer_sql.parse_schema),
            (
                wetune_sqlsolver.split_top_level_commas,
                materializer_sql.split_top_level_commas,
            ),
            (
                sanitize_wetune_schema.find_matching_paren,
                materializer_sql.find_matching_paren,
            ),
            (
                sanitize_wetune_schema.find_next_unquoted,
                materializer_sql.find_next_unquoted,
            ),
            (
                sanitize_wetune_schema.mask_sql_regions,
                materializer_sql.mask_sql_regions,
            ),
            (
                sanitize_wetune_schema.normalize_sql_layout,
                materializer_sql.normalize_sql_layout,
            ),
            (sanitize_wetune_schema.parse_schema, materializer_sql.parse_schema),
            (
                sanitize_wetune_schema.split_sql_statements,
                materializer_sql.split_sql_statements,
            ),
            (
                sanitize_wetune_schema.split_top_level_commas,
                materializer_sql.split_top_level_commas,
            ),
            (
                sanitize_wetune_schema.strip_sql_comments,
                materializer_sql.strip_sql_comments,
            ),
        )
        for bound, authority in mysql_bindings:
            self.assertIs(bound.func, authority)
            self.assertIs(
                bound.keywords["quote_policy"],
                materializer_sql.MYSQL_MATERIALIZER_QUOTE_POLICY,
            )
        postgres_bindings = (
            (
                wetune_sqlsolver.normalize_sql_layout,
                materializer_sql.normalize_sql_layout,
            ),
            (
                wetune_sqlsolver.transform_double_quoted_identifiers,
                materializer_sql.transform_double_quoted_identifiers,
            ),
        )
        for bound, authority in postgres_bindings:
            self.assertIs(bound.func, authority)
            self.assertIs(
                bound.keywords["quote_policy"],
                materializer_sql.STANDARD_MATERIALIZER_QUOTE_POLICY,
            )

    def test_cosette_query_normalization_preserves_comment_markers_in_literals(
        self,
    ) -> None:
        self.assertEqual(
            cosette.normalize_query_payload(
                "SELECT '--', '/* still literal */'; -- trailing"
            ),
            "SELECT '--', '/* still literal */'",
        )

    def test_all_three_layout_consumers_preserve_protected_whitespace(self) -> None:
        protected = (
            "'single  \n value', \"double  \n value\", `back  \t tick`, "
            "E'escape \\' quote  \n value', $é$ dollar  \n value $é$"
        )
        sql = f"SELECT  \n {protected}; -- trailing"
        expected = f"SELECT {protected}"

        self.assertEqual(cosette.normalize_query_payload(sql), expected)
        self.assertEqual(nonwetune_sqlsolver.ensure_one_line(sql), expected + "\n")
        self.assertEqual(wetune_sqlsolver.ensure_one_line(sql), expected + "\n")

    def test_wetune_identifier_rewrite_only_transforms_double_quote_regions(
        self,
    ) -> None:
        sql = (
            'SELECT "real name", \'literal "fake"\', '
            '$body$dollar "fake"$body$, E\'escape "fake"\', '
            '"dou""bled" FROM "select"'
        )
        rendered = wetune_sqlsolver.render_query(
            sql,
            {
                "real name": "real_name",
                'dou"bled': "doubled",
            },
        )

        self.assertEqual(
            rendered,
            "SELECT real_name, 'literal \"fake\"', "
            '$body$dollar "fake"$body$, E\'escape "fake"\', '
            "doubled FROM select_x",
        )

    def test_wetune_postgres_output_does_not_backslash_escape_plain_quotes(
        self,
    ) -> None:
        sql = r"""SELECT 'path\' AS "quoted name";"""

        self.assertEqual(
            wetune_sqlsolver.render_query(sql, {"quoted name": "quoted_name"}),
            r"SELECT 'path\' AS quoted_name;",
        )
        self.assertEqual(
            wetune_sqlsolver.ensure_one_line(sql),
            "SELECT 'path\\' AS \"quoted name\"\n",
        )

    def test_qed_interval_patch_ignores_protected_interval_text(self) -> None:
        sql = (
            "SELECT INTERVAL '123' DAY, "
            "'INTERVAL ''456'' DAY', "
            "$$INTERVAL '789' DAY$$, "
            "E'INTERVAL \\'999\\' DAY'"
        )

        self.assertEqual(
            qed.patch_qed_interval_precision(sql),
            "SELECT INTERVAL '123' DAY(3), "
            "'INTERVAL ''456'' DAY', "
            "$$INTERVAL '789' DAY$$, "
            "E'INTERVAL \\'999\\' DAY'",
        )

    def test_qed_interval_patch_uses_postgresql_token_boundaries(self) -> None:
        unchanged = (
            "myinterval '123' DAY",
            "t.INTERVAL '123' DAY",
            "INTERVAL '123' DAY_ALIAS",
            "INTERVAL '123' DAY.foo",
            "$INTERVAL '123' DAY",
            "©INTERVAL '123' DAY",
            "INTERVAL '123' DAY$alias",
            "INTERVAL '123' DAY©alias",
            "İNTERVAL '123' DAY",
            "ıNTERVAL '123' DAY",
            "INTERVAL\u00a0'123' DAY",
            "INTERVAL '123'\u00a0DAY",
            "INTERVAL '123' DAY\u00a0alias",
            "INTERVAL '123' DAY(3)",
        )
        for sql in unchanged:
            with self.subTest(sql=sql):
                self.assertEqual(qed.patch_qed_interval_precision(sql), sql)

        self.assertEqual(
            qed.patch_qed_interval_precision("INTERVAL\t'1234'\nDAY value"),
            "INTERVAL '1234' DAY(4) value",
        )

    def test_cosette_blocker_scan_ignores_e_and_dollar_bodies(self) -> None:
        sql = (
            "SELECT E'WHERE TRUE; x IN (1, 2); foo(id); ORDER BY fake', "
            "$$WHERE FALSE; y BETWEEN 1 AND 2; bar(id); ORDER BY fake$$ "
            "FROM t WHERE TRUE"
        )
        result = cosette.materialize_query(sql)

        self.assertEqual(result.sql, sql)
        self.assertTrue(any("Boolean literals" in item for item in result.blockers))
        self.assertFalse(any("ORDER BY" in item for item in result.blockers))
        self.assertFalse(any("IN predicates" in item for item in result.blockers))
        self.assertFalse(any("Function calls" in item for item in result.blockers))


class CosetteSoundnessClosureTests(unittest.TestCase):
    def assert_preserved_and_blocked(
        self,
        sql: str,
        preserved: str,
        blocker: str,
    ) -> None:
        result = cosette.materialize_query(sql)
        self.assertEqual(result.sql, sql)
        self.assertIn(preserved, result.sql)
        self.assertTrue(
            any(blocker in message for message in result.blockers),
            result.blockers,
        )

    def test_cast_numeric_and_integer_arithmetic_rewrites_fail_closed(self) -> None:
        cases = (
            (
                "SELECT CAST(2147483648 AS INTEGER)",
                "CAST(2147483648 AS INTEGER)",
                "CAST expressions",
            ),
            (
                "SELECT CAST(id AS INTEGER) FROM t",
                "CAST(id AS INTEGER)",
                "CAST expressions",
            ),
            (
                "SELECT 2147483647 + 1",
                "2147483647 + 1",
                "Integer arithmetic",
            ),
            (
                "SELECT 9223372036854775807 + 1",
                "9223372036854775807 + 1",
                "Integer arithmetic",
            ),
            (
                "SELECT -2147483648 / -1",
                "-2147483648 / -1",
                "Integer arithmetic",
            ),
            (
                "SELECT 1.0 / 2.0",
                "1.0 / 2.0",
                "Decimal literals",
            ),
        )
        for sql, preserved, blocker in cases:
            with self.subTest(sql=sql):
                self.assert_preserved_and_blocked(sql, preserved, blocker)

    def test_slicing_and_order_error_expressions_are_preserved_and_blocked(
        self,
    ) -> None:
        cases = (
            (
                "SELECT id FROM t LIMIT 0 OFFSET -1",
                "LIMIT 0 OFFSET -1",
                "LIMIT/OFFSET/FETCH",
            ),
            (
                "SELECT id FROM t LIMIT 0 OFFSET (1 / 0)",
                "OFFSET (1 / 0)",
                "LIMIT/OFFSET/FETCH",
            ),
            (
                "SELECT id FROM t ORDER BY 1 / 0",
                "ORDER BY 1 / 0",
                "ORDER BY is unsupported",
            ),
            (
                "SELECT count(*) FROM t ORDER BY 1 / 0 LIMIT 1",
                "ORDER BY 1 / 0 LIMIT 1",
                "ORDER BY is unsupported",
            ),
        )
        for sql, preserved, blocker in cases:
            with self.subTest(sql=sql):
                self.assert_preserved_and_blocked(sql, preserved, blocker)

    def test_left_join_intersect_and_in_shortcuts_no_longer_rewrite(self) -> None:
        join_sql = "SELECT l.id FROM l LEFT JOIN r ON 1 / 0 = 0 GROUP BY l.id"
        join = cosette.materialize_query(join_sql)
        self.assertEqual(join.sql, join_sql)
        self.assertTrue(any("Outer join" in item for item in join.blockers))

        fake_intersect = (
            "SELECT 'select * from t where id = 1 intersect "
            "select * from t where id = 2' AS payload FROM t"
        )
        intersect = cosette.materialize_query(fake_intersect)
        self.assertEqual(intersect.sql, fake_intersect)
        self.assertFalse(any("INTERSECT" in item for item in intersect.blockers))

        for predicate in (
            "id IN ('a,b', 'c''d')",
            "id NOT IN ('a,b', 'c''d')",
        ):
            with self.subTest(predicate=predicate):
                sql = f"SELECT id FROM t WHERE {predicate}"
                result = cosette.materialize_query(sql)
                self.assertEqual(result.sql, sql)
                self.assertIn("'a,b'", result.sql)
                self.assertIn("'c''d'", result.sql)
                self.assertTrue(any("IN" in item for item in result.blockers))

    def test_wildcards_are_not_misclassified_as_integer_multiplication(self) -> None:
        for sql in ("SELECT * FROM t", "SELECT t.* FROM t"):
            with self.subTest(sql=sql):
                result = cosette.materialize_query(sql)
                self.assertEqual(result.sql, sql)
                self.assertFalse(
                    any("Integer arithmetic" in item for item in result.blockers),
                    result.blockers,
                )

    def test_group_keys_are_preserved_and_blocked_without_binding_guesses(self) -> None:
        cases = (
            (
                "SELECT a, b, count(*) FROM t GROUP BY a, 2",
                "Literal GROUP BY keys",
            ),
            (
                "SELECT id FROM t GROUP BY id, 2147483647 + 1",
                "Integer arithmetic",
            ),
            (
                "SELECT id FROM t GROUP BY id, 'constant'",
                "Literal GROUP BY keys",
            ),
        )
        for sql, blocker in cases:
            with self.subTest(sql=sql):
                self.assert_preserved_and_blocked(sql, sql, blocker)

    def test_case_expressions_are_never_folded_lexically(self) -> None:
        cases = (
            "SELECT CASE WHEN TRUE THEN CASE WHEN FALSE THEN 10 ELSE 20 END ELSE 30 END",
            "SELECT CASE 01 WHEN 1 THEN 'same' ELSE 'different' END",
            "SELECT CASE WHEN TRUE THEN 1 ELSE 'not-an-integer' END",
        )
        for sql in cases:
            with self.subTest(sql=sql):
                self.assert_preserved_and_blocked(sql, sql, "CASE expressions")

    def test_join_syntax_is_preserved_instead_of_reassociated(self) -> None:
        cases = (
            (
                "SELECT * FROM a INNER JOIN b ON p WHERE q OR r",
                "INNER JOIN",
            ),
            (
                "SELECT * FROM a INNER JOIN b ON p CROSS JOIN c",
                "CROSS/NATURAL joins",
            ),
            (
                "SELECT l.id FROM l LEFT JOIN (SELECT id FROM r WHERE FALSE) x "
                "ON 1 / 0 = 0",
                "Outer joins",
            ),
            (
                "SELECT * FROM l, (SELECT id FROM r) x",
                "Derived-table FROM/JOIN subqueries",
            ),
        )
        for sql, blocker in cases:
            with self.subTest(sql=sql):
                self.assert_preserved_and_blocked(sql, sql, blocker)

    def test_function_names_are_not_reinterpreted_as_columns(self) -> None:
        sql = "SELECT count(*) FROM t"
        result = cosette.materialize_query(sql)

        self.assertEqual(result.sql, sql)
        self.assertFalse(result.blockers, result.blockers)

    def test_function_call_admission_is_a_closed_cosette_surface(self) -> None:
        supported = (
            "SELECT SUM(id) FROM t",
            "SELECT COUNT(*) FROM t",
            "SELECT COUNT(t.id) FROM t",
            "SELECT MAX(id), MIN(t.id) FROM t",
        )
        for sql in supported:
            with self.subTest(sql=sql):
                result = cosette.materialize_query(sql)
                self.assertEqual(result.sql, sql)
                self.assertFalse(result.blockers, result.blockers)

        unsupported = (
            "SELECT ABS(id) FROM t",
            "SELECT AVG(id) FROM t",
            "SELECT foo(id) FROM t",
            "SELECT SUM(ABS(id)) FROM t",
            "SELECT pg_catalog.COUNT(*) FROM t",
            "SELECT pg_catalog.EXISTS(id) FROM t",
            "SELECT COUNT(1) FROM t",
            "SELECT SUM(id, id) FROM t",
            "SELECT SUM(id",
            "SELECT COUNT(table.column",
            "SELECT SUM((id)",
            "SELECT COUNT(*) FILTER (WHERE id > 0) FROM t",
            "SELECT ©function(id) FROM t",
        )
        for sql in unsupported:
            with self.subTest(sql=sql):
                result = cosette.materialize_query(sql)
                self.assertEqual(result.sql, sql)
                self.assertTrue(
                    any(
                        "Function calls" in item
                        or "aggregate calls" in item
                        or "Aggregate FILTER" in item
                        for item in result.blockers
                    ),
                    result.blockers,
                )


class SharedSchemaScannerTests(unittest.TestCase):
    SCHEMA = """
        CREATE TABLE "orders(set)" (
          "id" integer NOT NULL,
          "amount" numeric(10, 2),
          "note" text DEFAULT 'a,b',
          PRIMARY KEY ("id")
        );
        CREATE TABLE `line,item` (
          `id` bigint,
          `payload` varchar(20) DEFAULT 'x''y,z'
        );
    """

    COMMENTED_BODY_SCHEMA = """
        CREATE TABLE "commented" (
          -- line comment before a column
          "id" -- line comment between the identifier and type
          integer NOT NULL,
          /* outer comment before a column
             /* nested comment before that column */
          */
          "payload" /* outer comment between the identifier and type
                         /* nested comment between them */
                      */ text DEFAULT $body$-- literal, /* marker */, )$body$,
          -- another line comment before a column
          "total" /* block comment between the identifier and type */ bigint
        );
    """

    def test_qed_schema_parser_keeps_quoted_commas_and_nested_typmods(self) -> None:
        tables = materializer_sql.parse_schema(
            self.SCHEMA,
            clean_identifier=qed.clean_identifier,
            parse_table=qed.parse_table,
        )

        self.assertEqual([table.name for table in tables], ["orders(set)", "line,item"])
        self.assertEqual(
            [column.name for column in tables[0].columns],
            ["id", "amount", "note"],
        )
        self.assertEqual(tables[0].columns[1].type_sql, "DECIMAL")
        self.assertEqual(
            [column.name for column in tables[1].columns],
            ["id", "payload"],
        )

    def test_wetune_schema_parser_keeps_quoted_commas_and_nested_typmods(self) -> None:
        schema = (
            self.SCHEMA.replace("`line,item`", '"line,item"')
            .replace("`id`", '"id"')
            .replace("`payload`", '"payload"')
        )
        tables = wetune_sqlsolver.parse_schema(
            schema,
            clean_identifier=wetune_sqlsolver.clean_identifier,
            parse_table=wetune_sqlsolver.parse_table,
        )

        self.assertEqual([table.name for table in tables], ["orders(set)", "line,item"])
        self.assertEqual(
            [column.name for column in tables[0].columns],
            ["id", "amount", "note"],
        )
        self.assertEqual(tables[0].primary_keys, [("id",)])
        self.assertEqual(
            [column.name for column in tables[1].columns],
            ["id", "payload"],
        )

    def test_qed_schema_parser_receives_comment_free_table_bodies(self) -> None:
        parsed_bodies = []

        def parse_table(table_name: str, body: str) -> qed.Table:
            parsed_bodies.append(body)
            return qed.parse_table(table_name, body)

        tables = materializer_sql.parse_schema(
            self.COMMENTED_BODY_SCHEMA,
            clean_identifier=qed.clean_identifier,
            parse_table=parse_table,
        )

        self.assertEqual(
            [column.name for column in tables[0].columns], ["id", "payload", "total"]
        )
        self.assertEqual(
            [column.type_sql for column in tables[0].columns],
            ["INTEGER", "VARCHAR(255)", "BIGINT"],
        )
        self.assertTrue(tables[0].columns[0].not_null)
        self.assertNotIn("line comment before", parsed_bodies[0])
        self.assertNotIn("nested comment", parsed_bodies[0])
        self.assertIn(
            "$body$-- literal, /* marker */, )$body$",
            parsed_bodies[0],
        )

    def test_wetune_schema_parser_receives_comment_free_table_bodies(self) -> None:
        parsed_bodies = []

        def parse_table(table_name: str, body: str) -> wetune_sqlsolver.Table:
            parsed_bodies.append(body)
            return wetune_sqlsolver.parse_table(table_name, body)

        tables = wetune_sqlsolver.parse_schema(
            self.COMMENTED_BODY_SCHEMA,
            clean_identifier=wetune_sqlsolver.clean_identifier,
            parse_table=parse_table,
        )

        self.assertEqual(
            [column.name for column in tables[0].columns], ["id", "payload", "total"]
        )
        self.assertEqual(
            [column.type_sql for column in tables[0].columns],
            ["INT", "VARCHAR(255)", "BIGINT"],
        )
        self.assertTrue(tables[0].columns[0].not_null)
        self.assertNotIn("line comment before", parsed_bodies[0])
        self.assertNotIn("nested comment", parsed_bodies[0])
        self.assertIn(
            "$body$-- literal, /* marker */, )$body$",
            parsed_bodies[0],
        )

    def test_schema_discovery_ignores_fake_ddl_in_all_protected_regions(self) -> None:
        schema = """
            -- CREATE TABLE line_fake (id integer);
            /* CREATE TABLE block_fake (id integer);
               /* CREATE TABLE nested_fake (id integer); */
            */
            DO $body$
              BEGIN
                -- these markers and punctuation are procedure text: /* (, ); */
                CREATE TABLE dollar_fake (id integer);
              END
            $body$;
            SELECT 'CREATE TABLE string_fake (id integer)';
            SELECT "CREATE TABLE identifier_fake (id integer)";
            SELECT `CREATE TABLE backtick_fake (id integer)`;
            CREATE /* accepted comment between keywords */ TABLE "actual" (
              "id" integer,
              "payload" text DEFAULT $value$-- not a comment, ), ; /* either */$value$
            );
            CREATE TABLE second ("id" bigint);
        """

        tables = materializer_sql.parse_schema(
            schema,
            clean_identifier=lambda identifier: identifier.strip('"'),
            parse_table=lambda name, body: (name, body),
        )

        self.assertEqual([name for name, _ in tables], ["actual", "second"])
        self.assertIn(
            "$value$-- not a comment, ), ; /* either */$value$",
            tables[0][1],
        )

    def test_schema_discovery_uses_postgresql_keyword_boundaries(self) -> None:
        schema = (
            "CREATE TABLE$joined (id integer);\n"
            "prefix.CREATE TABLE dotted_prefix (id integer);\n"
            "CREATE TABLE.dotted_suffix (id integer);\n"
            "CREATE\u00a0TABLE nbsp_joined (id integer);\n"
            "©CREATE TABLE high_prefix (id integer);\n"
            "CREATE TABLE©high_suffix (id integer);\n"
            "CREATE\tTABLE tab_separated (id integer);\n"
            "CREATE\vTABLE vtab_separated (id bigint);\n"
        )

        tables = materializer_sql.parse_schema(
            schema,
            clean_identifier=lambda identifier: identifier,
            parse_table=lambda name, body: (name, body.strip()),
        )

        self.assertEqual(
            [name for name, _ in tables],
            ["tab_separated", "vtab_separated"],
        )

    def test_wetune_mysql_policy_shields_fake_ddl_after_escaped_quote(self) -> None:
        schema = r"""
            SELECT 'text \' CREATE TABLE escaped_fake (id integer)';
            CREATE TABLE actual (id integer);
        """

        tables = wetune_sqlsolver.parse_schema(
            schema,
            clean_identifier=wetune_sqlsolver.clean_identifier,
            parse_table=wetune_sqlsolver.parse_table,
        )

        self.assertEqual([table.name for table in tables], ["actual"])

    def test_malformed_ddl_cannot_borrow_a_later_statement_extent(self) -> None:
        schema = """
            CREATE TABLE broken_header;
            CREATE TABLE first_valid (id integer);
            CREATE TABLE broken_body (id integer;
            CREATE TABLE second_valid (id bigint);
        """

        tables = materializer_sql.parse_schema(
            schema,
            clean_identifier=lambda identifier: identifier.strip(),
            parse_table=lambda name, body: (name, body.strip()),
        )

        self.assertEqual(
            tables,
            [
                ("first_valid", "id integer"),
                ("second_valid", "id bigint"),
            ],
        )

    def test_cosette_schema_discovery_preserves_its_narrow_name_grammar(self) -> None:
        schema = """
            -- CREATE TABLE line_fake (id integer);
            /* outer CREATE TABLE block_fake (id integer);
               /* CREATE TABLE nested_fake (id integer); */
            */
            SELECT 'CREATE TABLE string_fake (id integer)';
            DO $body$ CREATE TABLE dollar_fake (id integer); $body$;
            CREATE TABLE "quoted_is_unsupported" (id integer);
            CREATE TABLE empty_table (PRIMARY KEY (id));
            CREATE TABLE IF NOT EXISTS public.actual_table (
              id integer,
              payload text DEFAULT $value$-- literal /* text */$value$
            );
        """

        tables = cosette.parse_tables(schema)

        self.assertEqual([table.name for table in tables], ["actual_table"])
        self.assertEqual(
            [column.name for column in tables[0].columns],
            ["id", "payload"],
        )

    def test_sanitizer_schema_discovery_ignores_fake_ddl_and_nested_comments(
        self,
    ) -> None:
        schema = """
            -- CREATE TABLE line_fake (id integer);
            /* CREATE TABLE block_fake (id integer);
               /* CREATE TABLE nested_fake (id integer); */
            */
            SELECT 'CREATE TABLE string_fake (id integer)';
            DO $body$ CREATE TABLE dollar_fake (id integer); $body$;
            CREATE TABLE IF NOT EXISTS "actual" (
              "id" integer NOT NULL,
              "payload" text DEFAULT $value$NOT NULL\x20\x20
                UNIQUE -- literal /* text */$value$
            );
        """

        tables, audit, constraints = sanitize_wetune_schema.sanitize_schema(schema)

        self.assertEqual([table.name for table in tables], ["actual"])
        self.assertEqual(
            [column.name for column in tables[0].columns],
            ["id", "payload"],
        )
        self.assertEqual(audit["tables"], 1)
        self.assertFalse(tables[0].columns[1].not_null)
        self.assertEqual(
            tables[0].columns[1].default,
            "$value$NOT NULL  \n                UNIQUE -- literal /* text */$value$",
        )
        self.assertEqual(
            constraints["semanticSchema"]["tables"][0]["name"],
            "actual",
        )

    def test_sanitizer_mysql_policy_shields_fake_ddl_after_escaped_quote(self) -> None:
        schema = r"""
            SELECT 'text \' CREATE TABLE escaped_fake (id integer)';
            CREATE TABLE actual (id integer);
        """

        tables, audit, _constraints = sanitize_wetune_schema.sanitize_schema(schema)

        self.assertEqual([table.name for table in tables], ["actual"])
        self.assertEqual(audit["tables"], 1)


class SqlsolverSchemaConstraintTests(unittest.TestCase):
    def test_pair_constraints_are_emitted_exactly_and_primary_implies_not_null(
        self,
    ) -> None:
        schema = (
            "CREATE TABLE parent (id INT, payload VARCHAR(20));\n"
            "CREATE TABLE child (id INT, parent_id INT);\n"
        )
        constraints = [
            {"primary": [{"value": "PARENT__ID"}]},
            {"not_null": {"value": "CHILD__ID"}},
            {
                "foreign": [
                    {"value": "CHILD__PARENT_ID"},
                    {"value": "PARENT__ID"},
                ]
            },
        ]

        materialized, report = sqlsolver_constraints.materialize_pair_constraints(
            schema,
            constraints,
        )

        self.assertIn("id INT NOT NULL", materialized)
        self.assertIn("PRIMARY KEY (id)", materialized)
        self.assertIn(
            "FOREIGN KEY (parent_id) REFERENCES parent (id)",
            materialized,
        )
        self.assertTrue(report["ddlComplete"])
        self.assertEqual(report["sourceConstraintCount"], 3)
        self.assertEqual(report["residualConstraints"], [])

    def test_pair_reference_is_resolved_against_catalog_not_split_blindly(
        self,
    ) -> None:
        schema = "CREATE TABLE a__b (c__d INT);"

        materialized, _ = sqlsolver_constraints.materialize_pair_constraints(
            schema,
            [{"not_null": {"value": "a__b__c__d"}}],
        )

        self.assertIn("c__d INT NOT NULL", materialized)

    def test_nullable_unique_is_rejected_but_nonnull_unique_is_accepted(self) -> None:
        schema = "CREATE TABLE t (x INT);"
        nullable = sqlsolver_constraints.ConstraintSpec("unique", "t", ("x",))

        with self.assertRaisesRegex(
            sqlsolver_constraints.SqlsolverSchemaConstraintError,
            "nullable UNIQUE",
        ):
            sqlsolver_constraints.materialize_schema_constraints(
                schema,
                [nullable],
                authority="test",
            )

        materialized, _ = sqlsolver_constraints.materialize_schema_constraints(
            schema,
            [
                sqlsolver_constraints.ConstraintSpec("not_null", "t", ("x",)),
                nullable,
            ],
            authority="test",
        )
        self.assertIn("x INT NOT NULL", materialized)
        self.assertIn("UNIQUE (x)", materialized)

    def test_existing_nullable_unique_is_also_rejected(self) -> None:
        with self.assertRaisesRegex(
            sqlsolver_constraints.SqlsolverSchemaConstraintError,
            "nullable UNIQUE",
        ):
            sqlsolver_constraints.materialize_schema_constraints(
                "CREATE TABLE t (x INT, UNIQUE (x));",
                [],
                authority="test",
            )

        rendered, _ = sqlsolver_constraints.materialize_schema_constraints(
            "CREATE TABLE t (x INT NOT NULL, UNIQUE (x));",
            [],
            authority="test",
        )
        self.assertIn("UNIQUE (x)", rendered)

    def test_foreign_key_requires_emitted_key_and_compatible_type(self) -> None:
        schema = "CREATE TABLE p (id INT); CREATE TABLE c (p_id VARCHAR(20));"
        foreign = sqlsolver_constraints.ConstraintSpec(
            "foreign_key",
            "c",
            ("p_id",),
            referenced_table="p",
            referenced_columns=("id",),
        )

        with self.assertRaisesRegex(
            sqlsolver_constraints.SqlsolverSchemaConstraintError,
            "not an emitted primary",
        ):
            sqlsolver_constraints.materialize_schema_constraints(
                schema,
                [foreign],
                authority="test",
            )

        primary = sqlsolver_constraints.ConstraintSpec("primary_key", "p", ("id",))
        with self.assertRaisesRegex(
            sqlsolver_constraints.SqlsolverSchemaConstraintError,
            "type mismatch",
        ):
            sqlsolver_constraints.materialize_schema_constraints(
                schema,
                [primary, foreign],
                authority="test",
            )

    def test_unknown_inline_or_pair_constraint_fails_closed(self) -> None:
        with self.assertRaisesRegex(
            sqlsolver_constraints.SqlsolverSchemaConstraintError,
            "inline key",
        ):
            sqlsolver_constraints.materialize_pair_constraints(
                "CREATE TABLE t (x INT UNIQUE);",
                [],
            )

        with self.assertRaisesRegex(
            sqlsolver_constraints.SqlsolverSchemaConstraintError,
            "unsupported kind",
        ):
            sqlsolver_constraints.materialize_pair_constraints(
                "CREATE TABLE t (x INT);",
                [{"check": {"value": "T__X"}}],
            )

    def test_wetune_nullable_unique_and_check_remain_conservative_residuals(
        self,
    ) -> None:
        sidecar = {
            "semanticSchema": {
                "tables": [
                    {
                        "name": "parent",
                        "columns": [
                            {"name": "id", "notNull": True},
                            {"name": "optional_code", "notNull": False},
                        ],
                    },
                    {
                        "name": "child",
                        "columns": [
                            {"name": "id", "notNull": True},
                            {"name": "parent_id", "notNull": False},
                        ],
                    },
                ]
            },
            "primaryKeys": [{"table": "parent", "columns": ["id"]}],
            "uniqueKeys": [
                {
                    "table": "parent",
                    "columns": ["optional_code"],
                    "nullableColumns": ["optional_code"],
                    "semantics": "sql_unique_allows_multiple_nulls",
                }
            ],
            "uniqueIndexes": [],
            "foreignKeys": [
                {
                    "table": "child",
                    "columns": ["parent_id"],
                    "refTable": "parent",
                    "refColumns": ["id"],
                }
            ],
            "checks": [{"table": "child", "expression": "parent_id > 0"}],
        }

        specs, residual = wetune_sqlsolver.sqlsolver_sidecar_constraint_specs(
            sidecar,
            {},
        )

        self.assertEqual(
            [item["kind"] for item in residual],
            ["nullable_unique_key", "check"],
        )
        self.assertTrue(any(spec.kind == "foreign_key" for spec in specs))
        self.assertFalse(
            any(
                spec.kind == "unique" and spec.columns == ("optional_code",)
                for spec in specs
            )
        )

    def test_wetune_rebuild_removes_nullable_base_unique_but_keeps_safe_key(
        self,
    ) -> None:
        tables = [
            wetune_sqlsolver.Table(
                name="users",
                columns=[
                    wetune_sqlsolver.Column("id", "INT", True),
                    wetune_sqlsolver.Column("secure_identifier", "VARCHAR(255)", False),
                    wetune_sqlsolver.Column("login", "VARCHAR(255)", True),
                ],
                primary_keys=[("id",)],
                unique_keys=[("secure_identifier",), ("login",)],
            )
        ]
        sidecar = {
            "semanticSchema": {
                "tables": [
                    {
                        "name": "users",
                        "columns": [
                            {"name": "id", "notNull": True},
                            {"name": "secure_identifier", "notNull": False},
                            {"name": "login", "notNull": True},
                        ],
                    }
                ]
            },
            "primaryKeys": [{"table": "users", "columns": ["id"]}],
            "uniqueKeys": [
                {
                    "table": "users",
                    "columns": ["secure_identifier"],
                    "nullableColumns": ["secure_identifier"],
                    "semantics": "sql_unique_allows_multiple_nulls",
                },
                {
                    "table": "users",
                    "columns": ["login"],
                    "nullableColumns": [],
                    "semantics": "sql_unique_allows_multiple_nulls",
                },
            ],
            "uniqueIndexes": [],
            "foreignKeys": [],
            "checks": [],
        }

        wetune_sqlsolver.remove_base_unique_keys_for_sqlsolver(tables)
        base = wetune_sqlsolver.render_schema(tables, {})
        specs, residual = wetune_sqlsolver.sqlsolver_sidecar_constraint_specs(
            sidecar,
            {},
        )
        rendered, _ = sqlsolver_constraints.materialize_schema_constraints(
            base,
            specs,
            authority="test",
        )

        self.assertNotIn("UNIQUE (secure_identifier)", rendered)
        self.assertIn("UNIQUE (login)", rendered)
        self.assertEqual(
            [item["kind"] for item in residual],
            ["nullable_unique_key"],
        )


class IntegrityContractMetadataTests(unittest.TestCase):
    def test_nonwetune_null_constraints_are_normalized_and_remain_authoritative(
        self,
    ) -> None:
        case = SimpleNamespace(
            benchmark={
                "id": "verieql-literature",
                "schemaScope": "pair",
                "constraintScope": "pair",
            },
            case_id="empty-constraints",
            source_metadata={},
            constraints=None,
            source_dialect="ansi_like",
            read_dialect="postgres",
            write_dialect="postgres",
            feature_tags=[],
        )
        config = {
            "defaults": {
                "adapter": "none",
                "writeDialect": "postgres",
                "frontendTargetDialectPurpose": "calcite_syntax_only",
                "semanticProfile": "formal-sql-core",
                "bagSemantics": True,
                "nullSemantics": "sql-three-valued-logic",
            }
        }

        metadata = nonwetune_sqlsolver.build_metadata(
            config,
            case,
            "verieql-literature__empty-constraints",
        )

        self.assertEqual(metadata["constraints"], [])
        self.assertEqual(
            metadata["integrityContract"]["sources"],
            [
                {"kind": "parser_facing_ddl", "path": "schema.sql"},
                {"kind": "pair_metadata", "path": "metadata.json#/constraints"},
            ],
        )
        self.assertTrue(metadata["integrityContract"]["authoritativeForLogos"])
        self.assertEqual(metadata["integrityContract"]["silentDrops"], 0)

    def test_wetune_metadata_names_sidecar_and_rename_map_without_claiming_full_ddl(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            schema_path = (
                root / "benchmarks/core/wetune/schemas/core/app.base.schema.sql"
            )
            constraints_path = schema_path.with_suffix(".constraints.json")
            constraints_path.parent.mkdir(parents=True)
            constraints_path.write_text("{}\n")
            semantic_constraints = {
                "checks": [],
                "foreignKeys": [],
                "primaryKeys": [],
                "semanticSchema": {
                    "tables": [],
                    "typeSemantics": wetune_sqlsolver.FROZEN_SIDECAR_RAW_TYPE_SEMANTICS,
                },
                "uniqueIndexes": [],
                "uniqueKeys": [],
                "unsupportedSemanticConstraints": [],
            }

            metadata = wetune_sqlsolver.build_metadata(
                root=root,
                case_id="7",
                app_name="app",
                rewrite_type="test",
                commit_url="https://example.invalid/commit",
                schema_path=schema_path,
                constraints_path=constraints_path,
                read_dialect="postgres",
                referenced_tables=set(),
                materialized_tables=[],
                semantic_constraints=semantic_constraints,
                rename_map={"read": "read_x"},
                lowering_audit={},
                status="materialized",
            )

        self.assertEqual(metadata["flatCaseId"], "wetune-issues__7")
        contract = metadata["integrityContract"]
        self.assertEqual(
            contract["semanticSidecar"],
            "benchmarks/core/wetune/schemas/core/app.base.schema.constraints.json",
        )
        self.assertEqual(
            contract["identifierRenames"],
            "metadata.json#/renamedIdentifiers",
        )
        self.assertEqual(contract["silentDrops"], 0)
        self.assertFalse(contract["sqlsolverDdlComplete"])
        self.assertEqual(
            contract["typeAuthority"],
            "parser_facing_normalized_ddl",
        )
        self.assertEqual(
            contract["sidecarAuthority"],
            "integrity_declarations_only",
        )
        self.assertEqual(
            contract["sidecarRawTypeSemantics"],
            wetune_sqlsolver.FROZEN_SIDECAR_RAW_TYPE_SEMANTICS,
        )
        self.assertEqual(
            contract["sidecarRawTypeSemanticsDisposition"],
            "preserved_for_audit_but_overridden_by_typeAuthority",
        )
        self.assertFalse(metadata["semanticConstraints"]["includedInSqlsolverDdl"])

    def test_wetune_sidecar_with_unsupported_forms_fails_closed(self) -> None:
        sidecar = {
            "checks": [],
            "foreignKeys": [],
            "primaryKeys": [],
            "semanticSchema": {
                "tables": [],
                "typeSemantics": wetune_sqlsolver.FROZEN_SIDECAR_RAW_TYPE_SEMANTICS,
            },
            "uniqueIndexes": [],
            "uniqueKeys": [],
            "unsupportedSemanticConstraints": [{"kind": "exclude"}],
        }

        with self.assertRaisesRegex(ValueError, "unsupported semantic constraint"):
            wetune_sqlsolver.validate_semantic_contract_sidecar(
                sidecar,
                Path("app.base.schema.constraints.json"),
            )

    def test_wetune_sidecar_raw_type_statement_is_exact_audit_metadata(self) -> None:
        sidecar = {
            "checks": [],
            "foreignKeys": [],
            "primaryKeys": [],
            "semanticSchema": {
                "tables": [],
                "typeSemantics": "normalized types are merely advisory",
            },
            "uniqueIndexes": [],
            "uniqueKeys": [],
            "unsupportedSemanticConstraints": [],
        }

        with self.assertRaisesRegex(ValueError, "frozen raw-source audit statement"):
            wetune_sqlsolver.validate_semantic_contract_sidecar(
                sidecar,
                Path("app.base.schema.constraints.json"),
            )


class IntegrityCoverageGeneratorTests(unittest.TestCase):
    REQUIRED_KINDS = [
        "not_null",
        "primary_key",
        "unique",
        "foreign_key",
        "check",
        "partial_expression_unique_index",
    ]

    @staticmethod
    def write_json(path: Path, value: object) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(value, indent=2) + "\n")

    def make_fixture(self, root: Path) -> tuple[Path, Path, Path, Path]:
        scope_path = (
            root / "var/codex-background/logos-integrity-constraints-v1.scope.json"
        )
        self.write_json(
            scope_path,
            {
                "scope_revision": integrity_coverage.SCOPE_REVISION,
                "benchmark_case_count": 2,
                "required_constraint_kinds": self.REQUIRED_KINDS,
            },
        )
        metadata_root = root / "benchmarks/core/.generated/sqlsolver"
        pair_dir = metadata_root / "nonwetune-flat/pair__1"
        pair_metadata = {
            "sourceBenchmark": "verieql-literature",
            "flatCaseId": "pair__1",
            "constraintScope": "pair",
            "constraints": [{"not_null": {"value": "items__id"}}],
            "integrityContract": {
                "authoritativeForLogos": True,
                "sources": [
                    {"kind": "parser_facing_ddl", "path": "schema.sql"},
                    {"kind": "pair_metadata", "path": "metadata.json#/constraints"},
                ],
                "silentDrops": 0,
                "sqlsolverDdlComplete": False,
            },
        }
        self.write_json(pair_dir / "metadata.json", pair_metadata)
        (pair_dir / "schema.sql").write_text(
            "CREATE TABLE items (id INTEGER NOT NULL, code TEXT, "
            "PRIMARY KEY (id), UNIQUE (code));\n"
        )

        sidecar_relative = Path(
            "benchmarks/core/wetune/schemas/core/app.base.schema.constraints.json"
        )
        sidecar_path = root / sidecar_relative
        sidecar = {
            "checks": [
                {"table": "child", "expression": "active", "source": "create_table"}
            ],
            "foreignKeys": [
                {
                    "table": "child",
                    "columns": ["parent_id"],
                    "refTable": "parent",
                    "refColumns": ["id"],
                    "actions": "",
                    "source": "alter_table",
                }
            ],
            "primaryKeys": [{"table": "parent", "columns": ["id"]}],
            "semanticSchema": {
                "typeSemantics": integrity_coverage.FROZEN_SIDECAR_RAW_TYPE_SEMANTICS,
                "tables": [
                    {
                        "name": "child",
                        "columns": [
                            {"name": "id", "notNull": True},
                            {"name": "parent_id", "notNull": False},
                            {"name": "active", "notNull": True},
                        ],
                    },
                    {
                        "name": "parent",
                        "columns": [
                            {"name": "id", "notNull": True},
                            {"name": "code", "notNull": False},
                        ],
                    },
                ],
            },
            "uniqueIndexes": [
                {
                    "table": "child",
                    "terms": ["id"],
                    "where": "active",
                    "source": "create_unique_index",
                }
            ],
            "uniqueKeys": [
                {
                    "table": "parent",
                    "columns": ["code"],
                    "nullableColumns": ["code"],
                    "semantics": "sql_unique_allows_multiple_nulls",
                }
            ],
            "unsupportedSemanticConstraints": [],
        }
        self.write_json(sidecar_path, sidecar)

        wetune_dir = metadata_root / "wetune-issues/7"
        wetune_metadata = {
            "sourceBenchmark": "wetune-issues",
            "sourceCase": "7",
            "flatCaseId": "wetune-issues__7",
            "appName": "app",
            "semanticConstraints": {
                "source": sidecar_relative.as_posix(),
                "columns": 5,
                "typeLowerings": 0,
                "primaryKeys": 1,
                "uniqueKeys": 1,
                "uniqueIndexes": 1,
                "foreignKeys": 1,
                "checks": 1,
                "unsupportedSemanticConstraints": 0,
                "includedInSqlsolverDdl": False,
            },
            "renamedIdentifiers": {},
            "integrityContract": {
                "authoritativeForLogos": True,
                "sourceKind": "wetune_base_schema_sidecar",
                "typeAuthority": "parser_facing_normalized_ddl",
                "sidecarAuthority": "integrity_declarations_only",
                "parserFacingDdl": "schema.sql",
                "semanticSidecar": sidecar_relative.as_posix(),
                "sidecarRawTypeSemantics": (
                    integrity_coverage.FROZEN_SIDECAR_RAW_TYPE_SEMANTICS
                ),
                "sidecarRawTypeSemanticsDisposition": (
                    "preserved_for_audit_but_overridden_by_typeAuthority"
                ),
                "identifierRenames": "metadata.json#/renamedIdentifiers",
                "silentDrops": 0,
                "sqlsolverDdlComplete": False,
            },
        }
        self.write_json(wetune_dir / "metadata.json", wetune_metadata)
        (wetune_dir / "schema.sql").write_text(
            "CREATE TABLE child (id INTEGER NOT NULL, parent_id INTEGER, active BOOLEAN);\n"
        )
        return scope_path, metadata_root, pair_dir / "metadata.json", sidecar_path

    def generate(
        self, root: Path, scope_path: Path, metadata_root: Path, aligned: bool
    ):
        return integrity_coverage.generate_coverage(
            root=root,
            scope_path=scope_path,
            metadata_root=metadata_root,
            aligned=aligned,
        )

    def test_exact_coverage_requires_explicit_alignment_attestation(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            scope_path, metadata_root, _pair, _sidecar = self.make_fixture(root)

            draft = self.generate(root, scope_path, metadata_root, aligned=False)
            aligned = self.generate(root, scope_path, metadata_root, aligned=True)

        self.assertEqual(
            [entry["case_id"] for entry in draft["cases"]],
            ["pair__1", "wetune-issues__7"],
        )
        self.assertIsNone(draft["silent_drops"])
        self.assertFalse(draft["cases"][0]["rocq_aligned"])
        self.assertIsNone(draft["cases"][0]["silent_drops"])
        self.assertEqual(aligned["silent_drops"], 0)
        self.assertTrue(all(entry["rocq_aligned"] for entry in aligned["cases"]))
        self.assertTrue(all(entry["validator_aligned"] for entry in aligned["cases"]))
        self.assertTrue(
            all(entry["agent_context_aligned"] for entry in aligned["cases"])
        )
        wetune = next(
            entry for entry in aligned["cases"] if entry["case_id"].startswith("wetune")
        )
        self.assertEqual(wetune["constraint_kinds"], self.REQUIRED_KINDS)

    def test_unknown_pair_constraint_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            scope_path, metadata_root, pair_path, _sidecar = self.make_fixture(root)
            pair = json.loads(pair_path.read_text())
            pair["constraints"] = [{"mystery": {"value": "items__id"}}]
            self.write_json(pair_path, pair)

            with self.assertRaisesRegex(
                integrity_coverage.CoverageError, "unknown pair"
            ):
                self.generate(root, scope_path, metadata_root, aligned=False)

    def test_sidecar_unknown_or_unsupported_forms_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            scope_path, metadata_root, _pair, sidecar_path = self.make_fixture(root)
            sidecar = json.loads(sidecar_path.read_text())
            sidecar["unsupportedSemanticConstraints"] = [{"kind": "exclude"}]
            self.write_json(sidecar_path, sidecar)

            with self.assertRaisesRegex(
                integrity_coverage.CoverageError, "unsupported forms"
            ):
                self.generate(root, scope_path, metadata_root, aligned=False)

    def test_wetune_authority_markers_fail_closed_when_changed(self) -> None:
        mutations = {
            "typeAuthority": "raw_source_type",
            "sidecarAuthority": "types_and_constraints",
            "sidecarRawTypeSemantics": "normalizedFrontendType is advisory",
            "sidecarRawTypeSemanticsDisposition": "preserved_only",
        }
        for field, invalid_value in mutations.items():
            with self.subTest(field=field), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                scope_path, metadata_root, _pair, _sidecar = self.make_fixture(root)
                metadata_path = metadata_root / "wetune-issues/7/metadata.json"
                metadata = json.loads(metadata_path.read_text())
                metadata["integrityContract"][field] = invalid_value
                self.write_json(metadata_path, metadata)

                with self.assertRaises(integrity_coverage.CoverageError):
                    self.generate(root, scope_path, metadata_root, aligned=False)

    def test_wetune_unique_null_semantics_and_nullable_columns_fail_closed(
        self,
    ) -> None:
        mutations = {
            "semantics": "nulls_not_distinct",
            "nullableColumns": [],
        }
        for field, invalid_value in mutations.items():
            with self.subTest(field=field), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                scope_path, metadata_root, _pair, sidecar_path = self.make_fixture(root)
                sidecar = json.loads(sidecar_path.read_text())
                sidecar["uniqueKeys"][0][field] = invalid_value
                self.write_json(sidecar_path, sidecar)

                with self.assertRaisesRegex(
                    integrity_coverage.CoverageError,
                    "semantics|nullableColumns",
                ):
                    self.generate(root, scope_path, metadata_root, aligned=False)

    def test_wetune_sidecar_type_statement_and_sources_fail_closed(self) -> None:
        mutations = (
            ("typeSemantics", "raw types are not retained"),
            ("uniqueIndexSource", "alter_table"),
        )
        for mutation, invalid_value in mutations:
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                scope_path, metadata_root, _pair, sidecar_path = self.make_fixture(root)
                sidecar = json.loads(sidecar_path.read_text())
                if mutation == "typeSemantics":
                    sidecar["semanticSchema"]["typeSemantics"] = invalid_value
                else:
                    sidecar["uniqueIndexes"][0]["source"] = invalid_value
                self.write_json(sidecar_path, sidecar)

                with self.assertRaisesRegex(
                    integrity_coverage.CoverageError,
                    "typeSemantics|source",
                ):
                    self.generate(root, scope_path, metadata_root, aligned=False)

    def test_wetune_selected_sidecar_must_be_exact_base_path(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            scope_path, metadata_root, _pair, _sidecar = self.make_fixture(root)
            metadata_path = metadata_root / "wetune-issues/7/metadata.json"
            metadata = json.loads(metadata_path.read_text())
            opt_path = (
                "benchmarks/core/wetune/schemas/core/app.opt.schema.constraints.json"
            )
            metadata["semanticConstraints"]["source"] = opt_path
            metadata["integrityContract"]["semanticSidecar"] = opt_path
            self.write_json(metadata_path, metadata)

            with self.assertRaisesRegex(integrity_coverage.CoverageError, "requires"):
                self.generate(root, scope_path, metadata_root, aligned=False)

    def test_missing_or_duplicate_flat_ids_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            scope_path, metadata_root, pair_path, _sidecar = self.make_fixture(root)
            pair = json.loads(pair_path.read_text())
            pair.pop("flatCaseId")
            self.write_json(pair_path, pair)
            with self.assertRaisesRegex(integrity_coverage.CoverageError, "flatCaseId"):
                self.generate(root, scope_path, metadata_root, aligned=False)


class DirectScriptImportTests(unittest.TestCase):
    def test_all_consumers_import_shared_module_when_run_directly(self) -> None:
        for script_name in (
            "materialize_cosette.py",
            "materialize_nonwetune_sqlsolver.py",
            "materialize_qed.py",
            "materialize_wetune_sqlsolver.py",
            "sanitize_wetune_schema.py",
        ):
            with self.subTest(script=script_name):
                completed = subprocess.run(
                    [sys.executable, str(MATERIALIZER_DIR / script_name), "--help"],
                    text=True,
                    capture_output=True,
                    check=False,
                )
                self.assertEqual(completed.returncode, 0, completed.stderr)

    def test_coverage_generator_imports_directly(self) -> None:
        completed = subprocess.run(
            [sys.executable, str(COVERAGE_SCRIPT), "--help"],
            text=True,
            capture_output=True,
            check=False,
        )
        self.assertEqual(completed.returncode, 0, completed.stderr)


if __name__ == "__main__":
    unittest.main()
