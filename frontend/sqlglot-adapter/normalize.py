#!/usr/bin/env python3
import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import sqlglot
from sqlglot import exp
from sqlglot.dialects import Dialect
from sqlglot.dialects.postgres import Postgres
from sqlglot.tokens import Token, TokenType, Tokenizer


CODE = 0
SINGLE_QUOTED = 1
DOUBLE_QUOTED = 2
BACKTICK_QUOTED = 3
COMMENT = 4
DOLLAR_QUOTED = 5


def postgres_identifier_continuation(char: str) -> bool:
    """Whether ``char`` can continue an unquoted PostgreSQL identifier."""
    return (
        char == "_"
        or char == "$"
        or (char.isascii() and char.isalnum())
        or not char.isascii()
    )


def postgres_escape_string_prefix_at(sql: str, index: int) -> bool:
    """Whether ``index`` starts the standalone E/e prefix of an E-string."""
    return (
        sql[index] in "Ee"
        and index + 1 < len(sql)
        and sql[index + 1] == "'"
        and (
            index == 0
            or not postgres_identifier_continuation(sql[index - 1])
        )
    )


def postgres_quoted_end(
    sql: str,
    quote_start: int,
    quote: str,
    *,
    backslash_escapes: bool,
) -> int:
    """Return a conservative end offset for one PostgreSQL quoted token."""
    end = quote_start + 1
    while end < len(sql):
        if backslash_escapes and sql[end] == "\\" and end + 1 < len(sql):
            end += 2
            continue
        if sql[end] == quote:
            if end + 1 < len(sql) and sql[end + 1] == quote:
                end += 2
                continue
            return end + 1
        end += 1
    return len(sql)


def postgres_dollar_quote_delimiter_at(
    sql: str, index: int
) -> tuple[str | None, bool]:
    """Return a dollar delimiter and whether an unsupported tag must fail closed."""
    if sql[index] != "$":
        return None, False
    if index > 0 and postgres_identifier_continuation(sql[index - 1]):
        return None, False
    if index + 1 < len(sql) and sql[index + 1] == "$":
        return "$$", False
    if index + 1 >= len(sql):
        return None, False

    first = sql[index + 1]
    if not first.isascii():
        return None, True
    if not (first.isalpha() or first == "_"):
        return None, False

    end = index + 2
    while end < len(sql):
        char = sql[end]
        if char == "$":
            return sql[index : end + 1], False
        if not char.isascii():
            return None, True
        if not (char.isalnum() or char == "_"):
            return None, False
        end += 1
    return None, False


class CalcitePostgres(Postgres):
    """PostgreSQL generator with Calcite's spelling for one SQL type.

    Rendering the type from its SQLGlot ``DataType`` node keeps identifiers
    named ``timestamptz`` completely outside this compatibility adaptation.
    """

    class Generator(Postgres.Generator):
        def datatype_sql(self, expression: exp.DataType) -> str:
            if expression.is_type(exp.DType.TIMESTAMPTZ):
                precision = self.expressions(expression, flat=True)
                if precision:
                    return f"TIMESTAMP({precision}) WITH TIME ZONE"
                return "TIMESTAMP WITH TIME ZONE"
            return super().datatype_sql(expression)


class AliasStyleNormalizationError(Exception):
    def __init__(self, code: str, message: str, **details: Any) -> None:
        super().__init__(message)
        self.code = code
        self.details = details

    def report_entry(self) -> dict:
        return {
            "stage": "postgres_implicit_alias_style",
            "type": type(self).__name__,
            "code": self.code,
            "message": str(self),
            **self.details,
        }


class OrderAliasNormalizationError(Exception):
    def __init__(self, code: str, message: str, **details: Any) -> None:
        super().__init__(message)
        self.code = code
        self.details = details

    def report_entry(self) -> dict:
        return {
            "stage": "postgres_order_alias_expression",
            "type": type(self).__name__,
            "code": self.code,
            "message": str(self),
            **self.details,
        }


class IdentifierFoldingError(Exception):
    def __init__(self, code: str, message: str, **details: Any) -> None:
        super().__init__(message)
        self.code = code
        self.details = details

    def report_entry(self) -> dict:
        return {
            "stage": "postgres_identifier_folding",
            "type": type(self).__name__,
            "code": self.code,
            "message": str(self),
            **self.details,
        }


@dataclass(frozen=True)
class IdentifierSite:
    path: tuple[str | int, ...]
    name: str
    quoted: bool
    postgres_name: str

    def report_value(self) -> dict:
        return {
            "path": list(self.path),
            "text": self.name,
            "quoted": self.quoted,
            "postgresName": self.postgres_name,
        }


@dataclass(frozen=True)
class AliasSite:
    path: tuple[str | int, ...]
    kind: str
    name: str
    quoted: bool
    postgres_name: str
    explicit_as: bool
    alias_start: int
    alias_end: int

    def report_value(self) -> dict:
        return {
            "path": list(self.path),
            "kind": self.kind,
            "identifier": {
                "text": self.name,
                "quoted": self.quoted,
                "postgresName": self.postgres_name,
            },
            "explicitAs": self.explicit_as,
        }


def sql_lexical_contexts(sql: str) -> bytearray:
    """Classify each character without interpreting text inside SQL quoting.

    Compatibility patches are intentionally small textual rewrites, but a
    regex match inside an identifier, literal, or comment is observable SQL
    corruption.  This scanner is conservative: malformed or unterminated
    protected regions remain protected through end-of-input.
    """
    contexts = bytearray(len(sql))

    def protect(start: int, end: int, context: int) -> None:
        contexts[start:end] = bytes([context]) * (end - start)

    index = 0
    while index < len(sql):
        if sql.startswith("--", index):
            end = sql.find("\n", index + 2)
            end = len(sql) if end < 0 else end
            protect(index, end, COMMENT)
            index = end
            continue
        if sql.startswith("/*", index):
            depth = 1
            end = index + 2
            while end < len(sql) and depth:
                if sql.startswith("/*", end):
                    depth += 1
                    end += 2
                elif sql.startswith("*/", end):
                    depth -= 1
                    end += 2
                else:
                    end += 1
            protect(index, end, COMMENT)
            index = end
            continue

        if postgres_escape_string_prefix_at(sql, index):
            end = postgres_quoted_end(
                sql,
                index + 1,
                "'",
                backslash_escapes=True,
            )
            protect(index, end, SINGLE_QUOTED)
            index = end
            continue

        quote_context = {
            "'": SINGLE_QUOTED,
            '"': DOUBLE_QUOTED,
            "`": BACKTICK_QUOTED,
        }.get(sql[index])
        if quote_context is not None:
            quote = sql[index]
            end = postgres_quoted_end(
                sql,
                index,
                quote,
                backslash_escapes=False,
            )
            protect(index, end, quote_context)
            index = end
            continue

        if sql[index] == "$":
            marker, unsupported_tag = postgres_dollar_quote_delimiter_at(
                sql, index
            )
            if unsupported_tag:
                protect(index, len(sql), DOLLAR_QUOTED)
                break
            if marker is not None:
                close = sql.find(marker, index + len(marker))
                end = len(sql) if close < 0 else close + len(marker)
                protect(index, end, DOLLAR_QUOTED)
                index = end
                continue
        index += 1
    return contexts


def sub_at_sql_code(
    pattern: re.Pattern,
    repl,
    sql: str,
    *,
    allowed_contexts: frozenset[int] = frozenset({CODE}),
) -> str:
    contexts = sql_lexical_contexts(sql)

    def guarded(match: re.Match) -> str:
        start = match.start()
        if start >= len(contexts):
            return match.group(0)
        context = contexts[start]
        if context not in allowed_contexts:
            return match.group(0)
        if context != CODE and (
            (start > 0 and contexts[start - 1] == context)
            or (start >= 2 and sql[start - 2 : start].upper() == "U&")
        ):
            # A non-code match is allowed only at the opening delimiter of
            # that protected run. This prevents a regex from treating an
            # escaped quote inside an identifier as a fresh identifier, and
            # avoids partially rewriting PostgreSQL U&"..." syntax.
            return match.group(0)
        if context in allowed_contexts:
            return repl(match)
        return match.group(0)

    return pattern.sub(guarded, sql)


def timestamp_with_local_time_zone_error(statement_index: int) -> dict:
    return {
        "stage": "calcite_postgres_type_validation",
        "type": "UnsupportedTypeSemantics",
        "code": "timestamp_with_local_time_zone_unsupported",
        "message": (
            "TIMESTAMP WITH LOCAL TIME ZONE has distinct session/database "
            "semantics and is not a spelling variant of PostgreSQL timestamptz"
        ),
        "statement": statement_index,
    }


def inspect_source_type_semantics(sql: str, read: str) -> dict | None:
    """Reject unsupported source types before any output-dialect rendering."""
    statement_index = 0
    for parsed in sqlglot.parse(sql, read=read):
        if parsed is None or not is_effective_statement(parsed.sql(dialect=read)):
            continue
        statement_index += 1
        for node in parsed.walk():
            if isinstance(node, exp.DataType) and node.is_type(
                exp.DType.TIMESTAMPLTZ
            ):
                return timestamp_with_local_time_zone_error(statement_index)
    return None


def inspect_calcite_postgres_types(
    statements: list[str], normalizations: list[dict]
) -> dict | None:
    """Record structured TIMESTAMPTZ rendering and reject rendered LOCAL types."""
    for statement_index, statement in enumerate(statements, start=1):
        try:
            parsed = sqlglot.parse_one(statement, read="postgres")
        except Exception as exc:
            return {
                "stage": "calcite_postgres_type_validation",
                "type": type(exc).__name__,
                "code": "generated_statement_reparse_failed",
                "message": str(exc),
                "statement": statement_index,
            }
        for node in parsed.walk():
            if not isinstance(node, exp.DataType):
                continue
            if node.is_type(exp.DType.TIMESTAMPLTZ):
                return timestamp_with_local_time_zone_error(statement_index)
            if node.is_type(exp.DType.TIMESTAMPTZ):
                source = node.sql(dialect="postgres")
                target = node.sql(dialect=CalcitePostgres)
                normalizations.append(
                    {
                        "kind": "calcite_timestamptz_type",
                        "statement": statement_index,
                        "source": source,
                        "target": target,
                    }
                )
    return None


def patch_calcite_interval_literals(sql: str, normalizations: list[dict]) -> str:
    pattern = re.compile(
        r"INTERVAL[ \t\n\r\f\v]+'([0-9]+)[ \t\n\r\f\v]+"
        r"(DAY|DAYS|HOUR|HOURS|MINUTE|MINUTES|MONTH|MONTHS|QUARTER|QUARTERS|SECOND|SECONDS|WEEK|WEEKS|YEAR|YEARS)'",
        flags=re.IGNORECASE | re.ASCII,
    )

    def repl(match: re.Match) -> str:
        keyword_start = match.start()
        if keyword_start > 0:
            previous = sql[keyword_start - 1]
            if (
                previous.isascii()
                and (previous.isalnum() or previous in "_$.")
            ) or ord(previous) >= 0x80:
                return match.group(0)

        unit = match.group(2).upper()
        if unit.endswith("S"):
            unit = unit[:-1]
        normalizations.append(
            {
                "kind": "calcite_interval_literal",
                "source": match.group(0),
                "target": f"INTERVAL '{match.group(1)}' {unit}",
            }
        )
        return f"INTERVAL '{match.group(1)}' {unit}"

    return sub_at_sql_code(pattern, repl, sql)


def _walk_expression_paths(
    expression: exp.Expression, path: tuple[str | int, ...] = ()
):
    yield expression, path
    for key in sorted(expression.args):
        child = expression.args[key]
        if isinstance(child, exp.Expression):
            yield from _walk_expression_paths(child, path + (key,))
        elif isinstance(child, list):
            for index, item in enumerate(child):
                if isinstance(item, exp.Expression):
                    yield from _walk_expression_paths(item, path + (key, index))


def _postgres_identifier_name(identifier: exp.Identifier) -> str:
    if bool(identifier.args.get("quoted")):
        return str(identifier.this)
    canonical = identifier.copy()
    Dialect.get_or_raise("postgres").normalize_identifier(canonical)
    return str(canonical.this)


def _fold_unquoted_postgres_identifiers(statement: exp.Expression) -> None:
    postgres = Dialect.get_or_raise("postgres")
    for node in statement.walk():
        if isinstance(node, exp.Identifier) and not bool(node.args.get("quoted")):
            postgres.normalize_identifier(node)


def _collect_identifier_sites(statement: exp.Expression) -> list[IdentifierSite]:
    return [
        IdentifierSite(
            path=path,
            name=str(node.this),
            quoted=bool(node.args.get("quoted")),
            postgres_name=_postgres_identifier_name(node),
        )
        for node, path in _walk_expression_paths(statement)
        if isinstance(node, exp.Identifier)
    ]


def _require_identifier_sites(
    source: list[IdentifierSite],
    candidate: list[IdentifierSite],
    *,
    statement_index: int,
    stage: str,
    generated_quoted: bool,
) -> None:
    if len(source) != len(candidate):
        raise IdentifierFoldingError(
            "identifier_count_changed",
            "SQLGlot changed the number of PostgreSQL identifiers while canonicalizing them",
            statement=statement_index,
            auditStage=stage,
            sourceCount=len(source),
            candidateCount=len(candidate),
        )
    for source_site, candidate_site in zip(source, candidate):
        expected_quoted = True if generated_quoted else source_site.quoted
        if (
            candidate_site.path != source_site.path
            or candidate_site.name != source_site.postgres_name
            or candidate_site.quoted != expected_quoted
        ):
            raise IdentifierFoldingError(
                "identifier_identity_changed",
                "SQLGlot could not preserve PostgreSQL identifier quote identity and folding",
                statement=statement_index,
                auditStage=stage,
                sourceIdentifier=source_site.report_value(),
                candidateIdentifier=candidate_site.report_value(),
                expectedQuoted=expected_quoted,
            )


def transpile_with_postgres_identifier_folding(
    sql: str,
    *,
    read: str,
    write_dialect,
    pretty: bool,
    normalizations: list[dict],
) -> list[str]:
    """Quote PostgreSQL identifiers only after applying source folding.

    SQLGlot's ``identify=True`` quotes the spelling it parsed. Without this
    pass, an unquoted PostgreSQL ``DEPT`` becomes ``"DEPT"`` and changes
    identity instead of resolving as ``dept``. The two audits make the
    transformation fail closed if either AST normalization or rendering loses
    the source distinction between quoted and unquoted identifiers.
    """
    writer = Dialect.get_or_raise(write_dialect)
    statements = []
    for statement_index, statement in enumerate(
        sqlglot.parse(sql, read=read), start=1
    ):
        if statement is None:
            statements.append("")
            continue
        source_sites = _collect_identifier_sites(statement)
        _fold_unquoted_postgres_identifiers(statement)
        canonical_sites = _collect_identifier_sites(statement)
        _require_identifier_sites(
            source_sites,
            canonical_sites,
            statement_index=statement_index,
            stage="canonical_ast",
            generated_quoted=False,
        )
        generated = writer.generate(
            statement, copy=False, identify=True, pretty=pretty
        )
        try:
            reparsed = sqlglot.parse_one(generated, read="postgres")
        except Exception as exc:
            raise IdentifierFoldingError(
                "generated_statement_reparse_failed",
                "SQLGlot could not reparse its identifier-canonicalized PostgreSQL output",
                statement=statement_index,
                generatedSql=generated,
                causeType=type(exc).__name__,
                cause=str(exc),
            ) from exc
        _require_identifier_sites(
            source_sites,
            _collect_identifier_sites(reparsed),
            statement_index=statement_index,
            stage="generated_sql",
            generated_quoted=True,
        )
        folded = [
            {
                "path": list(site.path),
                "source": site.name,
                "target": site.postgres_name,
            }
            for site in source_sites
            if not site.quoted and site.name != site.postgres_name
        ]
        if folded:
            normalizations.append(
                {
                    "kind": "postgres_unquoted_identifier_folding",
                    "statement": statement_index,
                    "identifiers": folded,
                }
            )
        statements.append(generated)
    return statements


def _is_from_or_join_relation(expression: exp.Expression) -> bool:
    ancestor = expression.parent
    while ancestor is not None:
        if isinstance(ancestor, (exp.From, exp.Join)):
            return True
        if isinstance(ancestor, exp.Select):
            return False
        ancestor = ancestor.parent
    return False


def _token_at_identifier(tokens: list[Token], identifier: exp.Identifier) -> tuple[int, Token]:
    start = identifier.meta.get("start")
    end = identifier.meta.get("end")
    if not isinstance(start, int) or not isinstance(end, int):
        raise AliasStyleNormalizationError(
            "missing_alias_offset",
            "SQLGlot alias identifier is missing exact source offsets",
            identifier=identifier.sql(dialect="postgres"),
        )
    for index, token in enumerate(tokens):
        if token.start == start and token.end == end:
            return index, token
    raise AliasStyleNormalizationError(
        "missing_alias_token",
        "SQLGlot alias identifier has no token at its exact source offsets",
        identifier=identifier.sql(dialect="postgres"),
        start=start,
        end=end,
    )


def _collect_alias_sites(
    statement: exp.Expression, tokens: list[Token]
) -> list[AliasSite]:
    # Query aliases nested inside DDL are deliberately outside this adapter
    # repair. In particular, CREATE ... AS must never be mistaken for an
    # optional SELECT or relation alias marker.
    if isinstance(statement, exp.DDL):
        return []

    sites = []
    for node, path in _walk_expression_paths(statement):
        identifier = None
        kind = None
        if (
            isinstance(node, exp.Alias)
            and isinstance(node.parent, exp.Select)
            and node.arg_key == "expressions"
        ):
            identifier = node.args.get("alias")
            kind = "select_expression_alias"
        elif isinstance(node, exp.TableAlias) and isinstance(
            node.parent, (exp.Table, exp.Subquery)
        ):
            if _is_from_or_join_relation(node.parent):
                identifier = node.this
                kind = (
                    "subquery_relation_alias"
                    if isinstance(node.parent, exp.Subquery)
                    else "table_relation_alias"
                )

        if kind is None or not isinstance(identifier, exp.Identifier):
            continue

        token_index, _ = _token_at_identifier(tokens, identifier)
        previous = tokens[token_index - 1] if token_index else None
        explicit_as = bool(
            previous is not None
            and previous.token_type == TokenType.ALIAS
            and previous.text.upper() == "AS"
        )
        name = str(identifier.this)
        quoted = bool(identifier.args.get("quoted"))
        sites.append(
            AliasSite(
                path=path,
                kind=kind,
                name=name,
                quoted=quoted,
                postgres_name=_postgres_identifier_name(identifier),
                explicit_as=explicit_as,
                alias_start=int(identifier.meta["start"]),
                alias_end=int(identifier.meta["end"]),
            )
        )
    return sites


def _alias_sites_match(source: AliasSite, generated: AliasSite, identify: bool) -> bool:
    expected_generated_quoted = source.quoted or identify
    expected_generated_name = (
        source.postgres_name if identify and not source.quoted else source.name
    )
    return (
        source.path == generated.path
        and source.kind == generated.kind
        and expected_generated_name == generated.name
        and generated.quoted == expected_generated_quoted
        and source.postgres_name == generated.postgres_name
        and generated.explicit_as
    )


def _remove_generated_alias_as_tokens(
    generated_sql: str,
    tokens: list[Token],
    sites: list[AliasSite],
) -> tuple[str, list[tuple[AliasSite, int, int]]]:
    removals = []
    for site in sites:
        if site.explicit_as:
            continue
        alias_index = next(
            (
                index
                for index, token in enumerate(tokens)
                if token.start == site.alias_start and token.end == site.alias_end
            ),
            None,
        )
        if alias_index is None or alias_index == 0:
            raise AliasStyleNormalizationError(
                "missing_generated_alias_as",
                "generated implicit-alias site has no preceding AS token",
                site=site.report_value(),
            )
        marker = tokens[alias_index - 1]
        if marker.token_type != TokenType.ALIAS or marker.text.upper() != "AS":
            raise AliasStyleNormalizationError(
                "missing_generated_alias_as",
                "generated token immediately before an implicit alias is not AS",
                site=site.report_value(),
                token=marker.text,
            )

        # SQLGlot emits whitespace around AS. Delete AS and only the following
        # whitespace; comments and every other protected token remain intact.
        removal_end = marker.end + 1
        while removal_end < site.alias_start and generated_sql[removal_end].isspace():
            removal_end += 1
        removals.append((site, marker.start, removal_end))

    edited = generated_sql
    for _, start, end in sorted(removals, key=lambda item: item[1], reverse=True):
        edited = edited[:start] + edited[end:]
    return edited, removals


def _metadata_free_ast(expression: exp.Expression) -> list[dict]:
    copied = expression.copy()
    for node in copied.walk():
        node.meta.clear()
    return copied.dump()


def preserve_postgres_implicit_alias_style(
    source_sql: str,
    generated_statements: list[str],
    identify: bool,
    normalizations: list[dict],
) -> list[str]:
    try:
        source_expressions = [
            statement
            for statement in sqlglot.parse(source_sql, read="postgres")
            if statement is not None
            and is_effective_statement(statement.sql(dialect="postgres"))
        ]
    except Exception as exc:
        raise AliasStyleNormalizationError(
            "source_reparse_failed",
            "patched PostgreSQL source could not be reparsed for alias preservation",
            parserErrorType=type(exc).__name__,
            parserError=str(exc),
        ) from exc

    if len(source_expressions) != len(generated_statements):
        raise AliasStyleNormalizationError(
            "statement_count_mismatch",
            "source and generated PostgreSQL statement counts differ during alias preservation",
            sourceStatementCount=len(source_expressions),
            generatedStatementCount=len(generated_statements),
        )

    try:
        source_tokens = Tokenizer(dialect="postgres").tokenize(source_sql)
    except Exception as exc:
        raise AliasStyleNormalizationError(
            "source_tokenize_failed",
            "patched PostgreSQL source could not be tokenized for alias preservation",
            parserErrorType=type(exc).__name__,
            parserError=str(exc),
        ) from exc
    preserved = []
    for statement_index, (source_ast, generated_sql) in enumerate(
        zip(source_expressions, generated_statements), start=1
    ):
        try:
            generated_asts = [
                statement
                for statement in sqlglot.parse(generated_sql, read="postgres")
                if statement is not None
                and is_effective_statement(statement.sql(dialect="postgres"))
            ]
            if len(generated_asts) != 1:
                raise AliasStyleNormalizationError(
                    "generated_statement_count_mismatch",
                    "one generated PostgreSQL statement reparsed as a different statement count",
                    generatedStatementCount=len(generated_asts),
                )
            generated_ast = generated_asts[0]
            generated_tokens = Tokenizer(dialect="postgres").tokenize(generated_sql)
            source_sites = _collect_alias_sites(source_ast, source_tokens)
            generated_sites = _collect_alias_sites(generated_ast, generated_tokens)
        except AliasStyleNormalizationError as exc:
            exc.details.setdefault("statement", statement_index)
            raise
        except Exception as exc:
            raise AliasStyleNormalizationError(
                "generated_reparse_failed",
                "generated PostgreSQL statement could not be reparsed for alias preservation",
                statement=statement_index,
                parserErrorType=type(exc).__name__,
                parserError=str(exc),
            ) from exc

        if len(source_sites) != len(generated_sites):
            raise AliasStyleNormalizationError(
                "alias_site_count_mismatch",
                "source and generated alias-site counts differ",
                statement=statement_index,
                sourceSites=[site.report_value() for site in source_sites],
                generatedSites=[site.report_value() for site in generated_sites],
            )
        for source_site, generated_site in zip(source_sites, generated_sites):
            if not _alias_sites_match(source_site, generated_site, identify):
                raise AliasStyleNormalizationError(
                    "alias_site_mismatch",
                    "source and generated alias sites do not form an exact ordered bijection",
                    statement=statement_index,
                    sourceSite=source_site.report_value(),
                    generatedSite=generated_site.report_value(),
                )

        implicit_generated_sites = [
            AliasSite(
                path=generated.path,
                kind=generated.kind,
                name=generated.name,
                quoted=generated.quoted,
                postgres_name=generated.postgres_name,
                explicit_as=source.explicit_as,
                alias_start=generated.alias_start,
                alias_end=generated.alias_end,
            )
            for source, generated in zip(source_sites, generated_sites)
        ]
        edited, removals = _remove_generated_alias_as_tokens(
            generated_sql, generated_tokens, implicit_generated_sites
        )
        try:
            edited_asts = [
                statement
                for statement in sqlglot.parse(edited, read="postgres")
                if statement is not None
                and is_effective_statement(statement.sql(dialect="postgres"))
            ]
        except Exception as exc:
            raise AliasStyleNormalizationError(
                "edited_reparse_failed",
                "AS removal made a generated PostgreSQL statement unparsable",
                statement=statement_index,
                parserErrorType=type(exc).__name__,
                parserError=str(exc),
            ) from exc
        if len(edited_asts) != 1:
            raise AliasStyleNormalizationError(
                "edited_statement_count_mismatch",
                "AS removal changed the generated PostgreSQL statement count",
                statement=statement_index,
                editedStatementCount=len(edited_asts),
            )
        edited_ast = edited_asts[0]
        if _metadata_free_ast(generated_ast) != _metadata_free_ast(edited_ast):
            raise AliasStyleNormalizationError(
                "edited_ast_changed",
                "AS removal changed the generated PostgreSQL statement AST",
                statement=statement_index,
            )

        source_sites_by_role = {
            (site.path, site.kind): site for site in source_sites
        }
        for site, _, _ in removals:
            source_site = source_sites_by_role[(site.path, site.kind)]
            normalizations.append(
                {
                    "kind": "postgres_implicit_alias_style",
                    "statement": statement_index,
                    "siteKind": site.kind,
                    "sitePath": list(site.path),
                    "sourceIdentifier": {
                        "text": source_site.name,
                        "quoted": source_site.quoted,
                        "postgresName": source_site.postgres_name,
                    },
                    "generatedIdentifier": {
                        "text": site.name,
                        "quoted": site.quoted,
                        "postgresName": site.postgres_name,
                    },
                    "sourceExplicitAs": False,
                    "source": "implicit alias",
                    "target": "implicit alias",
                }
            )
        preserved.append(edited)
    return preserved


_REPEATABLE_ORDER_ALIAS_NODES = (
    exp.Add,
    exp.Column,
    exp.Grouping,
    exp.Identifier,
    exp.Literal,
    exp.Paren,
    exp.Sub,
)


def _nearest_select(expression: exp.Expression) -> exp.Select | None:
    ancestor = expression.parent
    while ancestor is not None:
        if isinstance(ancestor, exp.Select):
            return ancestor
        ancestor = ancestor.parent
    return None


def _repeatable_order_alias_expression(expression: exp.Expression) -> bool:
    """Whether duplicating an output expression in ORDER BY is conservative.

    The TPC-DS ``ansi.tpl`` profile uses a same-level output alias inside a
    CASE sort key. PostgreSQL and T-SQL reject that scope, while Calcite expands
    the alias. Keep this bridge deliberately narrower than general alias
    substitution: the admitted tree is pure GROUPING arithmetic over columns
    and literals, so expansion cannot duplicate a volatile call, subquery,
    window, aggregate finalization, or new runtime-error path.
    """

    return all(
        isinstance(node, _REPEATABLE_ORDER_ALIAS_NODES) for node in expression.walk()
    )


def expand_postgres_order_alias_expressions(
    generated_statements: list[str],
    *,
    identify: bool,
    pretty: bool,
    normalizations: list[dict],
) -> list[str]:
    """Expand non-standalone ORDER BY alias references for PostgreSQL.

    PostgreSQL permits ``ORDER BY output_alias`` but not an output alias nested
    in an expression such as ``ORDER BY CASE WHEN output_alias = 0 ...``.
    Calcite accepts the TPC-DS generator form by substituting the aliased
    expression. Reproduce exactly that substitution for the closed,
    repeatable expression subset above.
    """

    writer = Dialect.get_or_raise(CalcitePostgres)
    rewritten = []
    for statement_index, generated_sql in enumerate(generated_statements, start=1):
        try:
            statement = sqlglot.parse_one(generated_sql, read="postgres")
        except Exception as exc:
            raise OrderAliasNormalizationError(
                "generated_reparse_failed",
                "generated PostgreSQL statement could not be reparsed for ORDER BY alias expansion",
                statement=statement_index,
                parserErrorType=type(exc).__name__,
                parserError=str(exc),
            ) from exc

        statement_changed = False
        for select_index, select in enumerate(statement.find_all(exp.Select), start=1):
            aliases: dict[str, exp.Expression] = {}
            duplicate_aliases: set[str] = set()
            for projection in select.expressions:
                if not isinstance(projection, exp.Alias):
                    continue
                identifier = projection.args.get("alias")
                if not isinstance(identifier, exp.Identifier):
                    continue
                alias_name = _postgres_identifier_name(identifier)
                if alias_name in aliases:
                    duplicate_aliases.add(alias_name)
                aliases[alias_name] = projection.this

            order = select.args.get("order")
            if not isinstance(order, exp.Order):
                continue
            for order_index, ordered in enumerate(order.expressions, start=1):
                order_expression = ordered.this
                if not isinstance(order_expression, exp.Expression):
                    continue
                # A standalone output alias is legal PostgreSQL and must remain
                # an alias reference rather than duplicate its computation.
                if (
                    isinstance(order_expression, exp.Column)
                    and not order_expression.table
                ):
                    continue

                before = order_expression.sql(dialect="postgres")
                expanded_aliases = []
                for column in list(order_expression.find_all(exp.Column)):
                    if column.table or _nearest_select(column) is not select:
                        continue
                    identifier = column.this
                    if not isinstance(identifier, exp.Identifier):
                        continue
                    alias_name = _postgres_identifier_name(identifier)
                    alias_expression = aliases.get(alias_name)
                    if alias_expression is None:
                        continue
                    if alias_name in duplicate_aliases:
                        raise OrderAliasNormalizationError(
                            "ambiguous_output_alias",
                            "ORDER BY expression refers to a duplicate output alias",
                            statement=statement_index,
                            select=select_index,
                            orderItem=order_index,
                            alias=alias_name,
                        )
                    if not _repeatable_order_alias_expression(alias_expression):
                        raise OrderAliasNormalizationError(
                            "order_alias_expression_not_repeatable",
                            "ORDER BY alias expansion would duplicate an expression outside the admitted deterministic subset",
                            statement=statement_index,
                            select=select_index,
                            orderItem=order_index,
                            alias=alias_name,
                            aliasExpression=alias_expression.sql(dialect="postgres"),
                        )
                    column.replace(exp.Paren(this=alias_expression.copy()))
                    expanded_aliases.append(alias_name)

                if expanded_aliases:
                    statement_changed = True
                    normalizations.append(
                        {
                            "kind": "postgres_order_alias_expression",
                            "statement": statement_index,
                            "select": select_index,
                            "orderItem": order_index,
                            "aliases": expanded_aliases,
                            "source": before,
                            "target": order_expression.sql(dialect="postgres"),
                        }
                    )

        if statement_changed:
            generated_sql = writer.generate(
                statement,
                copy=False,
                identify=identify,
                pretty=pretty,
            )
        rewritten.append(generated_sql)
    return rewritten


def normalize_sql(
    sql: str,
    read: str,
    write: str,
    identify: bool,
    pretty: bool,
    apply_patches: bool,
) -> tuple[str, dict]:
    normalizations: list[dict] = []
    patched = sql

    report = {
        "readDialect": read,
        "writeDialect": write,
        "identify": identify,
        "pretty": pretty,
        "sqlglotVersion": sqlglot.__version__,
        "normalizations": normalizations,
        "errors": [],
    }

    try:
        if apply_patches:
            type_error = inspect_source_type_semantics(patched, read)
            if type_error is not None:
                report["errors"].append(type_error)
                return "", report
        write_dialect = (
            CalcitePostgres
            if apply_patches and write.lower() == "postgres"
            else write
        )
        if (
            read.lower() == "postgres"
            and write.lower() == "postgres"
            and identify
        ):
            statements = transpile_with_postgres_identifier_folding(
                patched,
                read=read,
                write_dialect=write_dialect,
                pretty=pretty,
                normalizations=normalizations,
            )
        else:
            statements = sqlglot.transpile(
                patched,
                read=read,
                write=write_dialect,
                identify=identify,
                pretty=pretty,
            )
    except IdentifierFoldingError as exc:
        report["errors"].append(exc.report_entry())
        return "", report
    except Exception as exc:
        report["errors"].append(
            {
                "stage": "sqlglot.transpile",
                "type": type(exc).__name__,
                "message": str(exc),
            }
        )
        return "", report

    effective_statements = [stmt.strip() for stmt in statements if is_effective_statement(stmt)]
    if apply_patches and read.lower() == "tsql" and write.lower() == "postgres":
        try:
            effective_statements = expand_postgres_order_alias_expressions(
                effective_statements,
                identify=identify,
                pretty=pretty,
                normalizations=normalizations,
            )
        except OrderAliasNormalizationError as exc:
            report["errors"].append(exc.report_entry())
            return "", report
    if read.lower() == "postgres" and write.lower() == "postgres":
        try:
            effective_statements = preserve_postgres_implicit_alias_style(
                patched,
                effective_statements,
                identify,
                normalizations,
            )
        except AliasStyleNormalizationError as exc:
            report["errors"].append(exc.report_entry())
            return "", report
    normalized = ";\n\n".join(effective_statements)
    if normalized:
        normalized += ";\n"

    if apply_patches:
        if write.lower() == "postgres":
            type_error = inspect_calcite_postgres_types(
                effective_statements, normalizations
            )
            if type_error is not None:
                report["errors"].append(type_error)
                return "", report
        normalized = patch_calcite_interval_literals(normalized, normalizations)

    report["statementCount"] = len(effective_statements)
    return normalized, report


def is_effective_statement(statement: str) -> bool:
    stripped = statement.strip()
    if not stripped:
        return False
    without_block_comments = re.sub(r"(?s)/\*.*?\*/", "", stripped).strip()
    without_line_comments = re.sub(r"(?m)^\s*--.*$", "", without_block_comments).strip()
    return bool(without_line_comments)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Normalize vendor SQL dialects into Calcite-friendly SQL with SQLGlot."
    )
    parser.add_argument("--input", required=True, help="Input SQL file.")
    parser.add_argument("--output", required=True, help="Output normalized SQL file.")
    parser.add_argument("--report", help="Optional JSON normalization report.")
    parser.add_argument("--read", default="tsql", help="Input SQLGlot dialect.")
    parser.add_argument("--write", default="postgres", help="Output SQLGlot dialect.")
    parser.add_argument(
        "--identify",
        action="store_true",
        help="Quote identifiers in the output to avoid reserved-word collisions.",
    )
    parser.add_argument("--pretty", action="store_true", help="Pretty-print output SQL.")
    parser.add_argument(
        "--no-patches",
        action="store_true",
        help="Disable Logos' small Calcite-compatibility patches.",
    )
    args = parser.parse_args()

    sql = Path(args.input).read_text()
    normalized, report = normalize_sql(
        sql=sql,
        read=args.read,
        write=args.write,
        identify=args.identify,
        pretty=args.pretty,
        apply_patches=not args.no_patches,
    )

    if report["errors"]:
        if args.report:
            Path(args.report).write_text(json.dumps(report, indent=2))
        print(json.dumps(report, indent=2), file=sys.stderr)
        return 1

    Path(args.output).write_text(normalized)
    if args.report:
        Path(args.report).write_text(json.dumps(report, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
