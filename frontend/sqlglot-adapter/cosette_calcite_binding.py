#!/usr/bin/env python3
"""Attest the closed non-semantic SQL spelling differences admitted by Cosette.

Input is a JSON object on stdin with ``embeddedSql`` and ``sourceSql``.  The
caller has already removed identifier quotes and applied any authoritative
alpha-renaming.  We accept only optional alias ``AS`` markers and ASCII case
differences in now-unquoted identifiers/keywords.  PostgreSQL parsing plus the
closed token comparison deliberately rejects literal, identifier, operator,
projection, predicate, and relation changes.
"""

from __future__ import annotations

import hashlib
import json
import sys
from typing import Any

import sqlglot
from sqlglot.dialects.postgres import Postgres
from sqlglot.tokens import TokenType

import normalize as sql_normalizer


def sha256_json(value: Any) -> str:
    return hashlib.sha256(
        json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()


def parse_one_statement(sql: str):
    statements = sqlglot.parse(sql, read="postgres")
    if len(statements) != 1:
        raise ValueError("binding input must contain exactly one PostgreSQL statement")
    return statements[0]


_LITERAL_TOKEN_TYPES = {
    TokenType.BIT_STRING,
    TokenType.BYTE_STRING,
    TokenType.HEREDOC_STRING,
    TokenType.HEX_STRING,
    TokenType.NATIONAL_STRING,
    TokenType.NUMBER,
    TokenType.RAW_STRING,
    TokenType.STRING,
    TokenType.UNICODE_STRING,
}


def canonical_token_text(token_type: TokenType, token_text: str) -> str:
    if (
        token_type not in _LITERAL_TOKEN_TYPES
        and token_text
        and token_text.isascii()
        and token_text.replace("_", "a").isalnum()
        and not token_text[0].isdigit()
    ):
        return token_text.casefold()
    return token_text


def token_inventory(
    sql: str,
) -> tuple[list[tuple[str, str]], list[tuple[str, str]], int]:
    tokens = Postgres.Tokenizer().tokenize(sql)
    aliases = sum(token.token_type == TokenType.ALIAS for token in tokens)
    raw_inventory = [
        (token.token_type.name, token.text)
        for token in tokens
        if token.token_type != TokenType.ALIAS
    ]
    canonical_inventory = [
        (
            token.token_type.name,
            canonical_token_text(token.token_type, token.text),
        )
        for token in tokens
        if token.token_type != TokenType.ALIAS
    ]
    return raw_inventory, canonical_inventory, aliases


def attest_optional_alias_style(embedded_sql: str, source_sql: str) -> dict[str, Any]:
    try:
        embedded_ast = parse_one_statement(embedded_sql)
        source_ast = parse_one_statement(source_sql)
    except (ValueError, sqlglot.errors.ParseError) as error:
        return {"status": "rejected", "reason": str(error)}
    embedded_canonical_ast = embedded_ast.sql(
        dialect="postgres", normalize=True, normalize_functions="lower"
    )
    source_canonical_ast = source_ast.sql(
        dialect="postgres", normalize=True, normalize_functions="lower"
    )
    if embedded_canonical_ast != source_canonical_ast:
        return {"status": "rejected", "reason": "PostgreSQL ASTs differ"}

    embedded_raw, embedded_tokens, embedded_aliases = token_inventory(embedded_sql)
    source_raw, source_tokens, source_aliases = token_inventory(source_sql)
    if embedded_tokens != source_tokens:
        return {
            "status": "rejected",
            "reason": "canonical non-AS PostgreSQL token streams differ",
        }
    case_folded = sum(
        left_type == right_type and left_text != right_text
        for (left_type, left_text), (right_type, right_text) in zip(
            embedded_raw, source_raw
        )
    )
    alias_style_differs = embedded_aliases != source_aliases
    if not alias_style_differs and case_folded == 0:
        return {
            "status": "rejected",
            "reason": "no admitted SQL spelling difference was observed",
        }
    fingerprint = sha256_json(embedded_tokens)
    if alias_style_differs and case_folded:
        status = "verified-unquoted-case-and-optional-alias-style"
    elif alias_style_differs:
        status = "verified-optional-alias-as-style"
    else:
        status = "verified-unquoted-case-style"
    return {
        "status": status,
        "policy": (
            "identical normalized PostgreSQL AST and identical ordered token "
            "stream after deleting only TokenType.ALIAS (AS) markers and "
            "ASCII-case-folding non-literal identifier/keyword tokens"
        ),
        "canonicalTokenSha256": fingerprint,
        "embeddedAliasTokenCount": embedded_aliases,
        "sourceAliasTokenCount": source_aliases,
        "caseFoldedTokenCount": case_folded,
        "nonAliasTokenCount": len(embedded_tokens),
    }


def attest_source_normalization_replay(payload: dict[str, Any]) -> dict[str, Any]:
    raw_sql = payload.get("rawSourceSql")
    generated_sql = payload.get("generatedSourceSql")
    read_dialect = payload.get("readDialect")
    write_dialect = payload.get("writeDialect")
    identify = payload.get("identify")
    pretty = payload.get("pretty")
    expected_report = payload.get("expectedReport")
    if (
        not isinstance(raw_sql, str)
        or not isinstance(generated_sql, str)
        or not isinstance(read_dialect, str)
        or not isinstance(write_dialect, str)
        or not isinstance(identify, bool)
        or not isinstance(pretty, bool)
        or not isinstance(expected_report, dict)
    ):
        return {"status": "rejected", "reason": "malformed replay request"}
    try:
        replayed_sql, actual_report = sql_normalizer.normalize_sql(
            sql=raw_sql,
            read=read_dialect,
            write=write_dialect,
            identify=identify,
            pretty=pretty,
            apply_patches=True,
        )
        replayed_ast = parse_one_statement(replayed_sql)
        generated_ast = parse_one_statement(generated_sql)
    except Exception as error:
        return {"status": "rejected", "reason": str(error)}
    if actual_report != expected_report:
        return {
            "status": "rejected",
            "reason": "SQLGlot replay report differs from source metadata",
        }
    if replayed_ast != generated_ast:
        return {
            "status": "rejected",
            "reason": "SQLGlot replay and generated source ASTs differ",
        }

    def exact_tokens(sql: str) -> list[tuple[str, str]]:
        return [
            (token.token_type.name, token.text)
            for token in Postgres.Tokenizer().tokenize(sql)
            if token.token_type != TokenType.SEMICOLON
        ]

    replayed_tokens = exact_tokens(replayed_sql)
    generated_tokens = exact_tokens(generated_sql)
    if replayed_tokens != generated_tokens:
        return {
            "status": "rejected",
            "reason": "SQLGlot replay and generated source tokens differ",
        }
    return {
        "status": "verified-sqlglot-source-normalization-replay",
        "policy": (
            "exact configured SQLGlot report and PostgreSQL token stream, "
            "ignoring only comments/layout and one trailing semicolon"
        ),
        "sqlglotVersion": actual_report.get("sqlglotVersion"),
        "canonicalTokenSha256": sha256_json(replayed_tokens),
        "tokenCount": len(replayed_tokens),
        "normalizationReportSha256": sha256_json(actual_report),
    }


def main() -> int:
    try:
        payload = json.load(sys.stdin)
        if not isinstance(payload, dict):
            raise ValueError("input must be a JSON object")
        if payload.get("mode") == "source-normalization-replay":
            result = attest_source_normalization_replay(payload)
        else:
            embedded_sql = payload.get("embeddedSql")
            source_sql = payload.get("sourceSql")
            if not isinstance(embedded_sql, str) or not isinstance(source_sql, str):
                raise ValueError("input must provide string embeddedSql/sourceSql fields")
            result = attest_optional_alias_style(embedded_sql, source_sql)
    except (ValueError, json.JSONDecodeError) as error:
        result = {"status": "rejected", "reason": str(error)}
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
