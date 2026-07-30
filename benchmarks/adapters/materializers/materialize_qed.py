#!/usr/bin/env python3
import argparse
import hashlib
import importlib.util
from importlib.machinery import SourceFileLoader
import json
import re
import shutil
import subprocess
import sys
import tempfile
from collections import Counter
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

try:
    from materializer_sql import (
        ASCII_SQL_WHITESPACE_PATTERN,
        POSTGRES_IDENTIFIER_CONTINUATION_CLASS,
        mask_sql_regions,
        parse_schema,
        protected_sql_regions,
        split_sql_statements,
        split_top_level_commas,
        strip_sql_comments,
        substitute_unprotected,
    )
except ModuleNotFoundError:  # Imported as benchmarks.adapters.materializers.*
    from .materializer_sql import (
        ASCII_SQL_WHITESPACE_PATTERN,
        POSTGRES_IDENTIFIER_CONTINUATION_CLASS,
        mask_sql_regions,
        parse_schema,
        protected_sql_regions,
        split_sql_statements,
        split_top_level_commas,
        strip_sql_comments,
        substitute_unprotected,
    )

try:
    from solver_frontend import (
        SolverFrontendConfigurationError,
        solver_materialization_config,
    )
except ModuleNotFoundError:  # Imported as benchmarks.adapters.materializers.*
    from .solver_frontend import (
        SolverFrontendConfigurationError,
        solver_materialization_config,
    )


ROOT = Path(__file__).resolve().parents[3]
EXPORTER_PATH = ROOT / "scripts/export-benchmark-ir"
DEFAULT_CONFIG = "benchmarks/core/ingestion.json"
DEFAULT_OUTPUT = "benchmarks/core/.generated/qed"
_QED_INTERVAL_PRECISION = re.compile(
    rf"(?<![{POSTGRES_IDENTIFIER_CONTINUATION_CLASS}.])"
    rf"INTERVAL{ASCII_SQL_WHITESPACE_PATTERN}+'([0-9]{{3,}})'"
    rf"{ASCII_SQL_WHITESPACE_PATTERN}+DAY"
    rf"(?![{POSTGRES_IDENTIFIER_CONTINUATION_CLASS}.])"
    rf"(?!{ASCII_SQL_WHITESPACE_PATTERN}*\()",
    flags=re.IGNORECASE | re.ASCII,
)
_QED_TSQL_DATE_DAY_SOURCE = re.compile(
    r"(?is)(?P<predicate_prefix>\bBETWEEN\s+CAST\s*\(\s*"
    r"(?P<lower_literal>'(?:''|[^'])*')\s+AS\s+DATE\s*\)\s+AND\s*)"
    r"(?P<upper_prefix>\(\s*CAST\s*\(\s*"
    r"(?P<upper_literal>'(?:''|[^'])*')\s+AS\s+DATE\s*\)\s*\+\s*)"
    r"(?P<days>[0-9]+)"
    r"(?P<unit>\s+days\b)?"
    r"(?P<suffix>\s*\))"
)
_QED_TSQL_DATE_DAY_NORMALIZED = re.compile(
    r"(?is)(?P<predicate_prefix>\bBETWEEN\s+CAST\s*\(\s*"
    r"(?P<lower_literal>'(?:''|[^'])*')\s+AS\s+DATE\s*\)\s+AND\s*)"
    r"(?P<upper_prefix>\(\s*CAST\s*\(\s*"
    r"(?P<upper_literal>'(?:''|[^'])*')\s+AS\s+DATE\s*\)\s*\+\s*)"
    r"(?P<days>[0-9]+)"
    r"(?P<alias>\s+AS\s+\"days\")?"
    r"(?P<suffix>\s*\))"
)
_RAW_COLUMN_CONSTRAINT = re.compile(
    r"(?is)\b(?:NOT\s+NULL|NULL|PRIMARY\s+KEY|UNIQUE|REFERENCES|CHECK|"
    r"DEFAULT|COLLATE|CONSTRAINT|GENERATED|IDENTITY)\b"
)
_RAW_CREATE_TABLE = re.compile(
    rf"(?<![{POSTGRES_IDENTIFIER_CONTINUATION_CLASS}.])"
    rf"CREATE{ASCII_SQL_WHITESPACE_PATTERN}+TABLE"
    rf"(?![{POSTGRES_IDENTIFIER_CONTINUATION_CLASS}.])",
    flags=re.IGNORECASE | re.DOTALL | re.ASCII,
)
_CANONICAL_SOURCE_SCHEMA_AUTHORITY_CACHE: dict[
    tuple[str, str, str], dict[str, dict[str, Any]]
] = {}
_QED_BASE_ALIAS_QUERY_POLICY = "qed-base-table-column-alias-order-v1"
_QED_PARSER_PREFLIGHT_POLICY = "qed-parser-planner-v1"


@dataclass
class Column:
    name: str
    type_sql: str
    not_null: bool


@dataclass
class Table:
    name: str
    columns: list[Column] = field(default_factory=list)
    primary_keys: list[tuple[str, ...]] = field(default_factory=list)
    unique_keys: list[tuple[str, ...]] = field(default_factory=list)
    applied_constraints: list[dict[str, Any]] = field(default_factory=list)
    omitted_constraints: list[dict[str, Any]] = field(default_factory=list)


class QedJsonRepairError(RuntimeError):
    """The parser JSON cannot be aligned with the attested QED schema."""


class QedJsonValidationError(RuntimeError):
    """The parser did not emit one complete, comparable QED query pair."""


@dataclass(frozen=True)
class _QedSqlToken:
    """One offset-preserving token used by the QED alias-order attestation."""

    kind: str
    text: str
    value: str | None
    start: int
    end: int
    depth: int
    quoted: bool = False


def _qed_alias_order_report(
    status: str,
    *,
    transformations: list[dict[str, Any]] | None = None,
    star_expansions: list[dict[str, Any]] | None = None,
    reason: str | None = None,
    evidence: dict[str, Any] | None = None,
) -> dict[str, Any]:
    report: dict[str, Any] = {
        "version": 1,
        "kind": "qed-base-table-column-alias-order",
        "status": status,
        "frontendColumnOrder": "case-sensitive-ASCII-lexicographic",
        "transformations": transformations or [],
        "starExpansions": star_expansions or [],
        "semanticContract": (
            "QED's QedTable sorts base columns lexicographically before Calcite "
            "binds a positional table column-alias list. For an exact full base-table "
            "list, emit the alias associated with each source DDL column at that "
            "column's QED-sorted position. This preserves the source-column-to-alias "
            "binding and leaves every query reference unchanged. Queries that can "
            "observe the base row's physical field order through a qualified star "
            "or whole-row alias reference are rejected. When either query side "
            "activates this boundary, an unqualified SELECT-list star is expanded "
            "on both sides only when its complete FROM/JOIN row consists of direct, "
            "schema-attested base relations; expansion uses FROM/JOIN order and "
            "source-column order. Derived, NATURAL, USING, malformed, or ambiguous "
            "star scopes fail closed when they contain an alias-list candidate."
        ),
        "rowOrderObservationPolicy": (
            "reject qualified alias stars and whole-row uses of a reordered "
            "base-table alias; pairwise-expand only fully attested direct-base "
            "unqualified stars in source row order"
        ),
    }
    if reason is not None:
        report["reason"] = reason
    if evidence is not None:
        report["evidence"] = evidence
    return report


def _lex_qed_alias_sql(sql: str) -> tuple[list[_QedSqlToken], list[Any]]:
    """Tokenize enough SQL to attest direct base-table alias-list positions."""

    regions = protected_sql_regions(sql)
    by_start = {region.start: region for region in regions}
    tokens: list[_QedSqlToken] = []
    depth = 0
    index = 0
    while index < len(sql):
        region = by_start.get(index)
        if region is not None:
            text = sql[region.start : region.end]
            if region.kind in {"double_quote", "backtick_quote"} and region.terminated:
                delimiter = region.delimiter
                value = text[1:-1].replace(delimiter * 2, delimiter)
                tokens.append(
                    _QedSqlToken(
                        "identifier",
                        text,
                        value,
                        region.start,
                        region.end,
                        depth,
                        quoted=True,
                    )
                )
            elif region.kind != "comment":
                tokens.append(
                    _QedSqlToken(
                        "literal",
                        text,
                        None,
                        region.start,
                        region.end,
                        depth,
                    )
                )
            index = region.end
            continue

        char = sql[index]
        if char in " \t\n\r\f\v":
            index += 1
            continue
        if char == "(":
            tokens.append(_QedSqlToken("open", char, None, index, index + 1, depth))
            depth += 1
            index += 1
            continue
        if char == ")":
            depth = max(0, depth - 1)
            tokens.append(_QedSqlToken("close", char, None, index, index + 1, depth))
            index += 1
            continue
        if char == ",":
            tokens.append(_QedSqlToken("comma", char, None, index, index + 1, depth))
            index += 1
            continue
        if char == ".":
            tokens.append(_QedSqlToken("dot", char, None, index, index + 1, depth))
            index += 1
            continue
        if char == "_" or char.isalpha() or ord(char) >= 128:
            end = index + 1
            while end < len(sql):
                next_char = sql[end]
                if not (
                    next_char == "_"
                    or next_char == "$"
                    or next_char.isalnum()
                    or ord(next_char) >= 128
                ):
                    break
                end += 1
            text = sql[index:end]
            tokens.append(
                _QedSqlToken("identifier", text, text, index, end, depth, quoted=False)
            )
            index = end
            continue
        if char.isdigit():
            end = index + 1
            while end < len(sql) and (sql[end].isalnum() or sql[end] in "._"):
                end += 1
            tokens.append(
                _QedSqlToken("number", sql[index:end], None, index, end, depth)
            )
            index = end
            continue
        tokens.append(_QedSqlToken("symbol", char, None, index, index + 1, depth))
        index += 1
    return tokens, regions


def _qed_matching_token_parens(tokens: list[_QedSqlToken]) -> dict[int, int]:
    matches: dict[int, int] = {}
    stack: list[int] = []
    for index, token in enumerate(tokens):
        if token.kind == "open":
            stack.append(index)
        elif token.kind == "close" and stack:
            open_index = stack.pop()
            matches[open_index] = index
    return matches


_QED_FROM_BOUNDARIES = frozenset(
    {
        "SELECT",
        "FROM",
        "JOIN",
        "ON",
        "WHERE",
        "GROUP",
        "HAVING",
        "ORDER",
        "LIMIT",
        "OFFSET",
        "FETCH",
        "UNION",
        "INTERSECT",
        "EXCEPT",
        "RETURNING",
    }
)


def _qed_word(token: _QedSqlToken) -> str | None:
    if token.kind != "identifier" or token.quoted or token.value is None:
        return None
    return token.value.upper()


def _qed_table_factor_start(tokens: list[_QedSqlToken], index: int) -> bool:
    if index <= 0:
        return False
    token = tokens[index]
    previous = tokens[index - 1]
    previous_word = _qed_word(previous)
    if previous.depth == token.depth and previous_word in {"FROM", "JOIN"}:
        return True
    if previous.kind != "comma" or previous.depth != token.depth:
        return False
    for cursor in range(index - 2, -1, -1):
        candidate = tokens[cursor]
        if candidate.depth < token.depth:
            return False
        if candidate.depth != token.depth:
            continue
        word = _qed_word(candidate)
        if word in _QED_FROM_BOUNDARIES:
            return word in {"FROM", "JOIN"}
    return False


def _qed_alias_list_tokens(
    tokens: list[_QedSqlToken], open_index: int, close_index: int
) -> list[_QedSqlToken] | None:
    expected_identifier = True
    aliases: list[_QedSqlToken] = []
    for token in tokens[open_index + 1 : close_index]:
        if token.depth != tokens[open_index].depth + 1:
            return None
        if expected_identifier:
            if token.kind != "identifier" or token.value is None:
                return None
            aliases.append(token)
        elif token.kind != "comma":
            return None
        expected_identifier = not expected_identifier
    if expected_identifier or not aliases:
        return None
    return aliases


def _qed_alias_row_observation_problem(
    tokens: list[_QedSqlToken], candidate: dict[str, Any]
) -> dict[str, Any] | None:
    """Reject uses that observe a base row rather than a named base column."""

    alias_token = candidate["aliasToken"]
    alias = alias_token.value
    if not isinstance(alias, str):
        return {
            "reason": "base-table-alias-is-malformed",
            "evidence": {"table": candidate["tableToken"].value},
        }
    for index, token in enumerate(tokens):
        if (
            token.kind != "identifier"
            or token.value is None
            or token.value.casefold() != alias.casefold()
            or token.start == alias_token.start
        ):
            continue
        if (
            index + 2 < len(tokens)
            and tokens[index + 1].kind == "dot"
            and tokens[index + 1].depth == token.depth
            and tokens[index + 2].depth == token.depth
        ):
            selected = tokens[index + 2]
            if selected.kind == "identifier":
                continue
            if selected.kind == "symbol" and selected.text == "*":
                return {
                    "reason": "qualified-base-table-alias-star-observes-row-order",
                    "evidence": {
                        "table": candidate["tableToken"].value,
                        "alias": alias,
                        "offset": token.start,
                    },
                }
        return {
            "reason": "whole-row-or-shadowed-base-table-alias-use-is-ambiguous",
            "evidence": {
                "table": candidate["tableToken"].value,
                "alias": alias,
                "offset": token.start,
            },
        }
    return None


def _qed_cte_names(
    tokens: list[_QedSqlToken], parens: dict[int, int]
) -> tuple[set[str], bool]:
    """Collect visible CTE names conservatively; false means WITH was ambiguous."""

    names: set[str] = set()
    complete = True
    for with_index, token in enumerate(tokens):
        if _qed_word(token) != "WITH":
            continue
        depth = token.depth
        cursor = with_index + 1
        if cursor < len(tokens) and _qed_word(tokens[cursor]) == "RECURSIVE":
            cursor += 1
        while cursor < len(tokens):
            name = tokens[cursor]
            if name.depth != depth or name.kind != "identifier" or name.value is None:
                complete = False
                break
            names.add(name.value.casefold())
            cursor += 1
            if (
                cursor < len(tokens)
                and tokens[cursor].kind == "open"
                and tokens[cursor].depth == depth
            ):
                close = parens.get(cursor)
                if (
                    close is None
                    or _qed_alias_list_tokens(tokens, cursor, close) is None
                ):
                    complete = False
                    break
                cursor = close + 1
            if cursor >= len(tokens) or _qed_word(tokens[cursor]) != "AS":
                complete = False
                break
            cursor += 1
            if cursor < len(tokens) and _qed_word(tokens[cursor]) in {
                "MATERIALIZED",
                "NOT",
            }:
                complete = False
                break
            if cursor >= len(tokens) or tokens[cursor].kind != "open":
                complete = False
                break
            close = parens.get(cursor)
            if close is None:
                complete = False
                break
            cursor = close + 1
            if (
                cursor < len(tokens)
                and tokens[cursor].kind == "comma"
                and tokens[cursor].depth == depth
            ):
                cursor += 1
                continue
            break
    return names, complete


def _qed_nearest_select_index(tokens: list[_QedSqlToken], index: int) -> int | None:
    depth = tokens[index].depth
    for cursor in range(index - 1, -1, -1):
        token = tokens[cursor]
        if token.depth < depth:
            return None
        if token.depth == depth and _qed_word(token) == "SELECT":
            return cursor
    return None


def _qed_select_from_extent(
    tokens: list[_QedSqlToken], select_index: int
) -> tuple[int | None, int]:
    depth = tokens[select_index].depth
    from_index: int | None = None
    end_index = len(tokens)
    for cursor in range(select_index + 1, len(tokens)):
        token = tokens[cursor]
        if token.depth < depth:
            end_index = cursor
            break
        if token.depth != depth:
            continue
        word = _qed_word(token)
        if from_index is None:
            if word == "FROM":
                from_index = cursor
            elif word in {"UNION", "INTERSECT", "EXCEPT"}:
                end_index = cursor
                break
        elif word in {
            "WHERE",
            "GROUP",
            "HAVING",
            "ORDER",
            "LIMIT",
            "OFFSET",
            "FETCH",
            "UNION",
            "INTERSECT",
            "EXCEPT",
            "RETURNING",
        }:
            end_index = cursor
            break
    return from_index, end_index


def _qed_unqualified_select_stars(
    tokens: list[_QedSqlToken], select_index: int, from_index: int
) -> list[int]:
    depth = tokens[select_index].depth
    stars: list[int] = []
    for index in range(select_index + 1, from_index):
        token = tokens[index]
        if token.depth != depth or token.kind != "symbol" or token.text != "*":
            continue
        previous = tokens[index - 1] if index > select_index else None
        following = tokens[index + 1] if index + 1 < len(tokens) else None
        if (
            following is not None
            and following.depth == depth
            and (following.kind == "comma" or _qed_word(following) == "FROM")
            and not (
                previous is not None
                and previous.depth == depth
                and previous.kind == "dot"
            )
        ):
            stars.append(index)
    return stars


_QED_BARE_FACTOR_ALIAS_BOUNDARIES = _QED_FROM_BOUNDARIES | frozenset(
    {
        "AS",
        "INNER",
        "LEFT",
        "RIGHT",
        "FULL",
        "CROSS",
        "NATURAL",
        "OUTER",
        "LATERAL",
        "ONLY",
        "USING",
    }
)


def _qed_star_base_factor(
    tokens: list[_QedSqlToken],
    start: int,
    tables: dict[str, dict[str, Any]],
    candidates_by_table_offset: dict[int, dict[str, Any]],
    cte_names: set[str],
) -> tuple[dict[str, Any] | None, str | None]:
    while start < len(tokens) and _qed_word(tokens[start]) in {"LATERAL", "ONLY"}:
        start += 1
    if start >= len(tokens) or tokens[start].kind != "identifier":
        return None, "star-from-factor-is-not-a-direct-base-table"
    table_token = tokens[start]
    if table_token.value is None:
        return None, "star-from-base-table-name-is-malformed"
    cursor = start
    identifiers = [table_token]
    while (
        cursor + 2 < len(tokens)
        and tokens[cursor + 1].kind == "dot"
        and tokens[cursor + 2].kind == "identifier"
        and tokens[cursor + 2].depth == table_token.depth
    ):
        identifiers.append(tokens[cursor + 2])
        cursor += 2
    if len(identifiers) != 1:
        return None, "star-from-base-table-is-schema-qualified"
    if table_token.value.casefold() in cte_names:
        return None, "star-from-base-table-is-shadowed-by-cte"
    table = tables.get(table_token.value.casefold())
    if table is None:
        return None, "star-from-factor-is-not-an-attested-base-table"
    if cursor + 1 < len(tokens) and tokens[cursor + 1].kind == "open":
        return None, "star-from-factor-can-be-a-table-function"

    alias_token = table_token
    next_index = cursor + 1
    if next_index < len(tokens) and _qed_word(tokens[next_index]) == "AS":
        if next_index + 1 >= len(tokens):
            return None, "star-from-base-table-alias-is-missing"
        possible_alias = tokens[next_index + 1]
        if possible_alias.kind != "identifier" or possible_alias.value is None:
            return None, "star-from-base-table-alias-is-malformed"
        alias_token = possible_alias
        next_index += 2
    elif next_index < len(tokens):
        possible_alias = tokens[next_index]
        if (
            possible_alias.kind == "identifier"
            and possible_alias.value is not None
            and _qed_word(possible_alias) not in _QED_BARE_FACTOR_ALIAS_BOUNDARIES
        ):
            alias_token = possible_alias
            next_index += 1

    candidate = candidates_by_table_offset.get(table_token.start)
    if candidate is not None:
        aliases = candidate["aliases"]
        if alias_token.start != candidate["aliasToken"].start:
            return None, "star-from-alias-list-binding-is-inconsistent"
        output_fields = [
            {
                "name": alias.value,
                "sql": f"{alias_token.text}.{alias.text}",
            }
            for alias in aliases
        ]
    else:
        if next_index < len(tokens) and tokens[next_index].kind == "open":
            return None, "star-from-base-table-has-unattested-column-alias-list"
        raw_columns = table.get("columns")
        if not isinstance(raw_columns, list) or not all(
            isinstance(column, dict) and isinstance(column.get("name"), str)
            for column in raw_columns
        ):
            return None, "star-from-base-table-column-order-is-malformed"
        output_fields = [
            {
                "name": column["name"],
                "sql": f"{alias_token.text}.{quote_identifier(column['name'])}",
            }
            for column in raw_columns
        ]
    return (
        {
            "table": table_token.value,
            "alias": alias_token.value,
            "tableOffset": table_token.start,
            "outputFields": output_fields,
        },
        None,
    )


def _qed_attest_unqualified_star_expansions(
    sql: str,
    tokens: list[_QedSqlToken],
    tables: dict[str, dict[str, Any]],
    candidates: list[dict[str, Any]],
    cte_names: set[str],
    expand_all_attested_stars: bool,
) -> tuple[list[tuple[int, int, str]], list[dict[str, Any]], dict[str, Any] | None]:
    """Expand only stars whose complete direct base row is schema-attested."""

    candidates_by_select: dict[int, list[dict[str, Any]]] = {}
    candidates_by_table_offset = {
        candidate["tableToken"].start: candidate for candidate in candidates
    }
    for candidate in candidates:
        select_index = _qed_nearest_select_index(
            tokens, tokens.index(candidate["tableToken"])
        )
        if select_index is not None:
            candidates_by_select.setdefault(select_index, []).append(candidate)

    select_indices = set(candidates_by_select)
    if expand_all_attested_stars:
        select_indices.update(
            index for index, token in enumerate(tokens) if _qed_word(token) == "SELECT"
        )

    replacements: list[tuple[int, int, str]] = []
    reports: list[dict[str, Any]] = []
    for select_index in sorted(select_indices):
        scope_candidates = candidates_by_select.get(select_index, [])
        from_index, end_index = _qed_select_from_extent(tokens, select_index)
        if from_index is None:
            if not scope_candidates:
                continue
            return (
                [],
                [],
                {
                    "reason": "alias-list-select-scope-has-no-from-clause",
                    "evidence": {"offset": tokens[select_index].start},
                },
            )
        stars = _qed_unqualified_select_stars(tokens, select_index, from_index)
        if not stars:
            continue
        depth = tokens[select_index].depth
        if any(
            token.depth == depth and _qed_word(token) in {"NATURAL", "USING"}
            for token in tokens[from_index + 1 : end_index]
        ):
            if not scope_candidates:
                continue
            return (
                [],
                [],
                {
                    "reason": "unqualified-star-natural-or-using-row-order-is-unsupported",
                    "evidence": {"offset": tokens[stars[0]].start},
                },
            )
        factor_starts = [from_index + 1]
        factor_starts.extend(
            index + 1
            for index in range(from_index + 1, end_index)
            if tokens[index].depth == depth
            and (tokens[index].kind == "comma" or _qed_word(tokens[index]) == "JOIN")
        )
        factors: list[dict[str, Any]] = []
        for start in factor_starts:
            factor, reason = _qed_star_base_factor(
                tokens,
                start,
                tables,
                candidates_by_table_offset,
                cte_names,
            )
            if factor is None:
                if not scope_candidates:
                    factors = []
                    break
                return (
                    [],
                    [],
                    {
                        "reason": reason,
                        "evidence": {"offset": tokens[stars[0]].start},
                    },
                )
            factors.append(factor)
        if not factors:
            continue
        factor_offsets = {factor["tableOffset"] for factor in factors}
        if any(
            candidate["tableToken"].start not in factor_offsets
            for candidate in scope_candidates
        ):
            return (
                [],
                [],
                {
                    "reason": "unqualified-star-base-factor-coverage-is-incomplete",
                    "evidence": {"offset": tokens[stars[0]].start},
                },
            )
        output_fields = [
            field for factor in factors for field in factor["outputFields"]
        ]
        if not output_fields:
            return (
                [],
                [],
                {
                    "reason": "unqualified-star-base-row-is-empty",
                    "evidence": {"offset": tokens[stars[0]].start},
                },
            )
        replacement = ", ".join(field["sql"] for field in output_fields)
        for star_index in stars:
            star = tokens[star_index]
            replacements.append((star.start, star.end, replacement))
            reports.append(
                {
                    "line": sql.count("\n", 0, star.start) + 1,
                    "sourceSpan": {"start": star.start, "end": star.end},
                    "sourceText": star.text,
                    "relationOrder": [
                        {"table": factor["table"], "alias": factor["alias"]}
                        for factor in factors
                    ],
                    "outputFieldOrder": [field["name"] for field in output_fields],
                    "replacementSql": replacement,
                    "semanticContract": (
                        "replace one unqualified SELECT-list star over only direct, "
                        "schema-attested base relations with the same qualified "
                        "fields in FROM/JOIN and source-column order"
                    ),
                }
            )
    return replacements, reports, None


def normalize_qed_base_table_column_alias_lists(
    sql: str,
    source_schema_type_authority: dict[str, Any],
    *,
    expand_all_attested_stars: bool = False,
) -> tuple[str, dict[str, Any]]:
    """Compensate only QED's attested base-column sorting before alias binding.

    SQL table column aliases are positional in source DDL order. QED constructs
    ``QedTable`` with the same columns sorted by name, so Calcite otherwise binds a
    generated full alias list to the wrong base columns. The rewrite is admitted only
    for an exact full base-table list and changes no identifier spelling or reference.
    """

    if source_schema_type_authority.get("status") != (
        "verified-ordered-raw-source-schema-types"
    ):
        return sql, _qed_alias_order_report(
            "unsupported", reason="source-schema-order-is-not-attested"
        )
    raw_tables = source_schema_type_authority.get("tables")
    if not isinstance(raw_tables, list):
        return sql, _qed_alias_order_report(
            "unsupported", reason="source-schema-table-list-is-malformed"
        )

    tables: dict[str, dict[str, Any]] = {}
    for raw_table in raw_tables:
        if not isinstance(raw_table, dict) or not isinstance(
            raw_table.get("name"), str
        ):
            return sql, _qed_alias_order_report(
                "unsupported", reason="source-schema-table-is-malformed"
            )
        key = raw_table["name"].casefold()
        if key in tables:
            return sql, _qed_alias_order_report(
                "unsupported",
                reason="source-schema-table-name-is-ambiguous",
                evidence={"table": raw_table["name"]},
            )
        tables[key] = raw_table

    tokens, regions = _lex_qed_alias_sql(sql)
    parens = _qed_matching_token_parens(tokens)
    cte_names, cte_scan_complete = _qed_cte_names(tokens, parens)
    candidates: list[dict[str, Any]] = []

    for start, token in enumerate(tokens):
        if token.kind != "identifier" or token.value is None:
            continue
        if not _qed_table_factor_start(tokens, start):
            continue
        cursor = start
        identifiers = [token]
        while (
            cursor + 2 < len(tokens)
            and tokens[cursor + 1].kind == "dot"
            and tokens[cursor + 2].kind == "identifier"
            and tokens[cursor + 2].depth == token.depth
        ):
            identifiers.append(tokens[cursor + 2])
            cursor += 2
        table_token = identifiers[-1]
        table = tables.get((table_token.value or "").casefold())
        if table is None:
            continue

        alias_token: _QedSqlToken | None = None
        open_index: int | None = None
        next_index = cursor + 1
        if next_index < len(tokens) and _qed_word(tokens[next_index]) == "AS":
            if next_index + 2 < len(tokens):
                alias_token = tokens[next_index + 1]
                if (
                    alias_token.kind == "identifier"
                    and tokens[next_index + 2].kind == "open"
                ):
                    open_index = next_index + 2
        elif next_index + 1 < len(tokens):
            possible_alias = tokens[next_index]
            if (
                possible_alias.kind == "identifier"
                and _qed_word(possible_alias) not in _QED_FROM_BOUNDARIES
                and tokens[next_index + 1].kind == "open"
            ):
                alias_token = possible_alias
                open_index = next_index + 1
        if alias_token is None or alias_token.value is None or open_index is None:
            continue

        if len(identifiers) != 1:
            return sql, _qed_alias_order_report(
                "unsupported",
                reason="schema-qualified-base-table-alias-list-is-ambiguous",
                evidence={"tableSql": ".".join(item.text for item in identifiers)},
            )
        if not cte_scan_complete:
            return sql, _qed_alias_order_report(
                "unsupported", reason="with-scope-could-not-be-attested"
            )
        if table_token.value.casefold() in cte_names:
            return sql, _qed_alias_order_report(
                "unsupported",
                reason="base-table-name-is-shadowed-by-cte",
                evidence={"table": table_token.value},
            )
        close_index = parens.get(open_index)
        if close_index is None:
            return sql, _qed_alias_order_report(
                "unsupported",
                reason="base-table-column-alias-list-is-unterminated",
                evidence={"table": table_token.value, "alias": alias_token.value},
            )
        body_start = tokens[open_index].end
        body_end = tokens[close_index].start
        if any(
            region.kind == "comment"
            and region.start < body_end
            and region.end > body_start
            for region in regions
        ):
            return sql, _qed_alias_order_report(
                "unsupported",
                reason="base-table-column-alias-list-contains-comment",
                evidence={"table": table_token.value, "alias": alias_token.value},
            )
        aliases = _qed_alias_list_tokens(tokens, open_index, close_index)
        if aliases is None:
            return sql, _qed_alias_order_report(
                "unsupported",
                reason="base-table-column-alias-list-is-not-a-simple-identifier-list",
                evidence={"table": table_token.value, "alias": alias_token.value},
            )
        raw_columns = table.get("columns")
        if not isinstance(raw_columns, list) or not all(
            isinstance(column, dict) and isinstance(column.get("name"), str)
            for column in raw_columns
        ):
            return sql, _qed_alias_order_report(
                "unsupported",
                reason="source-schema-column-order-is-malformed",
                evidence={"table": table_token.value},
            )
        source_columns = [column["name"] for column in raw_columns]
        if any(not name.isascii() for name in source_columns):
            return sql, _qed_alias_order_report(
                "unsupported",
                reason="qed-java-column-sort-is-not-attested-for-non-ascii-name",
                evidence={"table": table_token.value},
            )
        if len({name.casefold() for name in source_columns}) != len(source_columns):
            return sql, _qed_alias_order_report(
                "unsupported",
                reason="source-schema-column-name-is-ambiguous",
                evidence={"table": table_token.value},
            )
        if len(aliases) != len(source_columns):
            return sql, _qed_alias_order_report(
                "unsupported",
                reason="base-table-column-alias-list-is-not-full",
                evidence={
                    "table": table_token.value,
                    "alias": alias_token.value,
                    "sourceColumnCount": len(source_columns),
                    "aliasCount": len(aliases),
                },
            )
        alias_values = [alias.value for alias in aliases]
        if len({str(value).casefold() for value in alias_values}) != len(alias_values):
            return sql, _qed_alias_order_report(
                "unsupported",
                reason="base-table-column-alias-list-is-not-unique",
                evidence={"table": table_token.value, "alias": alias_token.value},
            )
        candidates.append(
            {
                "tableToken": table_token,
                "aliasToken": alias_token,
                "openToken": tokens[open_index],
                "closeToken": tokens[close_index],
                "sourceColumns": source_columns,
                "aliases": aliases,
            }
        )

    duplicate_aliases = [
        alias
        for alias, count in Counter(
            candidate["aliasToken"].value.casefold() for candidate in candidates
        ).items()
        if count > 1
    ]
    if duplicate_aliases:
        return sql, _qed_alias_order_report(
            "unsupported",
            reason="base-table-alias-is-ambiguous-or-shadowed",
            evidence={"aliases": sorted(duplicate_aliases)},
        )
    if not candidates and not expand_all_attested_stars:
        return sql, _qed_alias_order_report("not-applicable")
    for candidate in candidates:
        problem = _qed_alias_row_observation_problem(tokens, candidate)
        if problem is not None:
            return sql, _qed_alias_order_report(
                "unsupported",
                reason=problem["reason"],
                evidence=problem["evidence"],
            )

    star_replacements, star_expansions, star_problem = (
        _qed_attest_unqualified_star_expansions(
            sql,
            tokens,
            tables,
            candidates,
            cte_names,
            expand_all_attested_stars,
        )
    )
    if star_problem is not None:
        return sql, _qed_alias_order_report(
            "unsupported",
            reason=star_problem["reason"],
            evidence=star_problem["evidence"],
        )
    if star_expansions and not cte_scan_complete:
        return sql, _qed_alias_order_report(
            "unsupported", reason="with-scope-could-not-be-attested-for-star-expansion"
        )
    if not candidates and not star_expansions:
        return sql, _qed_alias_order_report("not-applicable")

    replacements: list[tuple[int, int, str]] = list(star_replacements)
    transformations: list[dict[str, Any]] = []
    for candidate in candidates:
        source_columns = candidate["sourceColumns"]
        aliases = candidate["aliases"]
        alias_by_column = dict(zip(source_columns, aliases))
        qed_columns = sorted(source_columns)
        reordered = [alias_by_column[column] for column in qed_columns]
        before_order = [alias.value for alias in aliases]
        after_order = [alias.value for alias in reordered]
        changed = before_order != after_order
        if changed:
            replacements.append(
                (
                    candidate["openToken"].end,
                    candidate["closeToken"].start,
                    ", ".join(alias.text for alias in reordered),
                )
            )
        transformations.append(
            {
                "table": candidate["tableToken"].value,
                "tableAlias": candidate["aliasToken"].value,
                "line": sql.count("\n", 0, candidate["tableToken"].start) + 1,
                "changed": changed,
                "sourceColumnOrder": source_columns,
                "aliasOrderBefore": before_order,
                "qedColumnOrder": qed_columns,
                "aliasOrderAfter": after_order,
            }
        )

    normalized = sql
    for start, end, replacement in sorted(replacements, reverse=True):
        normalized = normalized[:start] + replacement + normalized[end:]
    alias_changed = any(item["changed"] for item in transformations)
    status = (
        "verified-and-reordered"
        if alias_changed
        else ("verified-and-star-expanded" if star_expansions else "verified-no-change")
    )
    return normalized, _qed_alias_order_report(
        status,
        transformations=transformations,
        star_expansions=star_expansions,
    )


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Materialize core benchmark cases as QED inputs. Each case directory "
            "contains qed.sql, metadata.json, and qed.json when QED's parser accepts it."
        )
    )
    parser.add_argument("--config", default=DEFAULT_CONFIG)
    parser.add_argument("--output-dir", default=DEFAULT_OUTPUT)
    parser.add_argument(
        "--target",
        choices=("all", "wetune", "nonwetune"),
        default="all",
        help="Benchmark subset to materialize.",
    )
    parser.add_argument("--benchmark", action="append")
    parser.add_argument(
        "--case", action="append", help="Case id regex. May be repeated."
    )
    parser.add_argument("--limit", type=int)
    parser.add_argument("--force", action="store_true")
    parser.add_argument(
        "--skip-parser",
        action="store_true",
        help="Only write qed.sql/metadata.json; do not invoke PaperTools/scripts/qed-parser.",
    )
    args = parser.parse_args()

    exporter = load_exporter()
    config = json.loads(resolve_path(args.config).read_text())
    output_dir = resolve_path(args.output_dir)
    selected = set(args.benchmark or [])
    case_patterns = [re.compile(pattern) for pattern in args.case or []]

    if args.force:
        remove_selected_outputs(output_dir, args.target)
    output_dir.mkdir(parents=True, exist_ok=True)

    materialized = 0
    parser_failed = 0
    failed = 0
    for benchmark in config["benchmarks"]:
        benchmark_id = benchmark["id"]
        if not target_includes(args.target, benchmark_id):
            continue
        if selected and benchmark_id not in selected:
            continue
        for case in exporter.iter_cases(config, benchmark):
            if case_patterns and not case_matches(case, benchmark_id, case_patterns):
                continue
            if args.limit is not None and materialized >= args.limit:
                return finish(materialized, parser_failed, failed)
            try:
                status = materialize_case(
                    config, case, output_dir, skip_parser=args.skip_parser
                )
                materialized += 1
                if not args.skip_parser and status != "parsed":
                    parser_failed += 1
                print(
                    f"materialized {benchmark_id}/{case.case_id}: {status}",
                    file=sys.stderr,
                )
            except Exception as exc:
                failed += 1
                print(f"failed {benchmark_id}/{case.case_id}: {exc}", file=sys.stderr)
    return finish(materialized, parser_failed, failed)


def finish(materialized: int, parser_failed: int, failed: int) -> int:
    print(
        f"summary: materialized={materialized} parser_failed={parser_failed} failed={failed}",
        file=sys.stderr,
    )
    if materialized == 0:
        print(
            "failed: the selected QED materialization produced zero cases",
            file=sys.stderr,
        )
    return 1 if failed or materialized == 0 else 0


def remove_selected_outputs(output_dir: Path, target: str) -> None:
    if target == "all":
        if output_dir.exists():
            shutil.rmtree(output_dir)
        return
    selected = output_dir / (
        "wetune-issues" if target == "wetune" else "nonwetune-flat"
    )
    if selected.exists():
        shutil.rmtree(selected)


def target_includes(target: str, benchmark_id: str) -> bool:
    if target == "all":
        return True
    if target == "wetune":
        return benchmark_id == "wetune-issues"
    return benchmark_id != "wetune-issues"


def case_matches(case: Any, benchmark_id: str, patterns: list[re.Pattern]) -> bool:
    flat_case_id = flat_id(benchmark_id, case.case_id)
    return any(
        pattern.search(case.case_id) or pattern.search(flat_case_id)
        for pattern in patterns
    )


def load_exporter():
    loader = SourceFileLoader("logos_export_benchmark_ir", str(EXPORTER_PATH))
    spec = importlib.util.spec_from_loader("logos_export_benchmark_ir", loader)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load exporter from {EXPORTER_PATH}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def resolve_path(path: str | Path) -> Path:
    candidate = Path(path)
    return candidate if candidate.is_absolute() else ROOT / candidate


def count_noncomment_sql_statements(sql_text: str) -> int:
    return sum(
        bool(strip_sql_comments(statement).strip())
        for statement in split_sql_statements(sql_text)
    )


def materialize_case(
    config: dict[str, Any],
    case: Any,
    output_dir: Path,
    skip_parser: bool,
) -> str:
    benchmark_id = case.benchmark["id"]
    flat_case_id = flat_id(benchmark_id, case.case_id)
    case_dir = (
        output_dir
        / ("wetune-issues" if benchmark_id == "wetune-issues" else "nonwetune-flat")
        / flat_case_id
    )
    if benchmark_id == "wetune-issues":
        case_dir = output_dir / "wetune-issues" / case.case_id
    case_dir.mkdir(parents=True, exist_ok=True)
    for stale_name in (
        # A --skip-parser regeneration must not leave an older canonical
        # parser artifact behind: the runner's --parse-missing contract is
        # meaningful only when qed.json/qed.rkt belong to this exact qed.sql.
        "qed.json",
        "qed.rkt",
        "qed-equivalence-relaxed.sql",
        "qed-equivalence-relaxed.json",
        "qed-equivalence-relaxed.rkt",
        "qed-equivalence-star-expanded.sql",
        "qed-equivalence-star-expanded.json",
        "qed-equivalence-star-expanded.rkt",
        "qed-equivalence-projected.sql",
        "qed-equivalence-projected.json",
        "qed-equivalence-projected.rkt",
        "qed-equivalence-opaque-string.sql",
        "qed-equivalence-opaque-string.json",
        "qed-equivalence-opaque-string.rkt",
        "qed-equivalence-keyless.json",
    ):
        (case_dir / stale_name).unlink(missing_ok=True)

    read_dialect = case.read_dialect or case.benchmark.get("readDialect") or "postgres"
    write_dialect = "postgres"
    adapter = case.benchmark.get("adapter", config["defaults"].get("adapter", "none"))
    qed_solver_config = solver_materialization_config(case.benchmark, "qed")
    if qed_solver_config is not None and (
        qed_solver_config.get("queryPolicy") != _QED_BASE_ALIAS_QUERY_POLICY
        or qed_solver_config.get("preflight") != _QED_PARSER_PREFLIGHT_POLICY
    ):
        raise SolverFrontendConfigurationError(
            "unknown QED solver materialization policy: "
            + json.dumps(qed_solver_config, sort_keys=True)
        )
    raw_statement_counts = {
        "before": count_noncomment_sql_statements(case.before_sql),
        "after": count_noncomment_sql_statements(case.after_sql),
    }
    raw_pair_verified = all(count == 1 for count in raw_statement_counts.values())
    source_schema_type_authority = build_qed_source_schema_type_authority(
        case.schema_sql
    )

    with tempfile.TemporaryDirectory(prefix="logos-qed-") as tmp:
        tmp_dir = Path(tmp)
        before_alias_order: dict[str, Any] | None = None
        after_alias_order: dict[str, Any] | None = None
        if raw_pair_verified:
            before_sql, before_report = normalize_query(
                tmp_dir=tmp_dir,
                name="before",
                sql=case.before_sql,
                read=read_dialect,
                write=write_dialect,
                normalize=adapter == "sqlglot" or benchmark_id == "wetune-issues",
            )
            after_sql, after_report = normalize_query(
                tmp_dir=tmp_dir,
                name="after",
                sql=case.after_sql,
                read=read_dialect,
                write=write_dialect,
                normalize=adapter == "sqlglot" or benchmark_id == "wetune-issues",
            )
            before_sql, after_sql, day_arithmetic_report = patch_qed_tsql_date_day_pair(
                before_sql,
                after_sql,
                case.before_sql,
                case.after_sql,
                read_dialect,
            )
        else:
            before_sql = patch_qed_sql(strip_sql_comments(case.before_sql))
            after_sql = patch_qed_sql(strip_sql_comments(case.after_sql))
            before_report = {
                "skipped": True,
                "reason": "raw-query-side-statement-count-is-not-one",
            }
            after_report = dict(before_report)
            day_arithmetic_report = None
        if day_arithmetic_report is not None:
            before_report["qedPairCompatibility"] = day_arithmetic_report
            after_report["qedPairCompatibility"] = day_arithmetic_report
        if raw_pair_verified and qed_solver_config is not None:
            base_before_sql = before_sql
            base_after_sql = after_sql
            before_sql, before_alias_order = (
                normalize_qed_base_table_column_alias_lists(
                    base_before_sql, source_schema_type_authority
                )
            )
            after_sql, after_alias_order = normalize_qed_base_table_column_alias_lists(
                base_after_sql, source_schema_type_authority
            )
            pair_alias_boundary_active = any(
                report.get("status") != "not-applicable"
                for report in (before_alias_order, after_alias_order)
            )
            if pair_alias_boundary_active:
                before_sql, before_alias_order = (
                    normalize_qed_base_table_column_alias_lists(
                        base_before_sql,
                        source_schema_type_authority,
                        expand_all_attested_stars=True,
                    )
                )
                after_sql, after_alias_order = (
                    normalize_qed_base_table_column_alias_lists(
                        base_after_sql,
                        source_schema_type_authority,
                        expand_all_attested_stars=True,
                    )
                )
                pair_activation = {
                    "status": "activated-for-query-pair",
                    "queryPolicy": _QED_BASE_ALIAS_QUERY_POLICY,
                    "preflight": _QED_PARSER_PREFLIGHT_POLICY,
                    "reason": (
                        "at least one query side contains an attested base-table "
                        "column-alias list"
                    ),
                    "unqualifiedStarPolicy": (
                        "expand only complete direct schema-attested base rows on "
                        "both sides; leave unrelated unattested star scopes unchanged"
                    ),
                }
                for report in (before_alias_order, after_alias_order):
                    if report.get("status") != "not-applicable":
                        report["pairBoundaryActivation"] = pair_activation
        elif qed_solver_config is not None:
            before_alias_order = _qed_alias_order_report(
                "skipped", reason="raw-query-side-statement-count-is-not-one"
            )
            after_alias_order = dict(before_alias_order)
        if before_alias_order is not None and before_alias_order.get("status") not in {
            "not-applicable",
            "skipped",
        }:
            before_report["qedBaseTableColumnAliasOrder"] = before_alias_order
        if after_alias_order is not None and after_alias_order.get("status") not in {
            "not-applicable",
            "skipped",
        }:
            after_report["qedBaseTableColumnAliasOrder"] = after_alias_order
        quote_schema_identifiers = (
            adapter == "sqlglot" or benchmark_id == "wetune-issues"
        )
        schema_sql, constraint_coverage = render_qed_schema(
            case.schema_sql,
            before_sql + "\n" + after_sql,
            quote_identifiers=quote_schema_identifiers,
            constraints=case.constraints,
        )
        relaxed_schema_sql, relaxed_constraint_coverage = render_qed_schema(
            case.schema_sql,
            before_sql + "\n" + after_sql,
            quote_identifiers=quote_schema_identifiers,
            constraints=case.constraints,
            relax_not_null_varchar=True,
        )

    normalized_statement_counts = {
        "before": count_noncomment_sql_statements(before_sql),
        "after": count_noncomment_sql_statements(after_sql),
    }
    pair_verified = raw_pair_verified and all(
        count == 1 for count in normalized_statement_counts.values()
    )
    alias_order_verified = all(
        report is None or report.get("status") != "unsupported"
        for report in (before_alias_order, after_alias_order)
    )
    pair_statement_attestation = {
        "status": (
            "verified-single-statement-query-pair"
            if pair_verified
            else "unsupported-multi-statement-query-side"
        ),
        "requiredStatementCounts": {"before": 1, "after": 1},
        "rawStatementCounts": raw_statement_counts,
        "rawSha256": {
            "before": hashlib.sha256(case.before_sql.encode()).hexdigest(),
            "after": hashlib.sha256(case.after_sql.encode()).hexdigest(),
        },
        "normalizedStatementCounts": normalized_statement_counts,
        "policy": "one-query-statement-per-source-side",
    }

    qed_sql = (
        schema_sql
        + "\n"
        + ensure_sql_terminated(before_sql)
        + ensure_sql_terminated(after_sql)
    )
    qed_sql = patch_qed_interval_precision(qed_sql)
    write_text(case_dir / "qed.sql", qed_sql)
    qed_input_sha256 = sha256_path(case_dir / "qed.sql")

    fallback = None
    if pair_verified and alias_order_verified and relaxed_schema_sql != schema_sql:
        fallback_sql = patch_qed_interval_precision(
            relaxed_schema_sql
            + "\n"
            + ensure_sql_terminated(before_sql)
            + ensure_sql_terminated(after_sql)
        )
        write_text(case_dir / "qed-equivalence-relaxed.sql", fallback_sql)
        relaxed_input = case_dir / "qed-equivalence-relaxed.sql"
        fallback = {
            "id": "not-null-varchar-relaxed",
            "input": "qed-equivalence-relaxed.sql",
            "inputSha256": sha256_path(relaxed_input),
            "sourceInput": "qed.sql",
            "sourceInputSha256": qed_input_sha256,
            "generatedJson": "qed-equivalence-relaxed.json",
            "trigger": "qed-calcite-not-null-varchar-charset-bug",
            "resultPolicy": "accept-eq-only",
            "rowTypePolicy": "all-selected-source-columns-preserved",
            "constraintCoverage": relaxed_constraint_coverage,
        }

    parser_allowed = not skip_parser and pair_verified and alias_order_verified
    if not pair_verified:
        parser_status = {
            "skipped": True,
            "jsonExists": False,
            "statementAttestation": pair_statement_attestation,
        }
        parser_problem = {
            "kind": "multi-statement-query-side",
            "message": (
                "QED requires exactly one query statement on each source side: "
                f"raw={raw_statement_counts!r}, "
                f"normalized={normalized_statement_counts!r}"
            ),
        }
    elif not alias_order_verified:
        failed_sides = [
            {
                "side": side,
                "reason": report.get("reason"),
                "evidence": report.get("evidence"),
            }
            for side, report in (
                ("before", before_alias_order),
                ("after", after_alias_order),
            )
            if report.get("status") == "unsupported"
        ]
        parser_status = {
            "skipped": True,
            "jsonExists": False,
            "frontendNormalization": {
                "status": "unsupported",
                "kind": "qed-base-table-column-alias-order",
                "failedSides": failed_sides,
            },
        }
        parser_problem = {
            "kind": "unsafe-base-table-column-alias-list",
            "message": (
                "QED base-table column-alias ordering could not be attested: "
                + json.dumps(failed_sides, sort_keys=True)
            ),
        }
    elif skip_parser:
        parser_status = {"skipped": True}
        parser_problem = None
    else:
        parser_status = run_qed_parser(case_dir / "qed.sql")
        parser_problem = classify_qed_parser_problem(parser_status)
    parser_warning = (
        classify_qed_parser_warning(parser_status) if parser_allowed else None
    )
    active_constraint_coverage = constraint_coverage
    active_variant = "source-constraint-profile"
    star_fallback = None
    projection_fallback = None
    opaque_string_fallback = None
    star_status = None
    star_problem = None
    # QED sorts scan fields by name internally.  That can make a source-side
    # SELECT * disagree with an equivalent explicit source-order projection
    # even when the exact DDL itself parsed successfully.  Try the same
    # full-schema, star-only bridge directly from the source profile before
    # considering any constraint relaxation.
    if parser_allowed and is_qed_output_signature_problem(parser_problem):
        source_status = parser_status
        source_problem = parser_problem
        try:
            star_fallback = create_qed_star_expansion_equivalence_fallback(
                case_dir / "qed.sql",
                case_dir / "qed-equivalence-star-expanded.sql",
                constraint_coverage,
                benchmark_id,
                case.case_id,
            )
            star_status = run_qed_parser(case_dir / star_fallback["input"])
            star_problem = classify_qed_parser_problem(star_status)
            star_warning = classify_qed_parser_warning(star_status)
            if star_problem is None and star_status.get("jsonExists"):
                try:
                    star_status["jsonValidation"] = validate_qed_star_expansion_result(
                        case_dir / star_fallback["generatedJson"],
                        star_fallback,
                    )
                except QedJsonValidationError as exc:
                    star_problem = {"kind": "parser-error", "message": str(exc)}
            attempts = [
                {
                    "variant": "source-constraint-profile",
                    "status": source_status,
                    "problem": source_problem,
                },
                {
                    "variant": star_fallback["id"],
                    "status": star_status,
                    "problem": star_problem,
                },
            ]
            parser_status = {
                **star_status,
                "variant": star_fallback["id"],
                "attempts": attempts,
            }
            parser_problem = star_problem
            parser_warning = star_warning
            if star_problem is None and star_status.get("jsonExists"):
                promote_qed_parser_artifacts(
                    case_dir / star_fallback["input"], case_dir / "qed.sql"
                )
                parser_status["jsonExists"] = True
                parser_status["rktExists"] = (case_dir / "qed.rkt").exists()
                parser_status["jsonValidation"] = validate_qed_star_expansion_result(
                    case_dir / "qed.json", star_fallback
                )
                active_constraint_coverage = star_fallback["constraintCoverage"]
                active_variant = star_fallback["id"]
        except QedJsonValidationError as exc:
            star_fallback = {
                "id": "ast-star-expanded-equivalence",
                "status": "unavailable",
                "message": str(exc),
                "resultPolicy": "accept-eq-only",
            }
    if parser_allowed and is_qed_varchar_charset_problem(parser_problem):
        source_status = parser_status
        source_problem = parser_problem
        source_warning = parser_warning
        previous_attempts = parser_status.get("attempts")
        attempts = (
            list(previous_attempts)
            if isinstance(previous_attempts, list)
            else [
                {
                    "variant": "source-constraint-profile",
                    "status": source_status,
                    "problem": source_problem,
                }
            ]
        )
        try:
            opaque_string_fallback = create_qed_opaque_string_equivalence_fallback(
                case_dir / "qed.sql",
                case_dir / "qed-equivalence-opaque-string.sql",
                constraint_coverage,
                benchmark_id,
                case.case_id,
            )
            opaque_status = run_qed_parser(case_dir / opaque_string_fallback["input"])
            opaque_problem = classify_qed_parser_problem(opaque_status)
            opaque_warning = classify_qed_parser_warning(opaque_status)
            if opaque_problem is None and opaque_status.get("jsonExists"):
                try:
                    opaque_status["jsonValidation"] = validate_qed_opaque_string_result(
                        case_dir / opaque_string_fallback["generatedJson"],
                        opaque_string_fallback,
                    )
                except QedJsonValidationError as exc:
                    opaque_problem = {"kind": "parser-error", "message": str(exc)}
            attempts.append(
                {
                    "variant": opaque_string_fallback["id"],
                    "status": opaque_status,
                    "problem": opaque_problem,
                }
            )
            if opaque_problem is None and opaque_status.get("jsonExists"):
                parser_status = {
                    **opaque_status,
                    "variant": opaque_string_fallback["id"],
                    "attempts": attempts,
                }
                parser_problem = None
                parser_warning = opaque_warning
                promote_qed_parser_artifacts(
                    case_dir / opaque_string_fallback["input"],
                    case_dir / "qed.sql",
                )
                parser_status["jsonExists"] = True
                parser_status["rktExists"] = (case_dir / "qed.rkt").exists()
                parser_status["jsonValidation"] = validate_qed_opaque_string_result(
                    case_dir / "qed.json", opaque_string_fallback
                )
                active_constraint_coverage = opaque_string_fallback[
                    "constraintCoverage"
                ]
                active_variant = opaque_string_fallback["id"]
            else:
                parser_status = {**source_status, "attempts": attempts}
                parser_problem = source_problem
                parser_warning = source_warning
        except QedJsonValidationError as exc:
            opaque_string_fallback = {
                "id": "opaque-varchar-equality-integer-abstraction",
                "status": "unavailable",
                "message": str(exc),
                "resultPolicy": "accept-eq-only",
            }
    if (
        parser_allowed
        and fallback is not None
        and is_qed_varchar_charset_problem(parser_problem)
    ):
        fallback_status = run_qed_parser(case_dir / fallback["input"])
        fallback_problem = classify_qed_parser_problem(fallback_status)
        fallback_warning = classify_qed_parser_warning(fallback_status)
        previous_attempts = parser_status.get("attempts")
        attempts = (
            list(previous_attempts)
            if isinstance(previous_attempts, list)
            else [
                {
                    "variant": "source-constraint-profile",
                    "status": parser_status,
                    "problem": parser_problem,
                }
            ]
        )
        attempts.append(
            {
                "variant": fallback["id"],
                "status": fallback_status,
                "problem": fallback_problem,
            }
        )
        parser_status = {
            **fallback_status,
            "variant": fallback["id"],
            "attempts": attempts,
        }
        parser_problem = fallback_problem
        parser_warning = fallback_warning
        star_status = None
        star_problem = None
        if is_qed_output_signature_problem(fallback_problem):
            try:
                star_fallback = create_qed_star_expansion_equivalence_fallback(
                    case_dir / fallback["input"],
                    case_dir / "qed-equivalence-star-expanded.sql",
                    relaxed_constraint_coverage,
                    benchmark_id,
                    case.case_id,
                )
                star_status = run_qed_parser(case_dir / star_fallback["input"])
                star_problem = classify_qed_parser_problem(star_status)
                star_warning = classify_qed_parser_warning(star_status)
                if star_problem is None and star_status.get("jsonExists"):
                    try:
                        star_status["jsonValidation"] = (
                            validate_qed_star_expansion_result(
                                case_dir / star_fallback["generatedJson"],
                                star_fallback,
                            )
                        )
                    except QedJsonValidationError as exc:
                        star_problem = {"kind": "parser-error", "message": str(exc)}
                attempts.append(
                    {
                        "variant": star_fallback["id"],
                        "status": star_status,
                        "problem": star_problem,
                    }
                )
                parser_status = {
                    **star_status,
                    "variant": star_fallback["id"],
                    "attempts": attempts,
                }
                parser_problem = star_problem
                parser_warning = star_warning
            except QedJsonValidationError as exc:
                star_fallback = {
                    "id": "ast-star-expanded-equivalence",
                    "status": "unavailable",
                    "message": str(exc),
                    "resultPolicy": "accept-eq-only",
                }
        if is_qed_varchar_charset_problem(fallback_problem):
            try:
                projection_fallback = create_qed_projection_equivalence_fallback(
                    case_dir / fallback["input"],
                    case_dir / "qed-equivalence-projected.sql",
                    relaxed_constraint_coverage,
                )
                projected_status = run_qed_parser(
                    case_dir / projection_fallback["input"]
                )
                projected_problem = classify_qed_parser_problem(projected_status)
                projected_warning = classify_qed_parser_warning(projected_status)
                if projected_problem is None and projected_status.get("jsonExists"):
                    try:
                        projected_status["jsonValidation"] = (
                            validate_qed_projection_result(
                                case_dir / projection_fallback["generatedJson"],
                                projection_fallback,
                            )
                        )
                    except QedJsonValidationError as exc:
                        projected_problem = {
                            "kind": "parser-error",
                            "message": str(exc),
                        }
                attempts.append(
                    {
                        "variant": projection_fallback["id"],
                        "status": projected_status,
                        "problem": projected_problem,
                    }
                )
                parser_status = {
                    **projected_status,
                    "variant": projection_fallback["id"],
                    "attempts": attempts,
                }
                parser_problem = projected_problem
                parser_warning = projected_warning
                if projected_problem is None and projected_status.get("jsonExists"):
                    active_constraint_coverage = projection_fallback[
                        "constraintCoverage"
                    ]
            except QedJsonValidationError as exc:
                projection_fallback = {
                    "id": "ast-column-projected-equivalence",
                    "status": "unavailable",
                    "message": str(exc),
                    "resultPolicy": "accept-eq-only",
                }
        if fallback_problem is None and fallback_status.get("jsonExists"):
            promote_qed_parser_artifacts(
                case_dir / fallback["input"], case_dir / "qed.sql"
            )
            parser_status["jsonExists"] = True
            parser_status["rktExists"] = (case_dir / "qed.rkt").exists()
            parser_status["jsonValidation"] = validate_qed_json(case_dir / "qed.json")
            active_constraint_coverage = relaxed_constraint_coverage
            active_variant = fallback["id"]
        elif (
            isinstance(star_fallback, dict)
            and star_fallback.get("status") != "unavailable"
            and star_problem is None
            and isinstance(star_status, dict)
            and star_status.get("jsonExists")
        ):
            promote_qed_parser_artifacts(
                case_dir / star_fallback["input"], case_dir / "qed.sql"
            )
            parser_status["jsonExists"] = True
            parser_status["rktExists"] = (case_dir / "qed.rkt").exists()
            parser_status["jsonValidation"] = validate_qed_star_expansion_result(
                case_dir / "qed.json", star_fallback
            )
            active_constraint_coverage = star_fallback["constraintCoverage"]
            active_variant = star_fallback["id"]
        elif (
            isinstance(projection_fallback, dict)
            and projection_fallback.get("status") != "unavailable"
            and parser_problem is None
            and parser_status.get("jsonExists")
        ):
            promote_qed_parser_artifacts(
                case_dir / projection_fallback["input"], case_dir / "qed.sql"
            )
            parser_status["jsonExists"] = True
            parser_status["rktExists"] = (case_dir / "qed.rkt").exists()
            parser_status["jsonValidation"] = validate_qed_projection_result(
                case_dir / "qed.json", projection_fallback
            )
            active_constraint_coverage = projection_fallback["constraintCoverage"]
            active_variant = projection_fallback["id"]
    json_repair = None
    keyless_fallback = {
        "id": "keyless-equivalence-retry",
        "generatedJson": "qed-equivalence-keyless.json",
        "trigger": "qed-prover-error-on-keyed-input",
        "resultPolicy": "accept-eq-only",
        "rowTypePolicy": "identical-to-canonical-qed-json",
        "attestation": None,
    }
    if parser_allowed and parser_problem is None and parser_status.get("jsonExists"):
        try:
            json_repair = repair_qed_json(
                case_dir / "qed.json",
                expected_table_keys=active_constraint_coverage["renderedKeys"],
            )
            apply_qed_json_repair_coverage(active_constraint_coverage, json_repair)
            if (
                active_variant == "opaque-varchar-equality-integer-abstraction"
                and isinstance(opaque_string_fallback, dict)
                and opaque_string_fallback.get("status") != "unavailable"
            ):
                parser_status["jsonValidation"] = validate_qed_opaque_string_result(
                    case_dir / "qed.json",
                    opaque_string_fallback,
                )
            elif (
                active_variant == "ast-star-expanded-equivalence"
                and isinstance(star_fallback, dict)
                and star_fallback.get("status") != "unavailable"
            ):
                parser_status["jsonValidation"] = validate_qed_star_expansion_result(
                    case_dir / "qed.json",
                    star_fallback,
                )
            else:
                parser_status["jsonValidation"] = validate_qed_json(
                    case_dir / "qed.json"
                )
            keyless_fallback["attestation"] = write_qed_keyless_equivalence_variant(
                case_dir / "qed.json",
                case_dir / keyless_fallback["generatedJson"],
            )
        except (QedJsonRepairError, QedJsonValidationError) as exc:
            json_repair = {"status": "error", "message": str(exc)}
            parser_problem = {"kind": "parser-error", "message": str(exc)}
    if parser_problem and (case_dir / "qed.json").exists():
        (case_dir / "qed.json").unlink()
        parser_status["jsonExists"] = False
    status = (
        "parser-error"
        if not pair_verified or not alias_order_verified
        else (
            "not-parsed"
            if skip_parser
            else (
                "parsed"
                if parser_status.get("jsonExists") and parser_problem is None
                else "parser-error"
            )
        )
    )

    write_text(
        case_dir / "metadata.json",
        json.dumps(
            {
                **build_metadata(config, case, flat_case_id),
                "profile": "qed",
                "status": status,
                "qedInput": "qed.sql",
                "qedInputSha256": qed_input_sha256,
                "sourceSchemaTypeAuthority": source_schema_type_authority,
                "qedPairStatementAttestation": pair_statement_attestation,
                "qedJson": "qed.json" if (case_dir / "qed.json").exists() else None,
                "activeQEDVariant": active_variant,
                "qedEquivalenceFallback": fallback,
                "qedStarExpansionEquivalenceFallback": star_fallback,
                "qedProjectionEquivalenceFallback": projection_fallback,
                "qedOpaqueStringEquivalenceFallback": opaque_string_fallback,
                "qedKeylessEquivalenceFallback": keyless_fallback,
                "normalizationForSolverRun": {
                    "schema": {
                        "renderer": "logos-qed-schema-renderer",
                        "semanticNote": (
                            "DDL is simplified to QED parser-supported CREATE TABLE "
                            "statements. Every selected relation retains all source "
                            "columns and NOT NULL declarations, but no key declaration "
                            "is exposed during Calcite planning. Attested keys are "
                            "injected into parser JSON afterward; conservative omissions "
                            "are enumerated in constraintCoverage."
                        ),
                    },
                    "before": before_report,
                    "after": after_report,
                },
                "constraintCompatibility": active_constraint_coverage["compatibility"],
                "constraintCoverage": active_constraint_coverage,
                "sourceConstraintCoverage": json.loads(json.dumps(constraint_coverage)),
                "qedJsonRepair": json_repair,
                "parser": parser_status,
                "parserProblem": parser_problem,
                "parserWarning": parser_warning,
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
    )
    return status


def flat_id(benchmark_id: str, case_id: str) -> str:
    return f"{benchmark_id}__{case_id}"


def normalize_query(
    tmp_dir: Path,
    name: str,
    sql: str,
    read: str,
    write: str,
    normalize: bool,
) -> tuple[str, dict[str, Any]]:
    source = write_text(tmp_dir / f"{name}.source.sql", ensure_sql_terminated(sql))
    if not normalize:
        return patch_qed_sql(strip_sql_comments(source.read_text())), {"skipped": True}

    target = tmp_dir / f"{name}.normalized.sql"
    report = tmp_dir / f"{name}.normalization.json"
    command = [
        str(ROOT / "benchmarks/scripts/sqlglot-normalize"),
        "--input",
        str(source),
        "--output",
        str(target),
        "--report",
        str(report),
        "--read",
        read,
        "--write",
        write,
        "--identify",
    ]
    completed = subprocess.run(
        command,
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if completed.returncode != 0:
        raise RuntimeError(completed.stderr)
    logical_command = [
        "benchmarks/scripts/sqlglot-normalize",
        "--input",
        f"<temporary>/{source.name}",
        "--output",
        f"<temporary>/{target.name}",
        "--report",
        f"<temporary>/{report.name}",
        "--read",
        read,
        "--write",
        write,
        "--identify",
    ]
    return patch_qed_sql(target.read_text()), {
        "command": logical_command,
        "commandPathPolicy": (
            "Repository-relative executable plus stable <temporary> placeholders; "
            "the executed scratch directory is intentionally not serialized."
        ),
        "returnCode": completed.returncode,
        "stderrTail": tail(completed.stderr),
        "report": json.loads(report.read_text()),
    }


def run_qed_parser(sql_path: Path) -> dict[str, Any]:
    case_dir = sql_path.parent
    artifact_base = sql_path.with_suffix("")
    for suffix in (".json", ".rkt"):
        path = artifact_base.with_suffix(suffix)
        if path.exists():
            path.unlink()
    command = [str(ROOT.parent / "PaperTools/scripts/qed-parser"), str(sql_path)]
    started = subprocess.run(
        command,
        cwd=ROOT.parent,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    log_stem = "qed-parser" if sql_path.name == "qed.sql" else f"{sql_path.stem}-parser"
    stdout_log = write_text(case_dir / f"{log_stem}.stdout.log", started.stdout)
    stderr_log = write_text(case_dir / f"{log_stem}.stderr.log", started.stderr)
    json_path = artifact_base.with_suffix(".json")
    status = {
        "command": command,
        "input": sql_path.name,
        "stdoutLog": stdout_log.name,
        "stderrLog": stderr_log.name,
        "returnCode": started.returncode,
        "artifactsClearedBeforeRun": True,
        "jsonExists": json_path.exists(),
        "rktExists": artifact_base.with_suffix(".rkt").exists(),
        "stdoutTail": tail(started.stdout),
        "stderrTail": tail(started.stderr),
    }
    if json_path.exists():
        try:
            status["jsonValidation"] = validate_qed_json(json_path)
        except QedJsonValidationError as exc:
            status["jsonValidation"] = {"status": "error", "message": str(exc)}
    return status


def promote_qed_parser_artifacts(
    source_sql: str | Path, target_sql: str | Path
) -> None:
    """Promote one freshly parsed fallback to the canonical QED artifact names."""

    source_base = Path(source_sql).with_suffix("")
    target_base = Path(target_sql).with_suffix("")
    source_json = source_base.with_suffix(".json")
    target_json = target_base.with_suffix(".json")
    if not source_json.exists():
        raise QedJsonValidationError(f"fallback parser emitted no JSON: {source_json}")
    validate_qed_json(source_json)
    if target_json.exists():
        target_json.unlink()
    source_json.replace(target_json)
    source_rkt = source_base.with_suffix(".rkt")
    target_rkt = target_base.with_suffix(".rkt")
    if target_rkt.exists():
        target_rkt.unlink()
    if source_rkt.exists():
        source_rkt.replace(target_rkt)


def _validate_qed_expression(
    expression: Any,
    schema_signatures: list[list[str]],
    context: str,
) -> str:
    if not isinstance(expression, dict) or not isinstance(expression.get("type"), str):
        raise QedJsonValidationError(f"{context} has no string-valued QED type")
    if "column" in expression:
        if (
            not isinstance(expression["column"], int)
            or isinstance(expression["column"], bool)
            or set(expression) != {"column", "type"}
        ):
            raise QedJsonValidationError(f"{context} is a malformed column expression")
        return expression["type"]
    if not isinstance(expression.get("operator"), str) or not isinstance(
        expression.get("operand"), list
    ):
        raise QedJsonValidationError(f"{context} is a malformed operator expression")
    allowed = {"operator", "operand", "type", "query", "distinct", "ignoreNulls"}
    if any(key not in allowed for key in expression):
        raise QedJsonValidationError(f"{context} has unknown expression fields")
    for index, operand in enumerate(expression["operand"]):
        _validate_qed_expression(
            operand, schema_signatures, f"{context}.operand[{index}]"
        )
    if "query" in expression:
        _qed_rel_output_signature(
            expression["query"], schema_signatures, f"{context}.query"
        )
    for flag in ("distinct", "ignoreNulls"):
        if flag in expression and not isinstance(expression[flag], bool):
            raise QedJsonValidationError(f"{context}.{flag} is not Boolean")
    return expression["type"]


def _qed_set_common_signature(
    signatures: list[list[str]],
    context: str,
) -> list[str]:
    arity = len(signatures[0])
    if any(len(signature) != arity for signature in signatures[1:]):
        raise QedJsonValidationError(f"{context} input arities disagree")
    strings = {"CHAR", "VARCHAR"}
    integers = {"TINYINT", "SMALLINT", "INTEGER", "BIGINT"}
    approximate = {"REAL", "FLOAT", "DOUBLE"}
    exact_numeric = integers | {"DECIMAL"}
    common = []
    for index in range(arity):
        types = {signature[index].upper() for signature in signatures}
        non_null = types - {"NULL"}
        if not non_null:
            common.append("NULL")
        elif len(non_null) == 1:
            common.append(next(iter(non_null)))
        elif non_null <= strings:
            common.append("VARCHAR")
        elif non_null <= exact_numeric | approximate:
            if non_null & approximate:
                common.append("DOUBLE")
            elif "DECIMAL" in non_null:
                common.append("DECIMAL")
            elif "BIGINT" in non_null:
                common.append("BIGINT")
            else:
                common.append("INTEGER")
        elif non_null <= {"DATE", "TIMESTAMP"}:
            common.append("TIMESTAMP")
        else:
            raise QedJsonValidationError(
                f"{context} has incompatible types at output {index}: {sorted(types)}"
            )
    return common


def _qed_rel_output_signature(
    relation: Any,
    schema_signatures: list[list[str]],
    context: str,
) -> list[str]:
    """Recover a serialized QED relation's complete output type vector.

    This deliberately understands exactly the relation constructors emitted by
    QED's JSONSerializer.  Rejecting an unknown or malformed constructor is what
    lets a JSON file written before the legacy Racket exporter failed serve as a
    complete prover input rather than merely evidence that a file happened to
    exist.
    """

    if not isinstance(relation, dict) or len(relation) != 1:
        raise QedJsonValidationError(
            f"{context} is not a singleton QED relation object"
        )
    kind, payload = next(iter(relation.items()))
    if kind == "scan":
        if not isinstance(payload, int) or isinstance(payload, bool):
            raise QedJsonValidationError(
                f"{context}.scan is not an integer schema index"
            )
        if payload < 0 or payload >= len(schema_signatures):
            raise QedJsonValidationError(
                f"{context}.scan references missing schema {payload}"
            )
        return list(schema_signatures[payload])
    if kind == "values":
        if (
            not isinstance(payload, dict)
            or set(payload) != {"schema", "content"}
            or not isinstance(payload.get("schema"), list)
        ):
            raise QedJsonValidationError(f"{context}.values has no schema array")
        signature = payload["schema"]
        if not signature or not all(isinstance(item, str) for item in signature):
            raise QedJsonValidationError(
                f"{context}.values has an invalid output signature"
            )
        content = payload.get("content")
        if not isinstance(content, list) or any(
            not isinstance(row, list) or len(row) != len(signature) for row in content
        ):
            raise QedJsonValidationError(f"{context}.values has malformed rows")
        for row_index, row in enumerate(content):
            for column_index, value in enumerate(row):
                _validate_qed_expression(
                    value,
                    schema_signatures,
                    f"{context}.values.content[{row_index}][{column_index}]",
                )
        return list(signature)
    if kind == "filter":
        if not isinstance(payload, dict) or set(payload) != {"condition", "source"}:
            raise QedJsonValidationError(f"{context}.filter has incomplete fields")
        signature = _qed_rel_output_signature(
            payload["source"], schema_signatures, f"{context}.filter.source"
        )
        _validate_qed_expression(
            payload["condition"], schema_signatures, f"{context}.filter.condition"
        )
        return signature
    if kind == "sort":
        required = {"collation", "source", "offset", "limit"}
        if not isinstance(payload, dict) or set(payload) != required:
            raise QedJsonValidationError(f"{context}.sort has incomplete fields")
        signature = _qed_rel_output_signature(
            payload["source"], schema_signatures, f"{context}.sort.source"
        )
        collations = payload["collation"]
        if not isinstance(collations, list):
            raise QedJsonValidationError(f"{context}.sort.collation is not an array")
        for index, collation in enumerate(collations):
            if (
                not isinstance(collation, list)
                or len(collation) != 3
                or not isinstance(collation[0], int)
                or isinstance(collation[0], bool)
                or collation[0] < 0
                or collation[0] >= len(signature)
                or not isinstance(collation[1], str)
                or not isinstance(collation[2], str)
            ):
                raise QedJsonValidationError(
                    f"{context}.sort.collation[{index}] is malformed"
                )
        for field in ("offset", "limit"):
            value = payload[field]
            if value is not None:
                _validate_qed_expression(
                    value, schema_signatures, f"{context}.sort.{field}"
                )
        return signature
    if kind == "project":
        if not isinstance(payload, dict) or set(payload) != {"source", "target"}:
            raise QedJsonValidationError(f"{context}.project has no source")
        # Validate the complete child too: a well-typed target vector alone must
        # not make a truncated or unknown subtree acceptable.
        _qed_rel_output_signature(
            payload["source"], schema_signatures, f"{context}.project.source"
        )
        targets = payload.get("target")
        if not isinstance(targets, list) or not targets:
            raise QedJsonValidationError(f"{context}.project has no output expressions")
        return [
            _validate_qed_expression(
                target, schema_signatures, f"{context}.project.target[{index}]"
            )
            for index, target in enumerate(targets)
        ]
    if kind in {"join", "correlate"}:
        required = {"kind", "left", "right"} | (
            {"condition"} if kind == "join" else set()
        )
        if not isinstance(payload, dict) or set(payload) != required:
            raise QedJsonValidationError(f"{context}.{kind} has incomplete inputs")
        left_signature = _qed_rel_output_signature(
            payload["left"], schema_signatures, f"{context}.{kind}.left"
        )
        right_signature = _qed_rel_output_signature(
            payload["right"], schema_signatures, f"{context}.{kind}.right"
        )
        join_kind = payload.get("kind")
        if not isinstance(join_kind, str) or join_kind.upper() not in {
            "INNER",
            "LEFT",
            "RIGHT",
            "FULL",
            "SEMI",
            "ANTI",
        }:
            raise QedJsonValidationError(f"{context}.{kind} has invalid join kind")
        if kind == "join":
            _validate_qed_expression(
                payload["condition"], schema_signatures, f"{context}.join.condition"
            )
        if join_kind.upper() in {"SEMI", "ANTI"}:
            return left_signature
        return left_signature + right_signature
    if kind == "group":
        if not isinstance(payload, dict) or set(payload) != {
            "source",
            "keys",
            "function",
        }:
            raise QedJsonValidationError(f"{context}.group has no source")
        _qed_rel_output_signature(
            payload["source"], schema_signatures, f"{context}.group.source"
        )
        keys = payload.get("keys")
        functions = payload.get("function")
        if not isinstance(keys, list) or not isinstance(functions, list):
            raise QedJsonValidationError(f"{context}.group has malformed outputs")
        signature = [
            _validate_qed_expression(
                key, schema_signatures, f"{context}.group.keys[{index}]"
            )
            for index, key in enumerate(keys)
        ]
        signature.extend(
            _validate_qed_expression(
                function, schema_signatures, f"{context}.group.function[{index}]"
            )
            for index, function in enumerate(functions)
        )
        if not signature:
            raise QedJsonValidationError(
                f"{context}.group has an empty output signature"
            )
        return signature
    if kind in {"union", "intersect", "except"}:
        if not isinstance(payload, list) or not payload:
            raise QedJsonValidationError(f"{context}.{kind} has no inputs")
        signatures = [
            _qed_rel_output_signature(
                child, schema_signatures, f"{context}.{kind}[{index}]"
            )
            for index, child in enumerate(payload)
        ]
        return _qed_set_common_signature(signatures, f"{context}.{kind}")
    if kind == "distinct":
        return _qed_rel_output_signature(
            payload, schema_signatures, f"{context}.distinct"
        )
    raise QedJsonValidationError(f"{context} uses unknown QED relation {kind!r}")


def validate_qed_json(json_path: str | Path) -> dict[str, Any]:
    """Validate a fresh QED JSON pair and attest its complete output signature.

    The independent source-to-QED invariant is enforced by render_qed_schema:
    every selected relation is rendered with its complete source row type.  In
    particular a SELECT * target cannot become shorter before this validator
    reconstructs its output arity.  Do not pair this validator with lexical or
    projection-based schema pruning.
    """

    json_path = Path(json_path)
    try:
        raw_bytes = json_path.read_bytes()
        document = json.loads(raw_bytes)
    except (OSError, json.JSONDecodeError) as exc:
        raise QedJsonValidationError(
            f"cannot read QED JSON {json_path}: {exc}"
        ) from exc
    if not isinstance(document, dict):
        raise QedJsonValidationError("QED JSON root is not an object")
    schemas = document.get("schemas")
    if not isinstance(schemas, list):
        raise QedJsonValidationError("QED JSON has no schema array")
    schema_signatures: list[list[str]] = []
    for index, schema in enumerate(schemas):
        if not isinstance(schema, dict) or not isinstance(schema.get("name"), str):
            raise QedJsonValidationError(f"QED schema {index} is malformed")
        fields = schema.get("fields")
        types = schema.get("types")
        nullabilities = schema.get("nullable")
        keys = schema.get("key")
        if (
            not isinstance(fields, list)
            or not all(isinstance(field, str) for field in fields)
            or len(set(field.casefold() for field in fields)) != len(fields)
            or not isinstance(types, list)
            or not all(isinstance(item, str) for item in types)
            or len(types) != len(fields)
            or not isinstance(nullabilities, list)
            or not all(isinstance(item, bool) for item in nullabilities)
            or len(nullabilities) != len(fields)
            or not isinstance(keys, list)
        ):
            raise QedJsonValidationError(
                f"QED schema {schema.get('name', index)!r} has an incomplete row signature"
            )
        schema_signatures.append(list(types))
    queries = document.get("queries")
    helps = document.get("help")
    if not isinstance(queries, list) or len(queries) != 2:
        raise QedJsonValidationError("QED JSON must contain exactly two queries")
    if (
        not isinstance(helps, list)
        or len(helps) != 2
        or not all(isinstance(item, str) and item.strip() for item in helps)
    ):
        raise QedJsonValidationError("QED JSON must contain two complete Calcite plans")
    signatures = [
        _qed_rel_output_signature(query, schema_signatures, f"queries[{index}]")
        for index, query in enumerate(queries)
    ]
    if not signatures[0] or signatures[0] != signatures[1]:
        raise QedJsonValidationError(
            f"QED query output signatures disagree: {signatures[0]!r} vs {signatures[1]!r}"
        )
    return {
        "status": "verified-complete-query-pair",
        "queryCount": 2,
        "outputArity": len(signatures[0]),
        "outputTypes": signatures[0],
        "sha256": hashlib.sha256(raw_bytes).hexdigest(),
    }


def _coerce_qed_output_nulls(
    relation: dict[str, Any],
    target: list[str],
    path: list[str | int],
    repairs: list[dict[str, Any]],
) -> None:
    kind, payload = next(iter(relation.items()))
    if kind in {"filter", "sort"}:
        _coerce_qed_output_nulls(
            payload["source"], target, path + [kind, "source"], repairs
        )
        return
    if kind == "distinct":
        _coerce_qed_output_nulls(payload, target, path + ["distinct"], repairs)
        return
    if kind == "project":
        expressions = payload["target"]
        if len(expressions) != len(target):
            raise QedJsonValidationError("QED project arity changed during NULL repair")
        for index, (expression, expected) in enumerate(zip(expressions, target)):
            if (
                expression.get("operator") == "NULL"
                and expression.get("operand") == []
                and expected.upper() != "NULL"
            ):
                current = expression.get("type", "").upper()
                if current not in {"NULL", expected.upper()}:
                    raise QedJsonValidationError(
                        "QED NULL output has a type incompatible with its set column"
                    )
                expression["type"] = expected
                repairs.append(
                    {
                        "path": path + ["project", "target", index, "type"],
                        "from": "NULL",
                        "to": expected,
                    }
                )
        return
    if kind == "values":
        schema = payload["schema"]
        if len(schema) != len(target):
            raise QedJsonValidationError("QED VALUES arity changed during NULL repair")
        for index, expected in enumerate(target):
            column_has_null = any(
                row[index].get("operator") == "NULL" and row[index].get("operand") == []
                for row in payload["content"]
            )
            if column_has_null and expected.upper() != "NULL":
                if schema[index].upper() not in {"NULL", expected.upper()}:
                    raise QedJsonValidationError(
                        "QED NULL VALUES column has an incompatible set type"
                    )
                schema[index] = expected
                repairs.append(
                    {
                        "path": path + ["values", "schema", index],
                        "from": "NULL",
                        "to": expected,
                    }
                )
                for row_index, row in enumerate(payload["content"]):
                    value = row[index]
                    if value.get("operator") == "NULL" and value.get("operand") == []:
                        if value.get("type", "").upper() not in {
                            "NULL",
                            expected.upper(),
                        }:
                            raise QedJsonValidationError(
                                "QED NULL VALUES literal has an incompatible set type"
                            )
                        value["type"] = expected
                        repairs.append(
                            {
                                "path": path
                                + ["values", "content", row_index, index, "type"],
                                "from": "NULL",
                                "to": expected,
                            }
                        )
        return
    if kind in {"union", "intersect", "except"}:
        for index, child in enumerate(payload):
            _coerce_qed_output_nulls(child, target, path + [kind, index], repairs)


def repair_qed_set_null_types(document: dict[str, Any]) -> list[dict[str, Any]]:
    """Restore SQL set-operation coercion omitted by QED's JSON serializer."""

    schemas = document.get("schemas")
    queries = document.get("queries")
    # Backward-compatible standalone key repair accepts schema-only fixtures
    # and historical metadata. Direct materialization/runner paths validate a
    # complete pair before calling repair.
    if queries is None:
        return []
    if not isinstance(schemas, list) or not isinstance(queries, list):
        raise QedJsonValidationError("cannot repair NULL types in malformed QED JSON")
    schema_signatures = [list(schema["types"]) for schema in schemas]
    repairs: list[dict[str, Any]] = []

    def visit(relation: dict[str, Any], path: list[str | int]) -> None:
        kind, payload = next(iter(relation.items()))
        children: list[tuple[dict[str, Any], list[str | int]]] = []
        if kind in {"filter", "project", "group", "sort"}:
            children.append((payload["source"], path + [kind, "source"]))
        elif kind in {"join", "correlate"}:
            children.extend(
                (
                    (payload["left"], path + [kind, "left"]),
                    (payload["right"], path + [kind, "right"]),
                )
            )
        elif kind == "distinct":
            children.append((payload, path + ["distinct"]))
        elif kind in {"union", "intersect", "except"}:
            children.extend(
                (child, path + [kind, index]) for index, child in enumerate(payload)
            )
        for child, child_path in children:
            visit(child, child_path)
        if kind in {"union", "intersect", "except"}:
            signatures = [
                _qed_rel_output_signature(
                    child, schema_signatures, f"repair.{kind}[{index}]"
                )
                for index, child in enumerate(payload)
            ]
            target = _qed_set_common_signature(signatures, f"repair.{kind}")
            for index, child in enumerate(payload):
                _coerce_qed_output_nulls(child, target, path + [kind, index], repairs)

    for index, query in enumerate(queries):
        visit(query, ["queries", index])
    return repairs


def apply_qed_json_repair_coverage(
    coverage: dict[str, Any],
    attestation: dict[str, Any],
) -> None:
    """Reflect conservative JSON key drops in one materializer coverage record."""

    applied = coverage.get("applied")
    omitted = coverage.get("omitted")
    dropped_keys = attestation.get("droppedKeys")
    if (
        not isinstance(applied, list)
        or not isinstance(omitted, list)
        or not isinstance(dropped_keys, list)
    ):
        raise QedJsonRepairError(
            "QED repair coverage/attestation has malformed applied, omitted, or droppedKeys"
        )
    dropped_identities: set[tuple[str, str, tuple[str, ...]]] = set()
    for dropped in dropped_keys:
        if (
            not isinstance(dropped, dict)
            or dropped.get("kind") not in {"primary", "unique"}
            or not isinstance(dropped.get("table"), str)
            or not isinstance(dropped.get("columns"), list)
            or not isinstance(dropped.get("reason"), str)
        ):
            raise QedJsonRepairError(
                f"malformed conservatively dropped QED key: {dropped!r}"
            )
        dropped_identities.add(
            (
                dropped["kind"],
                dropped["table"].casefold(),
                tuple(sorted(column.casefold() for column in dropped["columns"])),
            )
        )
        omitted.append(
            constraint_entry(
                dropped["kind"],
                "qed-json-repair",
                dropped["table"],
                dropped["columns"],
                dropped["reason"],
                missingColumns=dropped.get("missingColumns") or [],
                nullableColumns=dropped.get("nullableColumns") or [],
            )
        )
    coverage["applied"] = [
        entry
        for entry in applied
        if not (
            isinstance(entry, dict)
            and entry.get("kind") in {"primary", "unique"}
            and isinstance(entry.get("table"), str)
            and isinstance(entry.get("columns"), list)
            and all(isinstance(column, str) for column in entry["columns"])
            and (
                entry["kind"],
                entry["table"].casefold(),
                tuple(sorted(column.casefold() for column in entry["columns"])),
            )
            in dropped_identities
        )
    ]
    coverage["omitted"] = deduplicate_constraint_entries(omitted)
    coverage["compatibility"] = (
        "conservative-relaxation" if coverage["omitted"] else "exact"
    )


def repair_qed_json(
    json_path: str | Path,
    metadata_path: str | Path | None = None,
    *,
    expected_table_keys: list[dict[str, Any]] | None = None,
) -> dict[str, Any]:
    """Inject attested keys against QED's final serialized field order.

    QED's parser associates DDL key indexes with CREATE TABLE declaration order
    but emits each JSON schema's [fields] in map order.  Supplying a key to the
    parser can therefore both constrain Calcite planning with the wrong columns
    and serialize an unsound key.  The materializer deliberately withholds all
    keys from qed.sql, then this function injects attested keys only after the
    parser has fixed the JSON field order.  It is the single authority used by
    direct materialization and by the standalone benchmark runner. Expected
    keys come either from the in-memory post-parse attestation or from the
    backward-compatible [metadata.json/constraintCoverage/renderedKeys] field.

    Repair is deterministic and idempotent.  If RelPruner removed a rendered
    key column, or serialized it as unexpectedly nullable, that key is dropped
    and attested as a conservative relaxation: proving the stronger
    unconstrained problem remains sound for the source schema.  RelPruner can
    likewise remove an entire keyed table; that key is dropped conservatively.
    A duplicate schema/field, malformed schema shape, or malformed attestation
    remains an error because it cannot be interpreted safely.
    """

    json_path = Path(json_path)
    metadata: dict[str, Any] | None = None
    metadata_file = Path(metadata_path) if metadata_path is not None else None
    if metadata_file is not None:
        try:
            loaded_metadata = json.loads(metadata_file.read_text())
        except (OSError, json.JSONDecodeError) as exc:
            raise QedJsonRepairError(
                f"cannot read QED metadata {metadata_file}: {exc}"
            ) from exc
        if not isinstance(loaded_metadata, dict):
            raise QedJsonRepairError(f"QED metadata is not an object: {metadata_file}")
        metadata = loaded_metadata
        if expected_table_keys is None:
            coverage = metadata.get("constraintCoverage")
            if not isinstance(coverage, dict) or not isinstance(
                coverage.get("renderedKeys"), list
            ):
                raise QedJsonRepairError(
                    "QED metadata lacks constraintCoverage.renderedKeys"
                )
            expected_table_keys = coverage["renderedKeys"]
    if expected_table_keys is None:
        raise QedJsonRepairError("expected QED table keys were not provided")

    expected: dict[str, dict[str, Any]] = {}
    for raw_key in expected_table_keys:
        if not isinstance(raw_key, dict):
            raise QedJsonRepairError("rendered key attestation contains a non-object")
        kind = raw_key.get("kind")
        table_name = raw_key.get("table")
        columns = raw_key.get("columns")
        if (
            kind not in {"primary", "unique"}
            or not isinstance(table_name, str)
            or not isinstance(columns, list)
            or not columns
            or not all(isinstance(column, str) for column in columns)
        ):
            raise QedJsonRepairError(f"malformed rendered key attestation: {raw_key!r}")
        folded_table = table_name.casefold()
        table_expected = expected.setdefault(
            folded_table,
            {"table": table_name, "keys": []},
        )
        if table_expected["table"] != table_name:
            raise QedJsonRepairError(
                f"case-insensitive duplicate rendered table name: {table_name}"
            )
        folded_columns = tuple(column.casefold() for column in columns)
        if len(set(folded_columns)) != len(folded_columns):
            raise QedJsonRepairError(
                f"rendered key repeats a column on table {table_name}: {columns}"
            )
        table_expected["keys"].append({"kind": kind, "columns": list(columns)})

    try:
        document = json.loads(json_path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        raise QedJsonRepairError(f"cannot read QED JSON {json_path}: {exc}") from exc
    if not isinstance(document, dict) or not isinstance(document.get("schemas"), list):
        raise QedJsonRepairError(f"QED JSON has no schema array: {json_path}")
    try:
        set_null_type_repairs = repair_qed_set_null_types(document)
    except QedJsonValidationError as exc:
        raise QedJsonRepairError(str(exc)) from exc

    schemas_by_name: dict[str, dict[str, Any]] = {}
    for raw_schema in document["schemas"]:
        if not isinstance(raw_schema, dict) or not isinstance(
            raw_schema.get("name"), str
        ):
            raise QedJsonRepairError("QED JSON contains a schema without a string name")
        raw_keys = raw_schema.get("key")
        if not isinstance(raw_keys, list) or any(
            not isinstance(key, list)
            or any(
                not isinstance(index, int) or isinstance(index, bool) for index in key
            )
            for key in raw_keys
        ):
            raise QedJsonRepairError(
                f"QED JSON schema {raw_schema['name']} has malformed key indexes"
            )
        folded_name = raw_schema["name"].casefold()
        if folded_name in schemas_by_name:
            raise QedJsonRepairError(
                f"QED JSON contains duplicate schema name {raw_schema['name']}"
            )
        schemas_by_name[folded_name] = raw_schema
        # Never trust a parser-emitted key index: even a table without an
        # expected key must not retain an accidental constraint. Attested keys
        # are injected below after field-order validation.
        raw_schema["key"] = []

    table_attestations: list[dict[str, Any]] = []
    dropped_keys: list[dict[str, Any]] = []
    for folded_table in sorted(expected):
        table_expected = expected[folded_table]
        table_name = table_expected["table"]
        schema = schemas_by_name.get(folded_table)
        if schema is None:
            for expected_key in table_expected["keys"]:
                dropped_keys.append(
                    {
                        "kind": expected_key["kind"],
                        "table": table_name,
                        "columns": expected_key["columns"],
                        "reason": "qed-json-pruned-rendered-key-table",
                        "missingColumns": expected_key["columns"],
                        "nullableColumns": [],
                    }
                )
            table_attestations.append(
                {
                    "table": table_name,
                    "fieldCount": None,
                    "keys": [],
                    "status": "pruned-by-qed-parser",
                }
            )
            continue
        fields = schema.get("fields")
        nullabilities = schema.get("nullable")
        if (
            not isinstance(fields, list)
            or not all(isinstance(field, str) for field in fields)
            or not isinstance(nullabilities, list)
            or len(nullabilities) != len(fields)
            or not all(isinstance(nullable, bool) for nullable in nullabilities)
        ):
            raise QedJsonRepairError(
                f"QED JSON has malformed fields/nullability for table {table_name}"
            )
        field_indexes: dict[str, int] = {}
        for index, field_name in enumerate(fields):
            folded_field = field_name.casefold()
            if folded_field in field_indexes:
                raise QedJsonRepairError(
                    f"QED JSON table {table_name} has duplicate field {field_name}"
                )
            field_indexes[folded_field] = index

        repaired_keys: list[list[int]] = []
        key_attestations: list[dict[str, Any]] = []
        for expected_key in table_expected["keys"]:
            indexes: list[int] = []
            missing_columns: list[str] = []
            nullable_columns: list[str] = []
            for column_name in expected_key["columns"]:
                index = field_indexes.get(column_name.casefold())
                if index is None:
                    missing_columns.append(column_name)
                    continue
                if nullabilities[index]:
                    nullable_columns.append(column_name)
                indexes.append(index)
            if missing_columns or nullable_columns:
                reason = (
                    "qed-json-pruned-rendered-key-column"
                    if missing_columns and not nullable_columns
                    else "qed-json-rendered-key-column-unexpectedly-nullable"
                    if nullable_columns and not missing_columns
                    else "qed-json-rendered-key-not-attested"
                )
                dropped_keys.append(
                    {
                        "kind": expected_key["kind"],
                        "table": table_name,
                        "columns": expected_key["columns"],
                        "reason": reason,
                        "missingColumns": missing_columns,
                        "nullableColumns": nullable_columns,
                    }
                )
                continue
            canonical_indexes = sorted(indexes)
            if canonical_indexes not in repaired_keys:
                repaired_keys.append(canonical_indexes)
            key_attestations.append(
                {
                    "kind": expected_key["kind"],
                    "columns": expected_key["columns"],
                    "jsonIndexes": canonical_indexes,
                }
            )
        repaired_keys.sort()
        schema["key"] = repaired_keys
        table_attestations.append(
            {
                "table": table_name,
                "fieldCount": len(fields),
                "keys": key_attestations,
            }
        )

    attestation = {
        "version": 1,
        "status": (
            "verified-with-conservative-key-drops"
            if dropped_keys
            else "verified-and-normalized"
        ),
        "policy": (
            "source keys withheld during QED planning; all parser key indexes "
            "cleared, then attested keys injected by column name against serialized "
            "QED field indexes"
        ),
        "tables": table_attestations,
        "droppedKeys": dropped_keys,
        "setNullTypeRepairs": set_null_type_repairs,
    }
    try:
        json_path.write_text(
            json.dumps(document, indent=2, ensure_ascii=False, sort_keys=True) + "\n"
        )
    except OSError as exc:
        raise QedJsonRepairError(
            f"cannot write repaired QED JSON {json_path}: {exc}"
        ) from exc

    if metadata is not None and metadata_file is not None:
        coverage = metadata.get("constraintCoverage")
        if not isinstance(coverage, dict):
            raise QedJsonRepairError(
                "QED metadata lacks an object-valued constraintCoverage"
            )
        apply_qed_json_repair_coverage(coverage, attestation)
        active_variant = metadata.get("activeQEDVariant")
        if (
            isinstance(active_variant, str)
            and active_variant != "source-constraint-profile"
        ):
            for field_name in (
                "qedEquivalenceFallback",
                "qedStarExpansionEquivalenceFallback",
                "qedProjectionEquivalenceFallback",
                "qedOpaqueStringEquivalenceFallback",
            ):
                descriptor = metadata.get(field_name)
                if (
                    isinstance(descriptor, dict)
                    and descriptor.get("id") == active_variant
                ):
                    # JSON round-tripping breaks the in-memory sharing used by
                    # direct materialization.  Keep the active descriptor's
                    # coverage synchronized with any conservatively dropped
                    # key so replay cannot restore stale claims.
                    descriptor["constraintCoverage"] = json.loads(json.dumps(coverage))
                    break
        metadata["constraintCompatibility"] = coverage["compatibility"]
        metadata["qedJsonRepair"] = attestation
        metadata["qedJson"] = json_path.name
        try:
            metadata_file.write_text(
                json.dumps(metadata, indent=2, ensure_ascii=False, sort_keys=True)
                + "\n"
            )
        except OSError as exc:
            raise QedJsonRepairError(
                f"cannot record QED JSON repair in {metadata_file}: {exc}"
            ) from exc
    return attestation


def write_qed_keyless_equivalence_variant(
    source_json: str | Path,
    target_json: str | Path,
) -> dict[str, Any]:
    """Write a full-output, constraint-relaxed QED variant for EQ-only retry.

    Removing keys enlarges the set of admissible databases, so a proof of EQ
    remains valid for the source schema.  A counterexample or any other result
    from this variant is intentionally not authoritative.
    """

    source_json = Path(source_json)
    target_json = Path(target_json)
    source_validation = validate_qed_json(source_json)
    try:
        document = json.loads(source_json.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        raise QedJsonValidationError(
            f"cannot read QED JSON {source_json}: {exc}"
        ) from exc
    removed: list[dict[str, Any]] = []
    for schema in document["schemas"]:
        keys = schema.get("key")
        if keys:
            removed.append({"table": schema["name"], "jsonKeys": keys})
        schema["key"] = []
    write_text(
        target_json,
        json.dumps(document, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
    )
    target_validation = validate_qed_json(target_json)
    if (
        target_validation["outputArity"] != source_validation["outputArity"]
        or target_validation["outputTypes"] != source_validation["outputTypes"]
    ):
        target_json.unlink(missing_ok=True)
        raise QedJsonValidationError("keyless QED variant changed the output signature")
    return {
        "status": "verified-full-output-keyless-variant",
        "changed": bool(removed),
        "removedKeys": removed,
        "sourceSha256": source_validation["sha256"],
        "variantSha256": target_validation["sha256"],
        "outputArity": target_validation["outputArity"],
        "outputTypes": target_validation["outputTypes"],
        "resultPolicy": "accept-eq-only",
    }


def extract_qed_query_pair(sql_text: str) -> dict[str, Any]:
    """Extract exactly two queries after a CREATE/DECLARE-only preamble."""

    statements = split_sql_statements(sql_text)
    schema_statements: list[str] = []
    declaration_statements: list[str] = []
    preamble_statements: list[str] = []
    queries: list[str] = []
    for statement in statements:
        visible = strip_sql_comments(statement).lstrip()
        if not visible.strip():
            continue
        is_schema = bool(re.match(r"(?is)^CREATE\s+TABLE\b", visible))
        is_declaration = bool(re.match(r"(?is)^DECLARE\s+SCALAR\s+FUNCTION\b", visible))
        if is_schema or is_declaration:
            if queries:
                raise QedJsonValidationError(
                    "QED CREATE/DECLARE statement appears after a query"
                )
            (schema_statements if is_schema else declaration_statements).append(
                statement
            )
            preamble_statements.append(statement)
            continue
        queries.append(statement)
    if len(queries) != 2:
        raise QedJsonValidationError(
            "QED input must contain exactly two non-DDL query statements; "
            f"found {len(queries)}"
        )
    return {
        "queries": queries,
        "schemaText": (
            ";\n".join(schema_statements) + ";\n" if schema_statements else ""
        ),
        "preambleText": (
            ";\n".join(preamble_statements) + ";\n" if preamble_statements else ""
        ),
        "declarations": declaration_statements,
        "statementCount": (
            len(schema_statements) + len(declaration_statements) + len(queries)
        ),
        "queryStatementCount": len(queries),
    }


def validate_qed_input_bindings(
    metadata_path: str | Path,
    fallback_id: str | None = None,
) -> dict[str, Any]:
    """Bind reusable parser JSON to the exact source and active variant SQL."""

    metadata_path = Path(metadata_path)
    try:
        metadata = json.loads(metadata_path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        raise QedJsonValidationError(
            f"cannot read QED metadata {metadata_path}: {exc}"
        ) from exc
    case_dir = metadata_path.parent
    stored_source_schema_authority = metadata.get("sourceSchemaTypeAuthority")
    if stored_source_schema_authority is not None:
        benchmark_id = metadata.get("sourceBenchmark")
        case_id = metadata.get("sourceCase")
        if not isinstance(benchmark_id, str) or not isinstance(case_id, str):
            raise QedJsonValidationError(
                "QED raw source schema authority lacks canonical case identity"
            )
        canonical_source_schema_authority = (
            load_canonical_qed_source_schema_type_authority(benchmark_id, case_id)
        )
        if stored_source_schema_authority != canonical_source_schema_authority:
            raise QedJsonValidationError(
                "QED raw source schema type authority is stale or malformed"
            )
    normalization = metadata.get("normalizationForSolverRun")
    if isinstance(normalization, dict):
        for side in ("before", "after"):
            side_report = normalization.get(side)
            alias_report = (
                side_report.get("qedBaseTableColumnAliasOrder")
                if isinstance(side_report, dict)
                else None
            )
            if isinstance(alias_report, dict) and alias_report.get("status") == (
                "unsupported"
            ):
                raise QedJsonValidationError(
                    "QED base-table column-alias ordering is unsupported on "
                    f"{side}: {alias_report.get('reason')}"
                )

    def attest_file(name: Any, expected: Any, label: str) -> dict[str, str]:
        if (
            not isinstance(name, str)
            or Path(name).name != name
            or not isinstance(expected, str)
        ):
            raise QedJsonValidationError(f"QED metadata lacks {label} digest binding")
        path = case_dir / name
        if not path.is_file():
            raise QedJsonValidationError(f"QED {label} input is missing: {name}")
        actual = sha256_path(path)
        if actual != expected:
            raise QedJsonValidationError(
                f"QED {label} input digest does not match metadata: {name}"
            )
        return {"input": name, "sha256": actual}

    source = attest_file(
        metadata.get("qedInput"),
        metadata.get("qedInputSha256"),
        "source-profile",
    )
    result: dict[str, Any] = {"source": source}
    if fallback_id is None or fallback_id == "source-constraint-profile":
        return result

    descriptors = (
        metadata.get("qedEquivalenceFallback"),
        metadata.get("qedStarExpansionEquivalenceFallback"),
        metadata.get("qedProjectionEquivalenceFallback"),
        metadata.get("qedOpaqueStringEquivalenceFallback"),
    )
    fallback = next(
        (
            item
            for item in descriptors
            if isinstance(item, dict) and item.get("id") == fallback_id
        ),
        None,
    )
    if (
        not isinstance(fallback, dict)
        or fallback.get("resultPolicy") != "accept-eq-only"
    ):
        raise QedJsonValidationError(
            f"QED metadata lacks EQ-only variant {fallback_id!r}"
        )
    result["variantSource"] = attest_file(
        fallback.get("sourceInput"),
        fallback.get("sourceInputSha256"),
        "variant-source",
    )
    result["variant"] = attest_file(
        fallback.get("input"),
        fallback.get("inputSha256"),
        "variant",
    )
    if fallback_id in {
        "ast-star-expanded-equivalence",
        "opaque-varchar-equality-integer-abstraction",
    }:
        benchmark_id = metadata.get("sourceBenchmark")
        case_id = metadata.get("sourceCase")
        if not isinstance(benchmark_id, str) or not isinstance(case_id, str):
            raise QedJsonValidationError(
                "QED Calcite-authoritative fallback lacks source case identity"
            )
        source_path = case_dir / result["variantSource"]["input"]
        pair = extract_qed_query_pair(source_path.read_text())
        queries = pair["queries"]
        tables = parse_schema(
            pair["schemaText"],
            clean_identifier=clean_identifier,
            parse_table=parse_table,
        )
        opaque_admission = None
        if fallback_id == "opaque-varchar-equality-integer-abstraction":
            source_coverage = metadata.get("sourceConstraintCoverage")
            if stored_source_schema_authority is None or not isinstance(
                source_coverage, dict
            ):
                raise QedJsonValidationError(
                    "QED opaque fallback lacks raw schema/constraint authority"
                )
            opaque_admission = build_qed_opaque_source_admission(
                tables,
                queries,
                source_coverage,
                benchmark_id,
                case_id,
            )
            rebuilt_authority = opaque_admission["calciteAuthority"]
            if (
                fallback.get("sourceSchemaTypeAuthority")
                != opaque_admission["rawSourceSchemaAuthority"]
                or fallback.get("sourceColumnUseClosure")
                != opaque_admission["baseUseClosure"]
                or fallback.get("sourceColumnProjection")
                != opaque_admission["sourceColumnProjection"]
                or fallback.get("constraintCoverage")
                != opaque_admission["constraintCoverage"]
            ):
                raise QedJsonValidationError(
                    "QED opaque raw-type/use-closure admission is stale"
                )
        else:
            rebuilt_authority = load_qed_calcite_output_attestation(
                benchmark_id,
                case_id,
                queries,
                tables,
            )
        stored_authority = fallback.get("calciteAuthority")
        if stored_authority != rebuilt_authority:
            raise QedJsonValidationError(
                "QED fallback Calcite authority is stale or malformed"
            )
        expected_paths = [
            str(
                Path("benchmarks/core/.generated/calcite-ir")
                / benchmark_id
                / case_id
                / f"{side}.calcite-ir.json"
            )
            for side in ("before", "after")
        ]
        authority_sides = rebuilt_authority.get("sides")
        if (
            not isinstance(authority_sides, list)
            or [item.get("side") for item in authority_sides] != ["before", "after"]
            or [item.get("path") for item in authority_sides] != expected_paths
        ):
            raise QedJsonValidationError(
                "QED fallback Calcite authority paths are not canonical"
            )
        if fallback_id == "ast-star-expanded-equivalence":
            expected_types = rebuilt_authority["sourceOutputTypes"]
            if fallback.get("expectedOutputTypes") != expected_types:
                raise QedJsonValidationError(
                    "QED star fallback expected output types are stale"
                )
            rebuilt_source_star = analyze_qed_source_star_provenance(
                tables,
                queries,
                rebuilt_authority,
            )
            rebuilt_source_star["outputArity"] = rebuilt_authority["outputArity"]
            if fallback.get("sourceStarProvenance") != rebuilt_source_star:
                raise QedJsonValidationError(
                    "QED star fallback source provenance is stale or malformed"
                )
        else:
            if any(
                type_name.startswith(("CHAR", "TEXT", "STRING"))
                for side in authority_sides
                for type_name in side["outputTypes"]
            ):
                raise QedJsonValidationError(
                    "opaque-string abstraction is restricted to exact VARCHAR semantics"
                )
            expected_types = [
                "INTEGER" if type_name.startswith("VARCHAR") else type_name
                for type_name in rebuilt_authority["sourceOutputTypes"]
            ]
            if fallback.get("expectedTransformedOutputTypes") != expected_types:
                raise QedJsonValidationError(
                    "QED opaque fallback expected output types are stale"
                )
            rebuilt_source_star = analyze_qed_source_star_provenance(
                tables,
                queries,
                rebuilt_authority,
            )
            expected_source_star = (
                rebuilt_source_star
                if rebuilt_source_star.get("starSideCount", 0) > 0
                else None
            )
            if fallback.get("sourceStarProvenance") != expected_source_star:
                raise QedJsonValidationError(
                    "QED opaque source-star provenance is stale or malformed"
                )
        result["calciteAuthority"] = rebuilt_authority
    result["fallback"] = fallback
    return result


def activate_qed_equivalence_fallback(
    metadata_path: str | Path,
    fallback_id: str,
) -> dict[str, Any]:
    """Record that the canonical qed.json came from an attested EQ fallback."""

    metadata_path = Path(metadata_path)
    try:
        metadata = json.loads(metadata_path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        raise QedJsonValidationError(
            f"cannot read QED metadata {metadata_path}: {exc}"
        ) from exc
    fallbacks = (
        metadata.get("qedEquivalenceFallback"),
        metadata.get("qedStarExpansionEquivalenceFallback"),
        metadata.get("qedProjectionEquivalenceFallback"),
        metadata.get("qedOpaqueStringEquivalenceFallback"),
    )
    fallback = next(
        (
            candidate
            for candidate in fallbacks
            if isinstance(candidate, dict) and candidate.get("id") == fallback_id
        ),
        None,
    )
    if (
        not isinstance(fallback, dict)
        or fallback.get("resultPolicy") != "accept-eq-only"
        or not isinstance(fallback.get("constraintCoverage"), dict)
    ):
        raise QedJsonValidationError(
            f"QED metadata does not attest equivalence fallback {fallback_id!r}"
        )
    validate_qed_input_bindings(metadata_path, fallback_id)
    metadata["activeQEDVariant"] = fallback_id
    metadata["constraintCoverage"] = fallback["constraintCoverage"]
    metadata["constraintCompatibility"] = fallback["constraintCoverage"].get(
        "compatibility", "conservative-relaxation"
    )
    metadata_path.write_text(
        json.dumps(metadata, indent=2, ensure_ascii=False, sort_keys=True) + "\n"
    )
    return fallback


def record_qed_keyless_equivalence_variant(
    metadata_path: str | Path,
    attestation: dict[str, Any],
) -> dict[str, Any]:
    metadata_path = Path(metadata_path)
    try:
        metadata = json.loads(metadata_path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        raise QedJsonValidationError(
            f"cannot read QED metadata {metadata_path}: {exc}"
        ) from exc
    fallback = metadata.get("qedKeylessEquivalenceFallback")
    if (
        not isinstance(fallback, dict)
        or fallback.get("resultPolicy") != "accept-eq-only"
        or fallback.get("generatedJson") != "qed-equivalence-keyless.json"
    ):
        raise QedJsonValidationError(
            "QED metadata does not attest the keyless EQ retry"
        )
    fallback["attestation"] = attestation
    metadata_path.write_text(
        json.dumps(metadata, indent=2, ensure_ascii=False, sort_keys=True) + "\n"
    )
    return fallback


def record_qed_projection_equivalence_fallback(
    metadata_path: str | Path,
    fallback: dict[str, Any],
) -> None:
    metadata_path = Path(metadata_path)
    try:
        metadata = json.loads(metadata_path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        raise QedJsonValidationError(
            f"cannot read QED metadata {metadata_path}: {exc}"
        ) from exc
    if (
        fallback.get("id") != "ast-column-projected-equivalence"
        or fallback.get("resultPolicy") != "accept-eq-only"
        or not isinstance(fallback.get("constraintCoverage"), dict)
        or not all(
            isinstance(fallback.get(field), str)
            for field in (
                "input",
                "inputSha256",
                "sourceInput",
                "sourceInputSha256",
            )
        )
    ):
        raise QedJsonValidationError("malformed QED projection equivalence fallback")
    metadata["qedProjectionEquivalenceFallback"] = fallback
    metadata_path.write_text(
        json.dumps(metadata, indent=2, ensure_ascii=False, sort_keys=True) + "\n"
    )


def record_qed_star_expansion_equivalence_fallback(
    metadata_path: str | Path,
    fallback: dict[str, Any],
) -> None:
    metadata_path = Path(metadata_path)
    try:
        metadata = json.loads(metadata_path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        raise QedJsonValidationError(
            f"cannot read QED metadata {metadata_path}: {exc}"
        ) from exc
    source_star = fallback.get("sourceStarProvenance")
    if (
        fallback.get("id") != "ast-star-expanded-equivalence"
        or fallback.get("resultPolicy") != "accept-eq-only"
        or not isinstance(fallback.get("constraintCoverage"), dict)
        or not isinstance(fallback.get("dependencyAttestation"), dict)
        or not isinstance(fallback.get("calciteAuthority"), dict)
        or not isinstance(fallback.get("expectedOutputTypes"), list)
        or not isinstance(source_star, dict)
        or source_star.get("status") != "verified-source-star-provenance-pair"
        or source_star.get("starSideCount", 0) <= 0
        or not all(
            isinstance(fallback.get(field), str)
            for field in (
                "input",
                "inputSha256",
                "sourceInput",
                "sourceInputSha256",
            )
        )
    ):
        raise QedJsonValidationError(
            "malformed QED star-expansion equivalence fallback"
        )
    metadata["qedStarExpansionEquivalenceFallback"] = fallback
    metadata_path.write_text(
        json.dumps(metadata, indent=2, ensure_ascii=False, sort_keys=True) + "\n"
    )


def record_qed_opaque_string_equivalence_fallback(
    metadata_path: str | Path,
    fallback: dict[str, Any],
) -> None:
    metadata_path = Path(metadata_path)
    try:
        metadata = json.loads(metadata_path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        raise QedJsonValidationError(
            f"cannot read QED metadata {metadata_path}: {exc}"
        ) from exc
    source_star = fallback.get("sourceStarProvenance")
    benchmark_id = metadata.get("sourceBenchmark")
    case_id = metadata.get("sourceCase")
    stored_source_authority = metadata.get("sourceSchemaTypeAuthority")
    canonical_source_authority = (
        load_canonical_qed_source_schema_type_authority(benchmark_id, case_id)
        if isinstance(benchmark_id, str) and isinstance(case_id, str)
        else None
    )
    if (
        fallback.get("id") != "opaque-varchar-equality-integer-abstraction"
        or fallback.get("resultPolicy") != "accept-eq-only"
        or not isinstance(fallback.get("constraintCoverage"), dict)
        or not isinstance(fallback.get("dependencyAttestation"), dict)
        or not isinstance(fallback.get("calciteAuthority"), dict)
        or not isinstance(fallback.get("expectedTransformedOutputTypes"), list)
        or not isinstance(fallback.get("sourceColumnUseClosure"), (dict, type(None)))
        or not isinstance(fallback.get("sourceColumnProjection"), (dict, type(None)))
        or stored_source_authority != canonical_source_authority
        or fallback.get("sourceSchemaTypeAuthority") != canonical_source_authority
        or (
            source_star is not None
            and (
                not isinstance(source_star, dict)
                or source_star.get("status") != "verified-source-star-provenance-pair"
                or not isinstance(source_star.get("starSideCount"), int)
                or source_star.get("starSideCount", 0) <= 0
            )
        )
        or not all(
            isinstance(fallback.get(field), str)
            for field in (
                "input",
                "inputSha256",
                "sourceInput",
                "sourceInputSha256",
            )
        )
    ):
        raise QedJsonValidationError("malformed QED opaque-string fallback")
    metadata["qedOpaqueStringEquivalenceFallback"] = fallback
    metadata_path.write_text(
        json.dumps(metadata, indent=2, ensure_ascii=False, sort_keys=True) + "\n"
    )


def classify_qed_parser_problem(parser_status: dict[str, Any]) -> dict[str, str] | None:
    validation = parser_status.get("jsonValidation")
    # SQLJSONParser writes the complete JSON document before invoking its
    # legacy Racket exporter.  A diagnostic after a fresh document passes our
    # structural/query-signature validation is therefore not a JSON parser
    # failure and must not hide a prover-supported case (e.g. EXCEPT,
    # INTERSECT, or DATE literals).
    if (
        isinstance(validation, dict)
        and validation.get("status") == "verified-complete-query-pair"
        and parser_status.get("artifactsClearedBeforeRun") is True
    ):
        return None
    validation_error = (
        str(validation.get("message") or "QED JSON validation failed")
        if isinstance(validation, dict) and validation.get("status") == "error"
        else None
    )
    # Signature disagreement is itself the actionable trigger for the exact
    # star-expansion retry, even when the legacy exporter later prints another
    # diagnostic.
    if validation_error and validation_error.startswith(
        "QED query output signatures disagree:"
    ):
        return {"kind": "parser-error", "message": validation_error}
    text = "\n".join(
        str(parser_status.get(key, "")) for key in ("stdoutTail", "stderrTail")
    )
    if not text.strip():
        return None
    patterns = [
        ("parser-error", r"charset is null for VARCHAR"),
        ("unsupported", r"UnsupportedOperationException:\s*([^\n]+)"),
        ("unsupported", r"Not supported [^\n]+"),
        ("parser-error", r"CalciteContextException:\s*([^\n]+)"),
        ("parser-error", r"ParseException:\s*([^\n]+)"),
        ("parser-error", r"Encountered [^\n]+"),
        ("parser-error", r"Correlation ID not declared"),
        ("parser-error", r"NullPointerException:\s*([^\n]+)"),
        ("parser-error", r"Exception:\s*([^\n]+)"),
        ("parser-error", r"RuntimeException:\s*([^\n]+)"),
    ]
    for kind, pattern in patterns:
        match = re.search(pattern, text, re.IGNORECASE)
        if match:
            return {
                "kind": kind,
                "message": match.group(1).strip()
                if match.groups()
                else match.group(0).strip(),
            }
    if validation_error:
        return {"kind": "parser-error", "message": validation_error}
    return None


def classify_qed_parser_warning(parser_status: dict[str, Any]) -> dict[str, str] | None:
    """Return a non-blocking post-JSON exporter diagnostic, when present."""

    validation = parser_status.get("jsonValidation")
    if (
        not isinstance(validation, dict)
        or validation.get("status") != "verified-complete-query-pair"
        or parser_status.get("artifactsClearedBeforeRun") is not True
    ):
        return None
    text = "\n".join(
        str(parser_status.get(key, "")) for key in ("stdoutTail", "stderrTail")
    )
    for pattern in (
        r"UnsupportedOperationException:\s*([^\n]+)",
        r"RuntimeException:\s*([^\n]+)",
        r"Exception:\s*([^\n]+)",
    ):
        match = re.search(pattern, text, re.IGNORECASE)
        if match:
            return {
                "kind": "post-json-racket-export-warning",
                "message": match.group(1).strip(),
            }
    return None


def is_qed_varchar_charset_problem(problem: dict[str, Any] | None) -> bool:
    """Recognize Calcite/QED's NOT NULL VARCHAR charset frontend bug."""

    return bool(
        isinstance(problem, dict)
        and re.search(
            r"charset is null for VARCHAR", str(problem.get("message", "")), re.I
        )
    )


def is_qed_output_signature_problem(problem: dict[str, Any] | None) -> bool:
    return bool(
        isinstance(problem, dict)
        and str(problem.get("message", "")).startswith(
            "QED query output signatures disagree:"
        )
    )


def build_metadata(
    config: dict[str, Any], case: Any, flat_case_id: str
) -> dict[str, Any]:
    defaults = config["defaults"]
    benchmark = case.benchmark
    return {
        "sourceBenchmark": benchmark["id"],
        "sourceCase": case.case_id,
        "flatCaseId": flat_case_id,
        "source": case.source_metadata,
        "schemaScope": benchmark["schemaScope"],
        "constraintScope": benchmark.get("constraintScope", "none"),
        "constraints": case.constraints,
        "adapter": benchmark.get("adapter", defaults.get("adapter", "none")),
        "sourceDialect": case.source_dialect or benchmark.get("sourceDialect"),
        "readDialect": case.read_dialect or benchmark.get("readDialect"),
        "writeDialect": "postgres",
        "frontendTargetDialectPurpose": "qed-calcite-parser",
        "semanticProfile": benchmark.get(
            "semanticProfile", defaults["semanticProfile"]
        ),
        "bagSemantics": benchmark.get("bagSemantics", defaults["bagSemantics"]),
        "nullSemantics": benchmark.get("nullSemantics", defaults["nullSemantics"]),
        "featureTags": case.feature_tags,
    }


def render_qed_schema(
    schema_sql: str,
    query_sql: str,
    quote_identifiers: bool,
    constraints: Any = None,
    *,
    relax_not_null_varchar: bool = False,
) -> tuple[str, dict[str, Any]]:
    all_tables = parse_schema(
        schema_sql,
        clean_identifier=clean_identifier,
        parse_table=parse_table,
    )
    tables = select_schema_tables(all_tables, query_sql)
    coverage: dict[str, Any] = {
        "compatibility": "exact",
        "policy": (
            "QED receives every column of each selected source relation. "
            "CREATE TABLE exposes NOT NULL but deliberately omits PRIMARY/UNIQUE "
            "during Calcite planning. Safe source keys are attested here and "
            "injected by repair_qed_json only after the parser fixes its final "
            "serialized field order. Unsupported constraints are conservative "
            "relaxations enumerated below."
        ),
        "applied": [entry for table in tables for entry in table.applied_constraints],
        "omitted": [entry for table in tables for entry in table.omitted_constraints],
    }
    apply_constraint_metadata(tables, all_tables, constraints, coverage)
    post_parse_keys = [
        constraint_entry(kind, "post-parse-attestation", table.name, key)
        for table in tables
        for kind, keys in (
            ("primary", table.primary_keys),
            ("unique", table.unique_keys),
        )
        for key in keys
    ]
    coverage["postParseKeys"] = post_parse_keys
    # Compatibility alias for existing one-click runners. These keys are no
    # longer rendered in qed.sql; they are candidates for post-parse injection.
    coverage["renderedKeys"] = post_parse_keys
    coverage["keyApplicationStage"] = "post-parse-json"

    relaxed_not_null_columns = {
        (table.name.casefold(), column.name.casefold()): (table.name, column.name)
        for table in tables
        for column in table.columns
        if relax_not_null_varchar
        and column.not_null
        and column.type_sql.upper().startswith("VARCHAR")
    }
    if relaxed_not_null_columns:
        coverage["applied"] = [
            entry
            for entry in coverage["applied"]
            if not (
                isinstance(entry, dict)
                and entry.get("kind") == "not_null"
                and isinstance(entry.get("table"), str)
                and isinstance(entry.get("columns"), list)
                and len(entry["columns"]) == 1
                and isinstance(entry["columns"][0], str)
                and (
                    entry["table"].casefold(),
                    entry["columns"][0].casefold(),
                )
                in relaxed_not_null_columns
            )
        ]
        coverage["omitted"].extend(
            constraint_entry(
                "not_null",
                "qed-equivalence-fallback",
                table_name,
                [column_name],
                "qed-varchar-nullability-relaxed-for-eq-proof",
            )
            for table_name, column_name in relaxed_not_null_columns.values()
        )
        coverage["equivalenceOnlyRelaxation"] = {
            "reason": "qed-calcite-not-null-varchar-charset-bug",
            "acceptedResult": "EQ",
            "soundness": (
                "Removing NOT NULL enlarges the admitted database class. "
                "An EQ proof over the enlarged class implies EQ under the source constraints; "
                "no non-EQ conclusion may be taken from this profile."
            ),
        }

    rendered = []
    for table in tables:
        declarations = []
        for column in table.columns:
            relax_column = (
                table.name.casefold(),
                column.name.casefold(),
            ) in relaxed_not_null_columns
            suffix = " NOT NULL" if column.not_null and not relax_column else ""
            declarations.append(
                f"  {render_identifier(column.name, quote_identifiers)} {column.type_sql}{suffix}"
            )
        if not declarations:
            continue
        rendered.append(
            f"CREATE TABLE {render_identifier(table.name, quote_identifiers)} (\n"
            + ",\n".join(declarations)
            + "\n);\n"
        )
    coverage["applied"] = deduplicate_constraint_entries(coverage["applied"])
    coverage["omitted"] = deduplicate_constraint_entries(coverage["omitted"])
    if coverage["omitted"]:
        coverage["compatibility"] = "conservative-relaxation"
    return "\n".join(rendered), coverage


def select_schema_tables(tables: list[Table], query_sql: str) -> list[Table]:
    """Select source relations without ever pruning their row type.

    QED needs a smaller application schema for some WeTune inputs, but column
    pruning is not semantics preserving in the presence of [SELECT *] or row
    multiplicities that differ only in a dropped column.  Relation selection is
    therefore conservative at the table boundary: once selected, a relation is
    rendered with every source column.
    """

    aliases = collect_table_aliases(query_sql)
    referenced_tables = {table.lower() for table in aliases.values()}
    referenced_tables.update(
        table.name.lower()
        for table in tables
        if identifier_is_referenced(query_sql, table.name)
    )
    selected = [
        table
        for table in tables
        if not referenced_tables or table.name.lower() in referenced_tables
    ]
    return selected or list(tables)


def _projection_witness_column(table: Table) -> Column:
    """Choose one non-string payload when a scan needs only bag cardinality."""

    for column in table.columns:
        if not column.type_sql.upper().startswith("VARCHAR"):
            return column
    if not table.columns:
        raise QedJsonValidationError(f"cannot project column-free table {table.name}")
    return table.columns[0]


def _exact_query_text(sql: str) -> str:
    # Benchmark SQL commonly carries generator comments that the QED input
    # deliberately strips.  Bind the executable token stream while ignoring
    # comments only; quoted literals remain byte-preserved by the shared lexer.
    value = strip_sql_comments(sql).strip()
    return value[:-1].rstrip() if value.endswith(";") else value


def _qed_schema_type_name(type_sql: str) -> str:
    normalized = normalize_type_for_qed(type_sql)
    return "VARCHAR" if normalized.startswith("VARCHAR") else normalized


def load_qed_calcite_output_attestation(
    benchmark_id: str,
    case_id: str,
    queries: list[str],
    tables: list[Table],
    *,
    raw_source_schema_authority: dict[str, Any] | None = None,
) -> dict[str, Any]:
    """Bind an abstraction to exact Calcite SQL/schema and ordered root types."""

    if len(queries) != 2:
        raise QedJsonValidationError("Calcite attestation requires exactly two queries")
    generated_root = (ROOT / "benchmarks/core/.generated/calcite-ir").resolve()
    case_root = (generated_root / benchmark_id / case_id).resolve()
    try:
        case_root.relative_to(generated_root)
    except ValueError as exc:
        raise QedJsonValidationError(
            "Calcite attestation case path escapes its root"
        ) from exc
    sides: list[dict[str, Any]] = []
    selected_schema = [
        {
            "name": table.name,
            "columns": [
                {"name": column.name, "type": _qed_schema_type_name(column.type_sql)}
                for column in table.columns
            ],
        }
        for table in tables
    ]
    raw_tables = None
    if raw_source_schema_authority is not None:
        if (
            raw_source_schema_authority.get("status")
            != "verified-ordered-raw-source-schema-types"
            or not isinstance(raw_source_schema_authority.get("schemaSha256"), str)
            or not isinstance(raw_source_schema_authority.get("tables"), list)
        ):
            raise QedJsonValidationError(
                "projected Calcite authority lacks raw source schema types"
            )
        raw_tables = {
            table.get("name").casefold(): table
            for table in raw_source_schema_authority["tables"]
            if isinstance(table, dict) and isinstance(table.get("name"), str)
        }
    for label, query in zip(("before", "after"), queries):
        path = case_root / f"{label}.calcite-ir.json"
        try:
            document = json.loads(path.read_text())
        except (OSError, json.JSONDecodeError) as exc:
            raise QedJsonValidationError(
                f"exact Calcite IR is unavailable for {benchmark_id}/{case_id}: {exc}"
            ) from exc
        ir_queries = document.get("queries") if isinstance(document, dict) else None
        ir_schema = document.get("schema") if isinstance(document, dict) else None
        if not isinstance(ir_queries, list) or len(ir_queries) != 1:
            raise QedJsonValidationError(
                "Calcite IR does not contain exactly one query"
            )
        ir_query = ir_queries[0]
        if (
            not isinstance(ir_query, dict)
            or not isinstance(ir_query.get("sql"), str)
            or _exact_query_text(ir_query["sql"]) != _exact_query_text(query)
        ):
            raise QedJsonValidationError(
                "Calcite IR SQL is not byte-bound to QED input"
            )
        if not isinstance(ir_schema, list):
            raise QedJsonValidationError("Calcite IR schema is malformed")
        by_table = {
            item.get("name").casefold(): item
            for item in ir_schema
            if isinstance(item, dict) and isinstance(item.get("name"), str)
        }
        for expected_table in selected_schema:
            actual_table = by_table.get(expected_table["name"].casefold())
            actual_columns = (
                actual_table.get("columns") if isinstance(actual_table, dict) else None
            )
            if raw_tables is None:
                if not isinstance(actual_columns, list) or len(actual_columns) != len(
                    expected_table["columns"]
                ):
                    raise QedJsonValidationError(
                        "Calcite IR schema row shape disagrees"
                    )
                for expected_column, actual_column in zip(
                    expected_table["columns"], actual_columns
                ):
                    if (
                        not isinstance(actual_column, dict)
                        or not isinstance(actual_column.get("name"), str)
                        or actual_column["name"].casefold()
                        != expected_column["name"].casefold()
                        or actual_column.get("type") != expected_column["type"]
                    ):
                        raise QedJsonValidationError(
                            "Calcite IR schema column/type disagrees with QED DDL"
                        )
            else:
                raw_table = raw_tables.get(expected_table["name"].casefold())
                raw_columns = (
                    raw_table.get("columns") if isinstance(raw_table, dict) else None
                )
                if (
                    not isinstance(actual_columns, list)
                    or not isinstance(raw_columns, list)
                    or len(actual_columns) != len(raw_columns)
                    or any(
                        not isinstance(actual, dict)
                        or not isinstance(actual.get("name"), str)
                        or not isinstance(raw, dict)
                        or not isinstance(raw.get("name"), str)
                        or actual["name"].casefold() != raw["name"].casefold()
                        for actual, raw in zip(actual_columns, raw_columns)
                    )
                ):
                    raise QedJsonValidationError(
                        "Calcite IR schema names/order disagree with raw source DDL"
                    )
                raw_names = {
                    column["name"].casefold()
                    for column in raw_columns
                    if isinstance(column, dict) and isinstance(column.get("name"), str)
                }
                if any(
                    column["name"].casefold() not in raw_names
                    for column in expected_table["columns"]
                ):
                    raise QedJsonValidationError(
                        "projected QED schema is outside raw source DDL"
                    )
        rel = ir_query.get("rel")
        row_type = rel.get("rowType") if isinstance(rel, dict) else None
        if (
            not isinstance(row_type, list)
            or not row_type
            or any(
                not isinstance(field, dict) or not isinstance(field.get("type"), str)
                for field in row_type
            )
        ):
            raise QedJsonValidationError("Calcite root has no ordered output signature")
        # Preserve every semantic output-type modifier exported by Calcite.
        # Presentation names are not part of the ordered value signature, and
        # nullability is kept for audit but (as in the Cosette admission gate)
        # is not itself treated as an observable output attribute.  In
        # particular, precision/scale/typmod fields must never be collapsed to
        # the bare SQL type name before the two source programs are compared.
        output_signature = [
            {key: field[key] for key in sorted(field) if key != "name"}
            for field in row_type
        ]
        comparable_signature = [
            {key: value for key, value in field.items() if key != "nullable"}
            for field in output_signature
        ]
        output_types = [field["type"] for field in row_type]
        sides.append(
            {
                "side": label,
                "path": str(path.relative_to(ROOT.resolve())),
                "sha256": sha256_path(path),
                "embeddedSqlSha256": hashlib.sha256(
                    ir_query["sql"].encode()
                ).hexdigest(),
                "selectedSchemaSha256": hashlib.sha256(
                    json.dumps(selected_schema, sort_keys=True).encode()
                ).hexdigest(),
                "schemaBindingPolicy": (
                    "exact-qed-type-and-row-shape"
                    if raw_tables is None
                    else "raw-source-type-digest-plus-exact-ir-name-order"
                ),
                "sourceSchemaSha256": (
                    None
                    if raw_source_schema_authority is None
                    else raw_source_schema_authority["schemaSha256"]
                ),
                "outputSignature": output_signature,
                "comparableOutputSignature": comparable_signature,
                "outputTypes": output_types,
            }
        )
    if sides[0]["comparableOutputSignature"] != sides[1]["comparableOutputSignature"]:
        raise QedJsonValidationError(
            "authoritative ordered Calcite output signatures disagree before abstraction"
        )
    return {
        "authority": "exact-generated-calcite-ir",
        "schemaTypeAuthority": (
            "calcite-and-qed-ddl"
            if raw_source_schema_authority is None
            else "digest-bound-raw-source-ddl"
        ),
        "orderedTypesEqual": True,
        "sides": sides,
        "sourceOutputSignature": sides[0]["outputSignature"],
        "sourceOutputTypes": sides[0]["outputTypes"],
        "outputArity": len(sides[0]["outputTypes"]),
    }


def _load_qed_canonical_calcite_rels(
    authority: dict[str, Any],
    tables: list[Table],
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    """Reload the exact relational trees bound by a Calcite authority report."""

    sides = authority.get("sides") if isinstance(authority, dict) else None
    if (
        not isinstance(sides, list)
        or len(sides) != 2
        or [side.get("side") for side in sides if isinstance(side, dict)]
        != ["before", "after"]
    ):
        raise QedJsonValidationError("Calcite authority has no ordered side pair")
    generated_root = (ROOT / "benchmarks/core/.generated/calcite-ir").resolve()
    rels: list[dict[str, Any]] = []
    selected_schemas: list[list[dict[str, Any]]] = []
    for expected_side, side in zip(("before", "after"), sides):
        relative = side.get("path")
        expected_sha = side.get("sha256")
        if not isinstance(relative, str) or not isinstance(expected_sha, str):
            raise QedJsonValidationError("Calcite authority lacks a path digest")
        path = (ROOT / relative).resolve()
        try:
            path.relative_to(generated_root)
        except ValueError as exc:
            raise QedJsonValidationError(
                "Calcite authority path escapes its canonical root"
            ) from exc
        if path.name != f"{expected_side}.calcite-ir.json":
            raise QedJsonValidationError("Calcite authority side path is non-canonical")
        if not path.is_file() or sha256_path(path) != expected_sha:
            raise QedJsonValidationError("Calcite authority file digest is stale")
        try:
            document = json.loads(path.read_text())
        except (OSError, json.JSONDecodeError) as exc:
            raise QedJsonValidationError(
                f"cannot reload Calcite authority relation: {exc}"
            ) from exc
        queries = document.get("queries") if isinstance(document, dict) else None
        raw_schema = document.get("schema") if isinstance(document, dict) else None
        rel = (
            queries[0].get("rel")
            if isinstance(queries, list)
            and len(queries) == 1
            and isinstance(queries[0], dict)
            else None
        )
        if not isinstance(rel, dict) or not isinstance(raw_schema, list):
            raise QedJsonValidationError(
                "Calcite authority has no exact relational tree"
            )
        by_table = {
            item.get("name").casefold(): item
            for item in raw_schema
            if isinstance(item, dict) and isinstance(item.get("name"), str)
        }
        selected_schema = []
        for table in tables:
            actual = by_table.get(table.name.casefold())
            columns = actual.get("columns") if isinstance(actual, dict) else None
            if not isinstance(columns, list) or any(
                not isinstance(column, dict)
                or not isinstance(column.get("name"), str)
                or not isinstance(column.get("type"), str)
                for column in columns
            ):
                raise QedJsonValidationError(
                    "Calcite authority schema is unavailable for source provenance"
                )
            selected_schema.append(
                {
                    "name": actual["name"],
                    "columns": [
                        {"name": column["name"], "type": column["type"]}
                        for column in columns
                    ],
                }
            )
        rels.append(rel)
        selected_schemas.append(selected_schema)
    if selected_schemas[0] != selected_schemas[1]:
        raise QedJsonValidationError(
            "Calcite authority schemas disagree between query sides"
        )
    return rels, selected_schemas[0]


def _run_qed_projection_analysis(
    mode: str,
    request: dict[str, Any],
    *,
    label: str,
) -> dict[str, Any]:
    with tempfile.TemporaryDirectory(prefix=f"logos-qed-{label}-") as directory:
        request_path = write_text(
            Path(directory) / "request.json",
            json.dumps(request, indent=2, sort_keys=True) + "\n",
        )
        report_path = Path(directory) / "report.json"
        completed = subprocess.run(
            [
                str(ROOT / "benchmarks/scripts/qed-projection-analyze"),
                "--mode",
                mode,
                "--input",
                str(request_path),
                "--output",
                str(report_path),
            ],
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
        if completed.returncode != 0 or not report_path.exists():
            raise QedJsonValidationError(
                f"QED {label} analysis failed: " + tail(completed.stderr).strip()
            )
        try:
            return json.loads(report_path.read_text())
        except (OSError, json.JSONDecodeError) as exc:
            raise QedJsonValidationError(
                f"cannot read QED {label} report: {exc}"
            ) from exc


def analyze_qed_source_star_provenance(
    tables: list[Table],
    queries: list[str],
    authority: dict[str, Any],
) -> dict[str, Any]:
    if len(queries) != 2:
        raise QedJsonValidationError(
            "QED source-star analysis requires exactly two queries"
        )
    calcite_rels, schema = _load_qed_canonical_calcite_rels(authority, tables)
    report = _run_qed_projection_analysis(
        "source-star-provenance",
        {
            "schema": schema,
            "queries": queries,
            "calciteRels": calcite_rels,
        },
        label="source-star-provenance",
    )
    reports = report.get("queries") if isinstance(report, dict) else None
    star_count = report.get("starSideCount") if isinstance(report, dict) else None
    if (
        not isinstance(report, dict)
        or report.get("status") != "verified-source-star-provenance-pair"
        or not isinstance(star_count, int)
        or isinstance(star_count, bool)
        or star_count < 0
        or star_count > 2
        or not isinstance(reports, list)
        or len(reports) != 2
        or sum(item is not None for item in reports) != star_count
    ):
        raise QedJsonValidationError("QED source-star provenance report is malformed")
    for item in reports:
        if item is None:
            continue
        validation = item.get("calciteValidation") if isinstance(item, dict) else None
        outputs = item.get("outputs") if isinstance(item, dict) else None
        if (
            not isinstance(item, dict)
            or item.get("status") != "verified-source-top-level-unqualified-star"
            or not isinstance(item.get("rewrittenSql"), str)
            or not isinstance(item.get("sourceSha256"), str)
            or not isinstance(item.get("rewrittenSha256"), str)
            or not isinstance(outputs, list)
            or len(outputs) != authority.get("outputArity")
            or not isinstance(validation, dict)
            or validation.get("status") != "verified-calcite-direct-output-provenance"
        ):
            raise QedJsonValidationError(
                "QED source-star side lacks exact Calcite provenance"
            )
    return report


def analyze_qed_parsed_star_provenance(
    json_path: str | Path,
    source_star_report: dict[str, Any],
    expected_output_types: list[str],
) -> dict[str, Any]:
    try:
        document = json.loads(Path(json_path).read_text())
    except (OSError, json.JSONDecodeError) as exc:
        raise QedJsonValidationError(
            f"cannot read parsed QED provenance input: {exc}"
        ) from exc
    report = _run_qed_projection_analysis(
        "qed-star-provenance",
        {
            "sourceStarQueries": source_star_report.get("queries"),
            "qedSchemas": document.get("schemas")
            if isinstance(document, dict)
            else None,
            "qedQueries": document.get("queries")
            if isinstance(document, dict)
            else None,
            "expectedOutputTypes": expected_output_types,
        },
        label="parsed-star-provenance",
    )
    queries = report.get("queries") if isinstance(report, dict) else None
    if (
        not isinstance(report, dict)
        or report.get("status") != "verified-qed-source-star-provenance-pair"
        or not isinstance(queries, list)
        or len(queries) != 2
        or any(
            source is not None
            and (
                not isinstance(parsed, dict)
                or parsed.get("status") != "verified-qed-direct-output-provenance"
            )
            for source, parsed in zip(source_star_report.get("queries", []), queries)
        )
    ):
        raise QedJsonValidationError(
            "parsed QED source-star provenance report is malformed"
        )
    return report


def analyze_qed_projection_dependencies(
    tables: list[Table],
    queries: list[str],
) -> dict[str, Any]:
    if len(queries) != 2:
        raise QedJsonValidationError(
            "QED projection analysis requires exactly two queries"
        )
    request = {
        "schema": [
            {
                "name": table.name,
                "columns": [
                    {"name": column.name, "type": column.type_sql}
                    for column in table.columns
                ],
            }
            for table in tables
        ],
        "queries": queries,
    }
    with tempfile.TemporaryDirectory(prefix="logos-qed-projection-") as directory:
        request_path = write_text(
            Path(directory) / "request.json",
            json.dumps(request, indent=2, sort_keys=True) + "\n",
        )
        report_path = Path(directory) / "report.json"
        completed = subprocess.run(
            [
                str(ROOT / "benchmarks/scripts/qed-projection-analyze"),
                "--input",
                str(request_path),
                "--output",
                str(report_path),
            ],
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
        if completed.returncode != 0 or not report_path.exists():
            raise QedJsonValidationError(
                "QED AST projection analysis failed: " + tail(completed.stderr).strip()
            )
        try:
            report = json.loads(report_path.read_text())
        except (OSError, json.JSONDecodeError) as exc:
            raise QedJsonValidationError(
                f"cannot read QED projection report: {exc}"
            ) from exc
    if (
        not isinstance(report, dict)
        or report.get("status") != "verified-ast-dependency-closure"
        or not isinstance(report.get("baseColumns"), dict)
        or not isinstance(report.get("referencedTables"), list)
        or not isinstance(report.get("queries"), list)
        or len(report["queries"]) != 2
        or not isinstance(report.get("outputArity"), int)
        or report["outputArity"] <= 0
    ):
        raise QedJsonValidationError("QED AST projection report is malformed")
    for query in report["queries"]:
        rewrite = query.get("projectionRewrite") if isinstance(query, dict) else None
        if (
            not isinstance(query, dict)
            or not isinstance(query.get("starExpandedSql"), str)
            or not isinstance(query.get("optimizedSql"), str)
            or not isinstance(query.get("sourceHadStar"), bool)
            or not isinstance(query.get("joinShapes"), list)
            or not isinstance(query.get("starSelectShapes"), list)
            or any(
                not isinstance(shape, dict)
                or not isinstance(shape.get("fromRelationKind"), str)
                or not isinstance(shape.get("joinRelationKinds"), list)
                or not all(isinstance(kind, str) for kind in shape["joinRelationKinds"])
                for shape in query.get("starSelectShapes", [])
            )
            or not isinstance(rewrite, dict)
            or rewrite.get("status") != "verified-dead-direct-column-projection"
            or rewrite.get("dangerousExpressionsRemoved") is not False
            or rewrite.get("topLevelOutputPreserved") is not True
        ):
            raise QedJsonValidationError(
                "QED AST projection report lacks a safe query rewrite attestation"
            )
    return report


def analyze_qed_base_use_closure(
    tables: list[Table],
    queries: list[str],
) -> dict[str, Any]:
    """Attest base columns used by the original pair without SQL rewriting."""

    if len(queries) != 2:
        raise QedJsonValidationError(
            "QED base-use analysis requires exactly two queries"
        )
    report = _run_qed_projection_analysis(
        "base-use-closure",
        {
            "schema": [
                {
                    "name": table.name,
                    "columns": [
                        {"name": column.name, "type": column.type_sql}
                        for column in table.columns
                    ],
                }
                for table in tables
            ],
            "queries": queries,
        },
        label="base-use-closure",
    )
    if (
        not isinstance(report, dict)
        or report.get("status") != "verified-exact-base-column-use-closure"
        or report.get("queryBytesPreserved") is not True
        or not isinstance(report.get("baseColumns"), dict)
        or not isinstance(report.get("referencedTables"), list)
        or not isinstance(report.get("queries"), list)
        or len(report["queries"]) != 2
        or not isinstance(report.get("outputArity"), int)
        or report["outputArity"] <= 0
        or any(
            not isinstance(query, dict)
            or query.get("queryBytesPreserved") is not True
            or not isinstance(query.get("inputSha256"), str)
            for query in report["queries"]
        )
    ):
        raise QedJsonValidationError("QED base-use closure report is malformed")
    return report


def analyze_qed_opaque_string_abstraction(
    tables: list[Table],
    queries: list[str],
    allow_nested_relational_stars: list[bool] | None = None,
) -> dict[str, Any]:
    request = {
        "schema": [
            {
                "name": table.name,
                "columns": [
                    {"name": column.name, "type": column.type_sql}
                    for column in table.columns
                ],
            }
            for table in tables
        ],
        "queries": queries,
        "allowNestedRelationalStars": allow_nested_relational_stars,
    }
    with tempfile.TemporaryDirectory(prefix="logos-qed-opaque-string-") as directory:
        request_path = write_text(
            Path(directory) / "request.json",
            json.dumps(request, indent=2, sort_keys=True) + "\n",
        )
        report_path = Path(directory) / "report.json"
        completed = subprocess.run(
            [
                str(ROOT / "benchmarks/scripts/qed-projection-analyze"),
                "--mode",
                "opaque-string",
                "--input",
                str(request_path),
                "--output",
                str(report_path),
            ],
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
        if completed.returncode != 0 or not report_path.exists():
            raise QedJsonValidationError(
                "QED opaque-string analysis failed: " + tail(completed.stderr).strip()
            )
        try:
            report = json.loads(report_path.read_text())
        except (OSError, json.JSONDecodeError) as exc:
            raise QedJsonValidationError(
                f"cannot read QED opaque-string report: {exc}"
            ) from exc
    reports = report.get("queries") if isinstance(report, dict) else None
    declarations = report.get("declarations") if isinstance(report, dict) else None
    like_abstraction = (
        report.get("likeUdfAbstraction") if isinstance(report, dict) else None
    )
    if (
        not isinstance(report, dict)
        or report.get("status") != "verified-opaque-string-equality-abstraction"
        or report.get("encodingInjective") is not True
        or report.get("nullPreserved") is not True
        or not isinstance(report.get("transformedColumns"), list)
        or not report["transformedColumns"]
        or not isinstance(reports, list)
        or len(reports) != 2
        or not isinstance(declarations, list)
        or any(
            declaration != "DECLARE SCALAR FUNCTION QED_VARCHAR_LIKE "
            "(INTEGER, INTEGER) RETURNS BOOLEAN"
            for declaration in declarations
        )
        or declarations
        not in (
            [],
            [
                "DECLARE SCALAR FUNCTION QED_VARCHAR_LIKE "
                "(INTEGER, INTEGER) RETURNS BOOLEAN"
            ],
        )
        or (
            bool(declarations)
            != (
                isinstance(like_abstraction, dict)
                and like_abstraction.get("argumentPolicy")
                == "arbitrary-nullable-integer-arguments"
                and like_abstraction.get("semanticPolicy")
                == "arbitrary-nullable-uninterpreted-function"
                and like_abstraction.get("transferPolicy")
                == (
                    "EQ-for-all-UDF-interpretations-implies-EQ-for-the-concrete-"
                    "strict-LIKE-interpretation"
                )
                and like_abstraction.get("sourceFragment")
                == (
                    "direct-varchar-column-and-backslash-free-string-literal-"
                    "without-escape"
                )
            )
        )
        or any(
            not isinstance(item, dict)
            or not isinstance(item.get("transformedSql"), str)
            or not isinstance(item.get("outputArity"), int)
            or not isinstance(item.get("allowedUses"), list)
            or not isinstance(item.get("sourceHadStar"), bool)
            or not isinstance(item.get("sourceHadTopLevelStar"), bool)
            or not isinstance(item.get("nestedStarsDirectBasePassThrough"), bool)
            for item in reports
        )
    ):
        raise QedJsonValidationError("QED opaque-string report is malformed")
    return report


def _align_qed_tables_with_raw_source_authority(
    tables: list[Table],
    authority: dict[str, Any],
) -> dict[str, dict[str, Any]]:
    if authority.get(
        "status"
    ) != "verified-ordered-raw-source-schema-types" or not isinstance(
        authority.get("tables"), list
    ):
        raise QedJsonValidationError("raw source schema type authority is malformed")
    raw_tables = {
        table.get("name").casefold(): table
        for table in authority["tables"]
        if isinstance(table, dict) and isinstance(table.get("name"), str)
    }
    for table in tables:
        raw_table = raw_tables.get(table.name.casefold())
        raw_columns = raw_table.get("columns") if isinstance(raw_table, dict) else None
        if not isinstance(raw_columns, list) or len(raw_columns) != len(table.columns):
            raise QedJsonValidationError(
                "QED DDL row shape disagrees with raw source schema authority"
            )
        for column, raw_column in zip(table.columns, raw_columns):
            if (
                not isinstance(raw_column, dict)
                or not isinstance(raw_column.get("name"), str)
                or not isinstance(raw_column.get("declaredType"), str)
                or column.name.casefold() != raw_column["name"].casefold()
                or column.type_sql != normalize_type_for_qed(raw_column["declaredType"])
            ):
                raise QedJsonValidationError(
                    "QED DDL names/order/types disagree with raw source schema authority"
                )
    return raw_tables


def _project_opaque_tables_to_live_base_columns(
    tables: list[Table],
    raw_tables: dict[str, dict[str, Any]],
    closure: dict[str, Any],
) -> tuple[list[Table], dict[str, Any], dict[str, set[str]]]:
    by_name = {table.name.casefold(): table for table in tables}
    retained: dict[str, set[str]] = {}
    witnesses: list[dict[str, str]] = []
    projected_tables: list[Table] = []
    omitted: list[dict[str, str]] = []
    for raw_name in closure.get("referencedTables", []):
        if not isinstance(raw_name, str) or raw_name.casefold() not in by_name:
            raise QedJsonValidationError(
                f"base-use closure references unknown QED table {raw_name!r}"
            )
        table = by_name[raw_name.casefold()]
        raw_table = raw_tables.get(table.name.casefold())
        raw_columns = raw_table.get("columns") if isinstance(raw_table, dict) else None
        if not isinstance(raw_columns, list) or len(raw_columns) != len(table.columns):
            raise QedJsonValidationError("raw source/QED table alignment is stale")
        requested = closure.get("baseColumns", {}).get(raw_name, [])
        if not isinstance(requested, list) or any(
            not isinstance(column, str) for column in requested
        ):
            raise QedJsonValidationError("base-use closure columns are malformed")
        canonical = {column.name.casefold(): column.name for column in table.columns}
        selected: set[str] = set()
        for requested_name in requested:
            name = canonical.get(requested_name.casefold())
            if name is None:
                raise QedJsonValidationError(
                    f"base-use closure references unknown column {table.name}.{requested_name}"
                )
            selected.add(name)
        if not selected:
            # A column-free scan still needs one payload so its bag cardinality
            # remains representable.  Do not introduce a character-family
            # witness into the VARCHAR abstraction.
            witness = next(
                (
                    column
                    for column, raw_column in zip(table.columns, raw_columns)
                    if raw_column.get("typeFamily") == "non-character"
                    and _qed_schema_type_name(column.type_sql) != "VARCHAR"
                ),
                None,
            )
            if witness is None:
                raise QedJsonValidationError(
                    f"base-use closure has no non-character witness for {table.name}"
                )
            selected.add(witness.name)
            witnesses.append({"table": table.name, "column": witness.name})
        next_columns: list[Column] = []
        for column, raw_column in zip(table.columns, raw_columns):
            if column.name not in selected:
                omitted.append(
                    {
                        "table": table.name,
                        "column": column.name,
                        "sourceTypeFamily": str(raw_column.get("typeFamily")),
                        "qedNormalizedType": _qed_schema_type_name(column.type_sql),
                    }
                )
                continue
            if (
                _qed_schema_type_name(column.type_sql) == "VARCHAR"
                and raw_column.get("typeFamily") != "varchar"
            ):
                raise QedJsonValidationError(
                    "opaque VARCHAR abstraction found a live non-VARCHAR source "
                    f"column: {table.name}.{column.name} "
                    f"({raw_column.get('declaredType')})"
                )
            next_columns.append(column)
        retained[table.name] = {column.name for column in next_columns}
        projected_tables.append(Table(name=table.name, columns=next_columns))
    if not projected_tables:
        raise QedJsonValidationError("base-use closure retained no source tables")
    return (
        projected_tables,
        {
            "status": "verified-exact-base-use-schema-projection",
            "queryBytesPreserved": True,
            "bagMultiplicityPreserved": True,
            "retained": [
                {
                    "table": table.name,
                    "columns": [column.name for column in table.columns],
                }
                for table in projected_tables
            ],
            "omitted": omitted,
            "cardinalityWitnessColumns": witnesses,
        },
        retained,
    )


def build_qed_opaque_source_admission(
    tables: list[Table],
    queries: list[str],
    constraint_coverage: dict[str, Any],
    benchmark_id: str,
    case_id: str,
) -> dict[str, Any]:
    """Build the replayable raw-type/use-closure admission for opaque strings."""

    raw_source_schema_authority = load_canonical_qed_source_schema_type_authority(
        benchmark_id, case_id
    )
    raw_tables = _align_qed_tables_with_raw_source_authority(
        tables, raw_source_schema_authority
    )
    base_use_closure = None
    source_column_projection = None
    active_tables = tables
    active_constraint_coverage = json.loads(json.dumps(constraint_coverage))
    try:
        base_use_closure = analyze_qed_base_use_closure(tables, queries)
    except QedJsonValidationError as exc:
        # Existing exact source-star provenance remains the only admitted star
        # bridge.  Every selected normalized VARCHAR must then be a raw source
        # VARCHAR, because a star can observe every field.
        if "relational source star" not in str(exc):
            raise
        for table in tables:
            raw_columns = raw_tables[table.name.casefold()]["columns"]
            for column, raw_column in zip(table.columns, raw_columns):
                if (
                    _qed_schema_type_name(column.type_sql) == "VARCHAR"
                    and raw_column.get("typeFamily") != "varchar"
                ):
                    raise QedJsonValidationError(
                        "opaque source-star abstraction found a non-VARCHAR raw "
                        f"source column: {table.name}.{column.name}"
                    ) from exc

    if base_use_closure is not None:
        projected_tables, candidate_projection, retained = (
            _project_opaque_tables_to_live_base_columns(
                tables,
                raw_tables,
                base_use_closure,
            )
        )
        # Preserve the established full-schema path when raw/QED families are
        # already exact.  The new projection is narrowly for dead columns whose
        # source family was erased by QED normalization (notably CHAR->VARCHAR).
        needs_projection = any(
            item.get("qedNormalizedType") == "VARCHAR"
            and item.get("sourceTypeFamily") != "varchar"
            for item in candidate_projection["omitted"]
        )
        if needs_projection:
            active_tables = projected_tables
            source_column_projection = candidate_projection
            active_constraint_coverage = _project_constraint_coverage(
                constraint_coverage, retained
            )

    authority = load_qed_calcite_output_attestation(
        benchmark_id,
        case_id,
        queries,
        active_tables,
        raw_source_schema_authority=(
            raw_source_schema_authority
            if source_column_projection is not None
            else None
        ),
    )
    return {
        "rawSourceSchemaAuthority": raw_source_schema_authority,
        "baseUseClosure": base_use_closure,
        "sourceColumnProjection": source_column_projection,
        "activeTables": active_tables,
        "constraintCoverage": active_constraint_coverage,
        "calciteAuthority": authority,
    }


def create_qed_opaque_string_equivalence_fallback(
    source_sql: str | Path,
    target_sql: str | Path,
    constraint_coverage: dict[str, Any],
    benchmark_id: str,
    case_id: str,
) -> dict[str, Any]:
    source_sql = Path(source_sql)
    target_sql = Path(target_sql)
    pair = extract_qed_query_pair(source_sql.read_text())
    queries = pair["queries"]
    ddl_text = pair["schemaText"]
    tables = parse_schema(
        ddl_text,
        clean_identifier=clean_identifier,
        parse_table=parse_table,
    )
    admission = build_qed_opaque_source_admission(
        tables,
        queries,
        constraint_coverage,
        benchmark_id,
        case_id,
    )
    raw_source_schema_authority = admission["rawSourceSchemaAuthority"]
    base_use_closure = admission["baseUseClosure"]
    source_column_projection = admission["sourceColumnProjection"]
    active_tables = admission["activeTables"]
    active_constraint_coverage = admission["constraintCoverage"]
    authority = admission["calciteAuthority"]
    if any(
        type_name.startswith(("CHAR", "TEXT", "STRING"))
        for side in authority["sides"]
        for type_name in side["outputTypes"]
    ):
        raise QedJsonValidationError(
            "opaque-string abstraction is restricted to exact VARCHAR semantics"
        )
    expected_transformed_output_types = [
        "INTEGER" if type_name.startswith("VARCHAR") else type_name
        for type_name in authority["sourceOutputTypes"]
    ]
    source_star_provenance = analyze_qed_source_star_provenance(
        tables,
        queries,
        authority,
    )
    star_queries = source_star_provenance["queries"]
    rewritten_queries = [
        item["rewrittenSql"] if isinstance(item, dict) else query
        for query, item in zip(queries, star_queries)
    ]
    has_source_star = source_star_provenance["starSideCount"] > 0
    report = analyze_qed_opaque_string_abstraction(
        active_tables,
        rewritten_queries,
        allow_nested_relational_stars=[isinstance(item, dict) for item in star_queries],
    )
    if any(
        item["outputArity"] != authority["outputArity"] for item in report["queries"]
    ):
        raise QedJsonValidationError(
            "opaque-string AST arity disagrees with authoritative Calcite output"
        )
    transformed = {
        (item["table"].casefold(), item["column"].casefold())
        for item in report["transformedColumns"]
        if isinstance(item, dict)
        and isinstance(item.get("table"), str)
        and isinstance(item.get("column"), str)
    }
    expected_transformed = {
        (table.name.casefold(), column.name.casefold())
        for table in active_tables
        for column in table.columns
        if _qed_schema_type_name(column.type_sql) == "VARCHAR"
    }
    if transformed != expected_transformed:
        raise QedJsonValidationError(
            "opaque-string report did not close every VARCHAR schema column"
        )
    quote_identifiers = bool(re.search(r'(?i)\bCREATE\s+TABLE\s+"', ddl_text))
    rendered_tables = []
    for table in active_tables:
        declarations = []
        for column in table.columns:
            type_sql = (
                "INTEGER"
                if (table.name.casefold(), column.name.casefold()) in transformed
                else column.type_sql
            )
            suffix = " NOT NULL" if column.not_null else ""
            declarations.append(
                f"  {render_identifier(column.name, quote_identifiers)} {type_sql}{suffix}"
            )
        rendered_tables.append(
            f"CREATE TABLE {render_identifier(table.name, quote_identifiers)} (\n"
            + ",\n".join(declarations)
            + "\n);\n"
        )
    write_text(
        target_sql,
        "\n".join(rendered_tables)
        + "\n"
        + "".join(ensure_sql_terminated(item) for item in pair["declarations"])
        + "".join(ensure_sql_terminated(item) for item in report["declarations"])
        + "".join(
            ensure_sql_terminated(item["transformedSql"]) for item in report["queries"]
        ),
    )
    return {
        "id": "opaque-varchar-equality-integer-abstraction",
        "input": target_sql.name,
        "inputSha256": sha256_path(target_sql),
        "sourceInput": source_sql.name,
        "sourceInputSha256": sha256_path(source_sql),
        "generatedJson": target_sql.with_suffix(".json").name,
        "trigger": (
            "qed-varchar-charset-on-closed-equality-or-attested-like-udf-fragment"
        ),
        "resultPolicy": "accept-eq-only",
        "rowTypePolicy": (
            "injective-varchar-domain-encoding-with-attested-nullable-like-udf"
            + (
                "-and-exact-base-use-schema-projection"
                if source_column_projection is not None
                else ""
            )
        ),
        "queryRewritePolicy": (
            ("exact-source-span-root-star-expansion-plus-" if has_source_star else "")
            + (
                "original-query-preserved-under-exact-base-use-schema-projection-plus-"
                if source_column_projection is not None
                else ""
            )
            + "exact-equality-literal-and-attested-like-spans-plus-varchar-ddl-"
            "to-integer-and-like-udf-declaration"
        ),
        "dependencyAttestation": report,
        "sourceSchemaTypeAuthority": raw_source_schema_authority,
        "sourceColumnUseClosure": base_use_closure,
        "sourceColumnProjection": source_column_projection,
        "sourceStarProvenance": (source_star_provenance if has_source_star else None),
        "calciteAuthority": authority,
        "expectedTransformedOutputTypes": expected_transformed_output_types,
        "constraintCoverage": active_constraint_coverage,
    }


def _project_constraint_coverage(
    coverage: dict[str, Any],
    retained: dict[str, set[str]],
) -> dict[str, Any]:
    projected = json.loads(json.dumps(coverage))
    applied = projected.get("applied")
    omitted = projected.get("omitted")
    if not isinstance(applied, list) or not isinstance(omitted, list):
        raise QedJsonValidationError("QED projection coverage is malformed")

    retained_folded = {
        table.casefold(): {column.casefold() for column in columns}
        for table, columns in retained.items()
    }

    def entry_retained(entry: Any) -> bool:
        if not isinstance(entry, dict) or not isinstance(entry.get("table"), str):
            return True
        columns = retained_folded.get(entry["table"].casefold())
        if columns is None:
            return False
        raw_columns = entry.get("columns")
        return not isinstance(raw_columns, list) or all(
            isinstance(column, str) and column.casefold() in columns
            for column in raw_columns
        )

    next_applied = []
    for entry in applied:
        if entry_retained(entry):
            next_applied.append(entry)
            continue
        if isinstance(entry, dict):
            omitted.append(
                {
                    **entry,
                    "source": "qed-ast-projection-fallback",
                    "reason": "constraint-column-outside-attested-dependency-closure",
                }
            )
    projected["applied"] = next_applied
    for metadata_field in ("postParseKeys", "renderedKeys"):
        values = projected.get(metadata_field)
        if isinstance(values, list):
            projected[metadata_field] = [
                entry for entry in values if entry_retained(entry)
            ]
    projected["omitted"] = deduplicate_constraint_entries(omitted)
    projected["compatibility"] = "conservative-relaxation"
    projected["equivalenceOnlyProjection"] = {
        "acceptedResult": "EQ",
        "reason": "qed-calcite-varchar-charset-bug-after-nullability-relaxation",
        "soundness": (
            "An attested complete base-column dependency closure retains every "
            "column observed by the original query. Base-row projection preserves bag "
            "multiplicity; an EQ proof for all projected databases therefore implies EQ "
            "for every source database. No non-EQ conclusion is accepted."
        ),
    }
    return projected


def create_qed_star_expansion_equivalence_fallback(
    source_sql: str | Path,
    target_sql: str | Path,
    constraint_coverage: dict[str, Any],
    benchmark_id: str,
    case_id: str,
) -> dict[str, Any]:
    """Expand relational stars without changing the source schema or operators.

    QED stores base-table fields in name-sorted order.  An implicit star on one
    side and an explicit source-order projection on the other can consequently
    serialize with different output vectors even when the SQL vectors agree.
    Exact source-span expansion plus source/Calcite/QED column provenance makes
    the source order explicit; SQLGlot qualification and projection pushdown
    are not trusted for this full-schema retry.
    """

    source_sql = Path(source_sql)
    target_sql = Path(target_sql)
    sql_text = source_sql.read_text()
    pair = extract_qed_query_pair(sql_text)
    queries = pair["queries"]
    ddl_text = pair["schemaText"]
    tables = parse_schema(
        ddl_text,
        clean_identifier=clean_identifier,
        parse_table=parse_table,
    )
    authority = load_qed_calcite_output_attestation(
        benchmark_id,
        case_id,
        queries,
        tables,
    )
    source_star_provenance = analyze_qed_source_star_provenance(
        tables,
        queries,
        authority,
    )
    if source_star_provenance["starSideCount"] <= 0:
        raise QedJsonValidationError("star-expansion fallback found no source star")
    source_star_provenance["outputArity"] = authority["outputArity"]
    rewritten_queries = [
        item["rewrittenSql"] if isinstance(item, dict) else query
        for query, item in zip(queries, source_star_provenance["queries"])
    ]
    write_text(
        target_sql,
        pair["preambleText"]
        + "".join(ensure_sql_terminated(query) for query in rewritten_queries),
    )
    return {
        "id": "ast-star-expanded-equivalence",
        "input": target_sql.name,
        "inputSha256": sha256_path(target_sql),
        "sourceInput": source_sql.name,
        "sourceInputSha256": sha256_path(source_sql),
        "generatedJson": target_sql.with_suffix(".json").name,
        "trigger": "qed-name-sorted-star-output-signature",
        "resultPolicy": "accept-eq-only",
        "rowTypePolicy": "all-selected-source-columns-preserved",
        "queryRewritePolicy": "exact-source-span-root-star-expansion-only",
        "dependencyAttestation": source_star_provenance,
        "sourceStarProvenance": source_star_provenance,
        "calciteAuthority": authority,
        "expectedOutputTypes": authority["sourceOutputTypes"],
        "constraintCoverage": json.loads(json.dumps(constraint_coverage)),
    }


def create_qed_projection_equivalence_fallback(
    source_sql: str | Path,
    target_sql: str | Path,
    constraint_coverage: dict[str, Any],
) -> dict[str, Any]:
    """Create an AST-attested, full-observation QED column projection fallback."""

    source_sql = Path(source_sql)
    target_sql = Path(target_sql)
    sql_text = source_sql.read_text()
    pair = extract_qed_query_pair(sql_text)
    queries = pair["queries"]
    ddl_text = pair["schemaText"]
    tables = parse_schema(
        ddl_text,
        clean_identifier=clean_identifier,
        parse_table=parse_table,
    )
    report = analyze_qed_projection_dependencies(tables, queries)
    by_name = {table.name.casefold(): table for table in tables}
    retained: dict[str, set[str]] = {}
    witnesses: list[dict[str, str]] = []
    for raw_name in report["referencedTables"]:
        if not isinstance(raw_name, str) or raw_name.casefold() not in by_name:
            raise QedJsonValidationError(
                f"QED projection report references unknown table {raw_name!r}"
            )
        table = by_name[raw_name.casefold()]
        raw_columns = report["baseColumns"].get(raw_name, [])
        if not isinstance(raw_columns, list) or not all(
            isinstance(column, str) for column in raw_columns
        ):
            raise QedJsonValidationError(
                f"QED projection report has malformed columns for {raw_name}"
            )
        canonical = {column.name.casefold(): column.name for column in table.columns}
        selected = set()
        for raw_column in raw_columns:
            column = canonical.get(raw_column.casefold())
            if column is None:
                raise QedJsonValidationError(
                    f"QED projection report references unknown column {raw_name}.{raw_column}"
                )
            selected.add(column)
        if not selected:
            witness = _projection_witness_column(table)
            selected.add(witness.name)
            witnesses.append({"table": table.name, "column": witness.name})
        retained[table.name] = selected

    rendered_tables = []
    removed_columns: list[dict[str, Any]] = []
    for table in tables:
        selected = retained.get(table.name)
        if selected is None:
            continue
        declarations = []
        for column in table.columns:
            if column.name not in selected:
                removed_columns.append({"table": table.name, "column": column.name})
                continue
            suffix = " NOT NULL" if column.not_null else ""
            declarations.append(
                f"  {quote_identifier(column.name)} {column.type_sql}{suffix}"
            )
        if not declarations:
            raise QedJsonValidationError(
                f"QED projection removed all columns from {table.name}"
            )
        rendered_tables.append(
            f"CREATE TABLE {quote_identifier(table.name)} (\n"
            + ",\n".join(declarations)
            + "\n);\n"
        )
    if not rendered_tables:
        raise QedJsonValidationError("QED projection retained no source tables")

    rewritten_queries = []
    for source_query, query_report in zip(queries, report["queries"]):
        rewrite = query_report["projectionRewrite"]
        removed = rewrite.get("removedSelections")
        if removed and query_report.get("sourceHadStar") is True:
            raise QedJsonValidationError(
                "QED projection cannot combine a relational source star with "
                "SQLGlot dead-column rewriting"
            )
        # Qualification/pushdown is needed only to keep a projected DDL valid
        # after a proven dead direct-column output is removed.  Otherwise keep
        # the exact normalized source SQL: unnecessary SQLGlot reserialization
        # can produce frontend spellings (notably interval literals) outside
        # QED's narrower parser even though no semantic rewrite was required.
        rewritten_queries.append(
            query_report["optimizedSql"] if removed else source_query
        )
    projected_sql = (
        "\n".join(rendered_tables)
        + "\n"
        + "".join(ensure_sql_terminated(item) for item in pair["declarations"])
        + "".join(ensure_sql_terminated(query) for query in rewritten_queries)
    )
    write_text(target_sql, projected_sql)
    projected_coverage = _project_constraint_coverage(constraint_coverage, retained)
    return {
        "id": "ast-column-projected-equivalence",
        "input": target_sql.name,
        "inputSha256": sha256_path(target_sql),
        "sourceInput": source_sql.name,
        "sourceInputSha256": sha256_path(source_sql),
        "generatedJson": target_sql.with_suffix(".json").name,
        "trigger": "qed-varchar-charset-after-nullability-relaxation",
        "resultPolicy": "accept-eq-only",
        "rowTypePolicy": "sqlglot-attested-live-base-columns",
        "queryRewritePolicy": "dead-direct-derived-columns-only",
        "dependencyAttestation": report,
        "removedColumns": removed_columns,
        "cardinalityWitnessColumns": witnesses,
        "constraintCoverage": projected_coverage,
    }


def validate_qed_projection_result(
    json_path: str | Path,
    fallback: dict[str, Any],
) -> dict[str, Any]:
    validation = validate_qed_json(json_path)
    attestation = fallback.get("dependencyAttestation")
    expected_arity = (
        attestation.get("outputArity") if isinstance(attestation, dict) else None
    )
    if (
        not isinstance(expected_arity, int)
        or validation["outputArity"] != expected_arity
    ):
        raise QedJsonValidationError(
            "projected QED JSON output arity does not match the source AST: "
            f"{validation['outputArity']} vs {expected_arity!r}"
        )
    return validation


def validate_qed_star_expansion_result(
    json_path: str | Path,
    fallback: dict[str, Any],
) -> dict[str, Any]:
    if fallback.get("id") != "ast-star-expanded-equivalence":
        raise QedJsonValidationError("QED star validator received a non-star fallback")
    validation = validate_qed_projection_result(json_path, fallback)
    expected_types = fallback.get("expectedOutputTypes")
    if (
        not isinstance(expected_types, list)
        or validation["outputTypes"] != expected_types
    ):
        raise QedJsonValidationError(
            "star-expanded QED JSON output types disagree with the authoritative "
            f"source signature: {validation['outputTypes']!r} vs "
            f"{expected_types!r}"
        )
    source_star = fallback.get("sourceStarProvenance")
    if (
        not isinstance(source_star, dict)
        or source_star.get("status") != "verified-source-star-provenance-pair"
        or source_star.get("starSideCount", 0) <= 0
    ):
        raise QedJsonValidationError(
            "star-expanded fallback lacks exact source provenance"
        )
    validation["sourceStarProvenanceValidation"] = analyze_qed_parsed_star_provenance(
        json_path,
        source_star,
        expected_types,
    )
    return validation


def validate_qed_opaque_string_result(
    json_path: str | Path,
    fallback: dict[str, Any],
) -> dict[str, Any]:
    validation = validate_qed_json(json_path)
    expected = fallback.get("expectedTransformedOutputTypes")
    if not isinstance(expected, list) or validation["outputTypes"] != expected:
        raise QedJsonValidationError(
            "opaque-string QED JSON output types disagree with the authoritative "
            f"encoded signature: {validation['outputTypes']!r} vs {expected!r}"
        )
    source_star = fallback.get("sourceStarProvenance")
    if source_star is not None:
        if (
            not isinstance(source_star, dict)
            or source_star.get("status") != "verified-source-star-provenance-pair"
            or source_star.get("starSideCount", 0) <= 0
        ):
            raise QedJsonValidationError(
                "opaque-string fallback has malformed source-star provenance"
            )
        validation["sourceStarProvenanceValidation"] = (
            analyze_qed_parsed_star_provenance(
                json_path,
                source_star,
                expected,
            )
        )
    return validation


def identifier_is_referenced(
    sql: str, identifier: str, forbid_preceding_dot: bool = False
) -> bool:
    quoted = quote_identifier(identifier)
    quoted_prefix = r"(?<!\.)" if forbid_preceding_dot else ""
    if re.search(rf"{quoted_prefix}{re.escape(quoted)}(?!\s*\.)", sql):
        return True
    bare_prefix = (
        r"(?<![.A-Za-z0-9_])" if forbid_preceding_dot else r"(?<![A-Za-z0-9_])"
    )
    return bool(
        re.search(rf"(?is){bare_prefix}{re.escape(identifier)}(?![A-Za-z0-9_])", sql)
    )


def collect_table_aliases(sql: str) -> dict[str, str]:
    aliases: dict[str, str] = {}
    relation_re = re.compile(
        r"(?is)(?:\bFROM\b|\bJOIN\b)\s*"
        r'("(?:""|[^"])+?"|[A-Za-z_][A-Za-z0-9_]*)'
        r'(?:\s+(?:AS\s+)?("(?:""|[^"])+?"|[A-Za-z_][A-Za-z0-9_]*))?'
    )
    stopwords = {
        "where",
        "join",
        "inner",
        "left",
        "right",
        "full",
        "cross",
        "on",
        "group",
        "order",
        "having",
        "limit",
        "offset",
        "union",
        "except",
        "intersect",
    }
    for match in relation_re.finditer(sql):
        table_name = clean_identifier(match.group(1))
        alias = clean_identifier(match.group(2)) if match.group(2) else None
        aliases[table_name] = table_name
        if alias and alias.lower() not in stopwords:
            aliases[alias] = table_name
    aliases.update(collect_comma_from_aliases(sql, stopwords))
    return aliases


def collect_comma_from_aliases(sql: str, stopwords: set[str]) -> dict[str, str]:
    aliases: dict[str, str] = {}
    from_re = re.compile(
        r"(?is)\bFROM\b(?P<body>.*?)(?=\bWHERE\b|\bGROUP\b|\bORDER\b|\bHAVING\b|\bLIMIT\b|\bUNION\b|\bEXCEPT\b|\bINTERSECT\b|$)"
    )
    for match in from_re.finditer(sql):
        for item in split_top_level_commas(match.group("body")):
            item = item.strip()
            if not item or item.startswith("("):
                continue
            rel = re.match(
                r'(?is)^("(?:""|[^"])+?"|[A-Za-z_][A-Za-z0-9_]*)(?:\s+(?:AS\s+)?("(?:""|[^"])+?"|[A-Za-z_][A-Za-z0-9_]*))?',
                item,
            )
            if not rel:
                continue
            table_name = clean_identifier(rel.group(1))
            alias = clean_identifier(rel.group(2)) if rel.group(2) else None
            aliases[table_name] = table_name
            if alias and alias.lower() not in stopwords:
                aliases[alias] = table_name
    return aliases


_DDL_IDENTIFIER = r'("(?:""|[^"])+?"|`(?:``|[^`])+?`|[A-Za-z_][A-Za-z0-9_]*)'


def constraint_entry(
    kind: str,
    source: str,
    table: str | None = None,
    columns: tuple[str, ...] | list[str] | None = None,
    reason: str | None = None,
    **details: Any,
) -> dict[str, Any]:
    entry: dict[str, Any] = {"kind": kind, "source": source}
    if table is not None:
        entry["table"] = table
    if columns is not None:
        entry["columns"] = list(columns)
    if reason is not None:
        entry["reason"] = reason
    entry.update({key: value for key, value in details.items() if value is not None})
    return entry


def deduplicate_constraint_entries(
    entries: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    result: list[dict[str, Any]] = []
    seen: set[str] = set()
    for entry in entries:
        key = json.dumps(entry, sort_keys=True, separators=(",", ":"))
        if key in seen:
            continue
        seen.add(key)
        result.append(entry)
    return result


def find_table(tables: list[Table], name: str) -> Table | None:
    folded = name.casefold()
    return next((table for table in tables if table.name.casefold() == folded), None)


def find_column(table: Table, name: str) -> Column | None:
    folded = name.casefold()
    return next(
        (column for column in table.columns if column.name.casefold() == folded), None
    )


def canonical_key(
    table: Table, columns: list[str] | tuple[str, ...]
) -> tuple[str, ...] | None:
    if not columns:
        return None
    canonical: list[str] = []
    for name in columns:
        column = find_column(table, name)
        if column is None:
            return None
        if column.name.casefold() in {item.casefold() for item in canonical}:
            return None
        canonical.append(column.name)
    return tuple(canonical)


def apply_not_null(table: Table, column_name: str) -> str | None:
    column = find_column(table, column_name)
    if column is None:
        return None
    column.not_null = True
    return column.name


def apply_primary_key(
    table: Table, columns: list[str] | tuple[str, ...]
) -> tuple[str, ...] | None:
    key = canonical_key(table, columns)
    if key is None:
        return None
    for column_name in key:
        apply_not_null(table, column_name)
    if key in table.primary_keys or key in table.unique_keys:
        return key
    # SQL permits only one PRIMARY KEY declaration, whereas benchmark metadata
    # can redundantly restate the same key through several sources.  A second
    # distinct non-null key has the same QED key semantics when rendered UNIQUE.
    if table.primary_keys:
        table.unique_keys.append(key)
    else:
        table.primary_keys.append(key)
    return key


def apply_unique_key(
    table: Table, columns: list[str] | tuple[str, ...]
) -> tuple[str, ...] | None:
    key = canonical_key(table, columns)
    if key is None:
        return None
    if not all(find_column(table, name).not_null for name in key):
        return None
    if key not in table.primary_keys and key not in table.unique_keys:
        table.unique_keys.append(key)
    return key


def parse_key_column_list(text: str) -> list[str] | None:
    columns: list[str] = []
    for part in split_top_level_commas(text):
        match = re.fullmatch(
            rf"(?is)\s*{_DDL_IDENTIFIER}(?:\s+(?:ASC|DESC))?\s*",
            part,
        )
        if not match:
            return None
        columns.append(clean_identifier(match.group(1)))
    return columns or None


def table_constraint(item: str) -> tuple[str | None, list[str] | None]:
    semantic = item.strip()
    named = re.match(
        rf"(?is)^CONSTRAINT\s+{_DDL_IDENTIFIER}\s+(?P<body>.+)$",
        semantic,
    )
    if named:
        semantic = named.group("body").strip()

    patterns = (
        (
            "primary",
            rf"(?is)^PRIMARY\s+KEY(?:\s+{_DDL_IDENTIFIER})?\s*\((?P<columns>.*)\)\s*$",
        ),
        (
            "unique",
            rf"(?is)^UNIQUE(?:\s+(?:KEY|INDEX))?(?:\s+{_DDL_IDENTIFIER})?\s*\((?P<columns>.*)\)\s*$",
        ),
    )
    for kind, pattern in patterns:
        match = re.match(pattern, semantic)
        if match:
            return kind, parse_key_column_list(match.group("columns"))

    masked = normalize_spaces(mask_sql_regions(semantic)).upper()
    if masked.startswith("FOREIGN KEY"):
        return "foreign", None
    if masked.startswith("CHECK"):
        return "check", None
    if item.lstrip().upper().startswith("CONSTRAINT"):
        return "unsupported", None
    if masked.startswith(("KEY", "INDEX")):
        return "index", None
    return None, None


def parse_table(table_name: str, body: str) -> Table:
    table = Table(name=table_name)
    pending_primary: list[list[str]] = []
    pending_unique: list[list[str]] = []
    for item in split_top_level_commas(body):
        item = item.strip()
        if not item:
            continue

        kind, key_columns = table_constraint(item)
        if kind is not None:
            if kind == "primary" and key_columns is not None:
                pending_primary.append(key_columns)
            elif kind == "unique" and key_columns is not None:
                pending_unique.append(key_columns)
            elif kind not in {"index"}:
                table.omitted_constraints.append(
                    constraint_entry(
                        kind or "unsupported",
                        "source-ddl",
                        table.name,
                        reason=(
                            "qed-does-not-support-foreign-keys"
                            if kind == "foreign"
                            else "check-not-attested-for-qed"
                            if kind == "check"
                            else "constraint-definition-not-exactly-renderable"
                        ),
                    )
                )
            continue

        match = re.match(
            r'(?is)\s*("(?:""|[^"])+?"|`(?:``|[^`])+?`|[A-Za-z_][A-Za-z0-9_]*)\s+(.+)$',
            item,
        )
        if not match:
            continue
        name = clean_identifier(match.group(1))
        rest = match.group(2)
        masked_rest = mask_sql_regions(rest)
        not_null = bool(re.search(r"(?is)\bNOT\s+NULL\b", masked_rest))
        table.columns.append(
            Column(name=name, type_sql=normalize_type_for_qed(rest), not_null=not_null)
        )
        if not_null:
            table.applied_constraints.append(
                constraint_entry("not_null", "source-ddl", table.name, [name])
            )
        if re.search(r"(?is)\bPRIMARY\s+KEY\b", masked_rest):
            pending_primary.append([name])
        if re.search(r"(?is)\bUNIQUE\b", masked_rest):
            pending_unique.append([name])
        if re.search(r"(?is)\bREFERENCES\b", masked_rest):
            table.omitted_constraints.append(
                constraint_entry(
                    "foreign",
                    "source-ddl",
                    table.name,
                    [name],
                    "qed-does-not-support-foreign-keys",
                )
            )
        if re.search(r"(?is)\bCHECK\s*\(", masked_rest):
            table.omitted_constraints.append(
                constraint_entry(
                    "check",
                    "source-ddl",
                    table.name,
                    [name],
                    "check-not-attested-for-qed",
                )
            )

    for columns in pending_primary:
        key = apply_primary_key(table, columns)
        if key is None:
            table.omitted_constraints.append(
                constraint_entry(
                    "primary",
                    "source-ddl",
                    table.name,
                    columns,
                    "constraint-column-not-found",
                )
            )
        else:
            table.applied_constraints.append(
                constraint_entry("primary", "source-ddl", table.name, key)
            )
    for columns in pending_unique:
        key = apply_unique_key(table, columns)
        if key is None:
            canonical = canonical_key(table, columns)
            table.omitted_constraints.append(
                constraint_entry(
                    "unique",
                    "source-ddl",
                    table.name,
                    canonical or columns,
                    (
                        "nullable-unique-not-exactly-representable"
                        if canonical is not None
                        else "constraint-column-not-found"
                    ),
                )
            )
        else:
            table.applied_constraints.append(
                constraint_entry("unique", "source-ddl", table.name, key)
            )
    return table


def constraint_reference_value(reference: Any) -> str | None:
    if isinstance(reference, str):
        return reference
    if isinstance(reference, dict) and isinstance(reference.get("value"), str):
        return reference["value"]
    return None


def resolve_constraint_reference(
    reference: Any,
    tables: list[Table],
) -> tuple[Table | None, Column | None, str | None]:
    value = constraint_reference_value(reference)
    if value is None:
        return None, None, None
    folded = value.casefold()
    for table in sorted(tables, key=lambda item: len(item.name), reverse=True):
        prefix = table.name.casefold() + "__"
        if not folded.startswith(prefix):
            continue
        column = find_column(table, value[len(table.name) + 2 :])
        return table, column, value
    return None, None, value


def add_applied_constraint(
    coverage: dict[str, Any],
    kind: str,
    source: str,
    table: Table,
    columns: tuple[str, ...] | list[str],
    **details: Any,
) -> None:
    coverage["applied"].append(
        constraint_entry(kind, source, table.name, columns, **details)
    )


def add_omitted_constraint(
    coverage: dict[str, Any],
    kind: str,
    source: str,
    reason: str,
    table: Table | str | None = None,
    columns: tuple[str, ...] | list[str] | None = None,
    **details: Any,
) -> None:
    coverage["omitted"].append(
        constraint_entry(
            kind,
            source,
            table.name if isinstance(table, Table) else table,
            columns,
            reason,
            **details,
        )
    )


def apply_pair_constraint_metadata(
    selected_tables: list[Table],
    all_tables: list[Table],
    constraints: list[Any],
    coverage: dict[str, Any],
) -> None:
    selected = {table.name.casefold(): table for table in selected_tables}
    source = "pair-constraint-metadata"
    for raw_constraint in constraints:
        if not isinstance(raw_constraint, dict) or len(raw_constraint) != 1:
            add_omitted_constraint(
                coverage,
                "unknown",
                source,
                "malformed-constraint-metadata",
            )
            continue
        kind, payload = next(iter(raw_constraint.items()))
        references = payload if isinstance(payload, list) else [payload]
        resolved = [
            resolve_constraint_reference(reference, all_tables)
            for reference in references
        ]
        owner = resolved[0][0] if resolved else None
        selected_owner = (
            selected.get(owner.name.casefold()) if owner is not None else None
        )
        if owner is not None and selected_owner is None:
            continue

        if kind == "not_null":
            table, column, value = resolved[0]
            if selected_owner is None or column is None:
                add_omitted_constraint(
                    coverage,
                    "not_null",
                    source,
                    "constraint-reference-not-resolved",
                    table,
                    rawReference=value,
                )
                continue
            canonical = apply_not_null(selected_owner, column.name)
            if canonical is None:
                add_omitted_constraint(
                    coverage,
                    "not_null",
                    source,
                    "constraint-column-not-found",
                    selected_owner,
                    [column.name],
                )
            else:
                add_applied_constraint(
                    coverage, "not_null", source, selected_owner, [canonical]
                )
            continue

        if kind == "primary":
            raw_values = [value for _, _, value in resolved if value is not None]
            if (
                selected_owner is None
                or not resolved
                or any(table is None or column is None for table, column, _ in resolved)
                or any(
                    table.name.casefold() != owner.name.casefold()
                    for table, _, _ in resolved
                )
            ):
                add_omitted_constraint(
                    coverage,
                    "primary",
                    source,
                    "constraint-reference-not-resolved",
                    selected_owner or owner,
                    rawReferences=raw_values,
                )
                continue
            key = apply_primary_key(
                selected_owner,
                [column.name for _, column, _ in resolved],
            )
            if key is None:
                add_omitted_constraint(
                    coverage,
                    "primary",
                    source,
                    "constraint-column-not-found",
                    selected_owner,
                    rawReferences=raw_values,
                )
            else:
                add_applied_constraint(coverage, "primary", source, selected_owner, key)
            continue

        if kind == "foreign":
            if selected_owner is None:
                # An unresolved owner cannot safely be classified as out of scope.
                if owner is None:
                    add_omitted_constraint(
                        coverage,
                        "foreign",
                        source,
                        "constraint-reference-not-resolved",
                        rawReferences=[
                            value for _, _, value in resolved if value is not None
                        ],
                    )
                continue
            source_column = resolved[0][1]
            target_table = resolved[1][0] if len(resolved) > 1 else None
            target_column = resolved[1][1] if len(resolved) > 1 else None
            add_omitted_constraint(
                coverage,
                "foreign",
                source,
                "qed-does-not-support-foreign-keys",
                selected_owner,
                [source_column.name] if source_column is not None else None,
                refTable=target_table.name if target_table is not None else None,
                refColumns=[target_column.name] if target_column is not None else None,
            )
            continue

        add_omitted_constraint(
            coverage,
            kind,
            source,
            "constraint-kind-not-exactly-renderable",
            selected_owner or owner,
            rawReferences=[value for _, _, value in resolved if value is not None],
        )


def apply_application_constraint_metadata(
    selected_tables: list[Table],
    constraints: dict[str, Any],
    coverage: dict[str, Any],
) -> None:
    selected = {table.name.casefold(): table for table in selected_tables}
    source = "application-constraint-metadata"

    semantic_schema = constraints.get("semanticSchema") or {}
    for raw_table in semantic_schema.get("tables") or []:
        if not isinstance(raw_table, dict) or not isinstance(
            raw_table.get("name"), str
        ):
            continue
        table = selected.get(raw_table["name"].casefold())
        if table is None:
            continue
        for raw_column in raw_table.get("columns") or []:
            if not isinstance(raw_column, dict) or not raw_column.get("notNull"):
                continue
            name = raw_column.get("name")
            canonical = apply_not_null(table, name) if isinstance(name, str) else None
            if canonical is None:
                add_omitted_constraint(
                    coverage,
                    "not_null",
                    source,
                    "constraint-column-not-found",
                    table,
                    [name] if isinstance(name, str) else None,
                )
            else:
                add_applied_constraint(coverage, "not_null", source, table, [canonical])

    for raw_key in constraints.get("primaryKeys") or []:
        if not isinstance(raw_key, dict) or not isinstance(raw_key.get("table"), str):
            continue
        table = selected.get(raw_key["table"].casefold())
        if table is None:
            continue
        columns = raw_key.get("columns") or []
        key = (
            apply_primary_key(table, columns)
            if all(isinstance(item, str) for item in columns)
            else None
        )
        if key is None:
            add_omitted_constraint(
                coverage,
                "primary",
                source,
                "constraint-column-not-found",
                table,
                columns if isinstance(columns, list) else None,
            )
        else:
            add_applied_constraint(coverage, "primary", source, table, key)

    normalized_unique_signatures: set[tuple[str, tuple[str, ...]]] = set()
    for raw_key in constraints.get("uniqueKeys") or []:
        if not isinstance(raw_key, dict) or not isinstance(raw_key.get("table"), str):
            continue
        table = selected.get(raw_key["table"].casefold())
        if table is None:
            continue
        columns = raw_key.get("columns") or []
        if not all(isinstance(item, str) for item in columns):
            add_omitted_constraint(
                coverage,
                "unique",
                source,
                "constraint-column-not-found",
                table,
            )
            continue
        signature = (table.name.casefold(), tuple(item.casefold() for item in columns))
        normalized_unique_signatures.add(signature)
        nullable_columns = raw_key.get("nullableColumns") or []
        if nullable_columns:
            add_omitted_constraint(
                coverage,
                "unique",
                source,
                "nullable-unique-not-exactly-representable",
                table,
                columns,
                nullableColumns=nullable_columns,
            )
            continue
        key = apply_unique_key(table, columns)
        if key is None:
            add_omitted_constraint(
                coverage,
                "unique",
                source,
                "constraint-columns-not-proven-not-null",
                table,
                columns,
            )
        else:
            add_applied_constraint(coverage, "unique", source, table, key)

    for raw_index in constraints.get("uniqueIndexes") or []:
        if not isinstance(raw_index, dict) or not isinstance(
            raw_index.get("table"), str
        ):
            continue
        table = selected.get(raw_index["table"].casefold())
        if table is None:
            continue
        terms = raw_index.get("terms") or []
        simple_columns = terms if all(isinstance(item, str) for item in terms) else []
        signature = (
            table.name.casefold(),
            tuple(item.casefold() for item in simple_columns),
        )
        if not raw_index.get("where") and signature in normalized_unique_signatures:
            continue
        if raw_index.get("where"):
            add_omitted_constraint(
                coverage,
                "unique",
                source,
                "partial-unique-index-not-exactly-representable",
                table,
                simple_columns or None,
                predicate=raw_index.get("where"),
            )
            continue
        key = apply_unique_key(table, simple_columns) if simple_columns else None
        if key is None:
            add_omitted_constraint(
                coverage,
                "unique",
                source,
                "expression-or-nullable-unique-index-not-exactly-representable",
                table,
                simple_columns or None,
            )
        else:
            add_applied_constraint(coverage, "unique", source, table, key)

    for raw_foreign in constraints.get("foreignKeys") or []:
        if not isinstance(raw_foreign, dict) or not isinstance(
            raw_foreign.get("table"), str
        ):
            continue
        table = selected.get(raw_foreign["table"].casefold())
        if table is None:
            continue
        add_omitted_constraint(
            coverage,
            "foreign",
            source,
            "qed-does-not-support-foreign-keys",
            table,
            raw_foreign.get("columns"),
            refTable=raw_foreign.get("refTable"),
            refColumns=raw_foreign.get("refColumns"),
        )

    for raw_check in constraints.get("checks") or []:
        if not isinstance(raw_check, dict) or not isinstance(
            raw_check.get("table"), str
        ):
            continue
        table = selected.get(raw_check["table"].casefold())
        if table is None:
            continue
        add_omitted_constraint(
            coverage,
            "check",
            source,
            "check-not-attested-for-qed",
            table,
            expression=raw_check.get("expression"),
        )

    for raw_unsupported in constraints.get("unsupportedSemanticConstraints") or []:
        table_name = (
            raw_unsupported.get("table") if isinstance(raw_unsupported, dict) else None
        )
        table = (
            selected.get(table_name.casefold()) if isinstance(table_name, str) else None
        )
        if table_name is not None and table is None:
            continue
        add_omitted_constraint(
            coverage,
            "unsupported",
            source,
            "source-constraint-not-normalized",
            table or table_name,
            detail=raw_unsupported,
        )


def apply_constraint_metadata(
    selected_tables: list[Table],
    all_tables: list[Table],
    constraints: Any,
    coverage: dict[str, Any],
) -> None:
    if constraints is None:
        return
    if isinstance(constraints, list):
        apply_pair_constraint_metadata(
            selected_tables, all_tables, constraints, coverage
        )
        return
    if isinstance(constraints, dict):
        apply_application_constraint_metadata(selected_tables, constraints, coverage)
        return
    add_omitted_constraint(
        coverage,
        "unknown",
        "constraint-metadata",
        "malformed-constraint-metadata",
    )


def normalize_type_for_qed(type_sql: str) -> str:
    lower = normalize_spaces(type_sql).lower()
    if lower.startswith("bigint"):
        return "BIGINT"
    if lower.startswith(("integer", "int", "smallint", "tinyint", "mediumint")):
        return "INTEGER"
    if lower.startswith(("decimal", "numeric")):
        return "DECIMAL"
    if lower.startswith(("double", "float", "real")):
        return "DOUBLE"
    if lower.startswith(("bool", "boolean")):
        return "BOOLEAN"
    if lower.startswith("date"):
        return "DATE"
    if lower.startswith(("timestamp", "datetime", "time")):
        return "TIMESTAMP"
    if lower.startswith(("char", "varchar", "character", "text", "string")):
        return "VARCHAR(255)"
    return "VARCHAR(255)"


def source_character_type_family(type_sql: str) -> str:
    """Classify the raw declared character family without QED normalization.

    Fixed-width CHAR and varying-width VARCHAR have observably different SQL
    equality semantics.  The QED renderer deliberately maps both to VARCHAR,
    so an abstraction admission decision must use this independent raw source
    authority rather than either the rendered DDL or Calcite's inferred type.
    """

    lower = normalize_spaces(type_sql).casefold()
    if re.match(r"^(?:varchar|character\s+varying|char\s+varying)\b", lower):
        return "varchar"
    if re.match(r"^(?:char|character)(?:\s*\(|\s*$)", lower):
        return "char"
    if re.match(r"^(?:text|string)\b", lower):
        return "text"
    return "non-character"


def _parse_raw_source_table(table_name: str, body: str) -> dict[str, Any]:
    columns: list[dict[str, Any]] = []
    seen: set[str] = set()
    for item in split_top_level_commas(body):
        item = item.strip()
        if not item:
            continue
        kind, _ = table_constraint(item)
        if kind is not None:
            continue
        match = re.match(
            r'(?is)\s*("(?:""|[^"])+?"|`(?:``|[^`])+?`|[A-Za-z_][A-Za-z0-9_]*)\s+(.+)$',
            item,
        )
        if match is None:
            raise QedJsonValidationError(
                f"raw source schema has an unparsed item in {table_name}: {item!r}"
            )
        name = clean_identifier(match.group(1))
        folded = name.casefold()
        if folded in seen:
            raise QedJsonValidationError(
                f"raw source schema has duplicate column {table_name}.{name}"
            )
        seen.add(folded)
        rest = match.group(2)
        masked = mask_sql_regions(rest)
        constraint = _RAW_COLUMN_CONSTRAINT.search(masked)
        declared_type = normalize_spaces(
            rest[: constraint.start()] if constraint is not None else rest
        )
        if not declared_type:
            raise QedJsonValidationError(
                f"raw source schema column has no declared type: {table_name}.{name}"
            )
        columns.append(
            {
                "name": name,
                "declaredType": declared_type,
                "typeFamily": source_character_type_family(declared_type),
                "notNull": bool(re.search(r"(?is)\bNOT\s+NULL\b", masked)),
            }
        )
    if not columns:
        raise QedJsonValidationError(
            f"raw source schema table has no parsed columns: {table_name}"
        )
    return {"name": table_name, "columns": columns}


def build_qed_source_schema_type_authority(schema_sql: str) -> dict[str, Any]:
    """Bind ordered raw DDL types before ``normalize_type_for_qed`` erases them."""

    tables = parse_schema(
        schema_sql,
        clean_identifier=clean_identifier,
        parse_table=_parse_raw_source_table,
    )
    searchable = mask_sql_regions(schema_sql, mask_quotes=True)
    create_count = len(list(_RAW_CREATE_TABLE.finditer(searchable)))
    if not tables or len(tables) != create_count:
        raise QedJsonValidationError(
            "raw source schema authority did not account for every CREATE TABLE"
        )
    seen: set[str] = set()
    for table in tables:
        folded = table["name"].casefold()
        if folded in seen:
            raise QedJsonValidationError(
                f"raw source schema has duplicate table {table['name']}"
            )
        seen.add(folded)
    return {
        "status": "verified-ordered-raw-source-schema-types",
        "schemaSha256": hashlib.sha256(schema_sql.encode()).hexdigest(),
        "tables": tables,
    }


def load_canonical_qed_source_schema_type_authority(
    benchmark_id: str,
    case_id: str,
) -> dict[str, Any]:
    """Rebuild raw type authority from the canonical ingestion case.

    Generated metadata is intentionally not its own authority.  Cold runner
    retries and replay validation both use this lookup so a stale or edited
    family classification cannot turn a live CHAR into a VARCHAR abstraction.
    """

    config_path = resolve_path(DEFAULT_CONFIG)
    config_bytes = config_path.read_bytes()
    cache_key = (
        str(ROOT.resolve()),
        hashlib.sha256(config_bytes).hexdigest(),
        benchmark_id,
    )
    cached = _CANONICAL_SOURCE_SCHEMA_AUTHORITY_CACHE.get(cache_key)
    if cached is not None:
        authority = cached.get(case_id)
        if authority is None:
            raise QedJsonValidationError(
                "canonical case is unavailable for raw schema authority: "
                f"{benchmark_id}/{case_id}"
            )
        return json.loads(json.dumps(authority))

    config = json.loads(config_bytes)
    benchmarks = [
        benchmark
        for benchmark in config.get("benchmarks", [])
        if isinstance(benchmark, dict) and benchmark.get("id") == benchmark_id
    ]
    if len(benchmarks) != 1:
        raise QedJsonValidationError(
            f"canonical benchmark is unavailable for raw schema authority: {benchmark_id}"
        )
    exporter = load_exporter()
    by_case: dict[str, dict[str, Any]] = {}
    for case in exporter.iter_cases(config, benchmarks[0]):
        if case.case_id in by_case:
            raise QedJsonValidationError(
                "canonical case is ambiguous for raw schema authority: "
                f"{benchmark_id}/{case.case_id}"
            )
        by_case[case.case_id] = build_qed_source_schema_type_authority(case.schema_sql)
    _CANONICAL_SOURCE_SCHEMA_AUTHORITY_CACHE[cache_key] = by_case
    authority = by_case.get(case_id)
    if authority is None:
        raise QedJsonValidationError(
            "canonical case is unavailable for raw schema authority: "
            f"{benchmark_id}/{case_id}"
        )
    return json.loads(json.dumps(authority))


def patch_qed_sql(sql: str) -> str:
    return patch_qed_interval_precision(strip_sql_comments(sql))


def patch_qed_tsql_date_day_pair(
    before_sql: str,
    after_sql: str,
    before_source: str,
    after_source: str,
    read_dialect: str,
) -> tuple[str, str, dict[str, Any] | None]:
    """Repair SQLGlot's nested `N AS days` rendering, with pair attestation.

    TPC-DS's T-SQL-like source spells date displacement as `date + N days` in
    one query and `date + N` in the other. SQLGlot parses `days` as a nested
    alias and emits invalid PostgreSQL. We rewrite both structurally matching
    sides to an explicit DAY interval only when the complete BETWEEN
    lower/upper/date-count multisets agree, both bounds use the same literal,
    and exactly one complete source side contains the unit token and its
    corresponding normalized alias. This prevents a protected lookalike,
    legitimate result-column alias, or unrelated date arithmetic from being
    changed.
    """

    if read_dialect.casefold() not in {"tsql", "tsql_like"}:
        return before_sql, after_sql, None

    sources = (before_source, after_source)
    normalized = (before_sql, after_sql)

    # Bracket-quoted T-SQL identifiers can contain an entire predicate
    # lookalike. The shared scanner deliberately follows standard/PostgreSQL
    # quoting and therefore does not guess at bracket boundaries. Fail closed
    # whenever either raw T-SQL side has a structural bracket token.
    if any(
        "[" in (masked := mask_sql_regions(sql)) or "]" in masked for sql in sources
    ):
        return before_sql, after_sql, None

    def unprotected_matches(pattern: re.Pattern[str], sql: str) -> list[re.Match[str]]:
        found: list[re.Match[str]] = []

        def retain(match: re.Match[str]) -> str:
            found.append(match)
            return match.group(0)

        # These patterns begin at structural BETWEEN and byte-preserve every
        # quoted literal in their matched tail. `start_only` therefore admits
        # the intended DATE literals while rejecting a whole lookalike whose
        # BETWEEN begins inside a string or comment.
        substitute_unprotected(pattern, retain, sql, start_only=True)
        return found

    source_matches = tuple(
        unprotected_matches(_QED_TSQL_DATE_DAY_SOURCE, sql) for sql in sources
    )
    normalized_matches = tuple(
        unprotected_matches(_QED_TSQL_DATE_DAY_NORMALIZED, sql) for sql in normalized
    )

    if any(not side for side in source_matches + normalized_matches):
        return before_sql, after_sql, None

    def signatures(
        matches: tuple[list[re.Match[str]], list[re.Match[str]]],
    ) -> tuple[Counter[tuple[str, str, str]], Counter[tuple[str, str, str]]]:
        return tuple(
            Counter(
                (
                    match.group("lower_literal"),
                    match.group("upper_literal"),
                    match.group("days"),
                )
                for match in side
            )
            for side in matches
        )

    source_signatures = signatures(source_matches)
    normalized_signatures = signatures(normalized_matches)
    unit_vectors = tuple(
        [match.group("unit") is not None for match in side] for side in source_matches
    )
    complete_unit_sides = (
        all(unit_vectors[0]) and not any(unit_vectors[1]),
        all(unit_vectors[1]) and not any(unit_vectors[0]),
    )
    source_side = 0 if complete_unit_sides[0] else 1
    plain_side = 1 - source_side

    if (
        source_signatures[0] != source_signatures[1]
        or normalized_signatures[0] != normalized_signatures[1]
        or source_signatures[0] != normalized_signatures[0]
        or sum(complete_unit_sides) != 1
        or any(
            lower != upper
            for pair_signatures in (source_signatures, normalized_signatures)
            for signature in pair_signatures
            for lower, upper, _days in signature
        )
        or any(
            match.group("alias") is None for match in normalized_matches[source_side]
        )
        or any(
            match.group("alias") is not None for match in normalized_matches[plain_side]
        )
    ):
        return before_sql, after_sql, None

    def explicit_day_interval(match: re.Match) -> str:
        return (
            match.group("predicate_prefix")
            + match.group("upper_prefix")
            + f"INTERVAL '{match.group('days')}' DAY"
            + match.group("suffix")
        )

    patched = tuple(
        substitute_unprotected(
            _QED_TSQL_DATE_DAY_NORMALIZED,
            explicit_day_interval,
            sql,
            start_only=True,
        )
        for sql in normalized
    )
    report = {
        "kind": "tsql-predicate-date-day-to-explicit-interval",
        "sourceSide": "before" if source_side == 0 else "after",
        "occurrencesPerQuery": len(normalized_matches[0]),
        "predicateOnly": True,
        "outputSignatureUnaffected": True,
        "dateDayMultiset": [
            {
                "lowerDateLiteral": lower_literal,
                "upperDateLiteral": upper_literal,
                "days": days,
                "count": count,
            }
            for (
                lower_literal,
                upper_literal,
                days,
            ), count in sorted(normalized_signatures[0].items())
        ],
        "semanticNote": (
            "Both pair members have the same complete BETWEEN lower/upper "
            "CAST(DATE)+day-count multiset, with equal lower and upper date "
            "literals at every site. Exactly one complete T-SQL-like source "
            "side carries `days`, which SQLGlot rendered as an illegal nested "
            "alias. QED rejects DATE+INTEGER, so both upper bounds are emitted "
            "as explicit DAY intervals. The rewrite is restricted to "
            "predicates and cannot change the query output signature."
        ),
    }
    return patched[0], patched[1], report


def patch_qed_interval_precision(sql: str) -> str:
    def repl(match: re.Match) -> str:
        value = match.group(1)
        precision = len(value)
        return f"INTERVAL '{value}' DAY({precision})"

    return substitute_unprotected(
        _QED_INTERVAL_PRECISION,
        repl,
        sql,
        start_only=True,
    )


def ensure_sql_terminated(sql: str) -> str:
    stripped = sql.strip()
    if not stripped:
        return "\n"
    return stripped if stripped.endswith(";") else stripped + ";\n"


def quote_identifier(identifier: str) -> str:
    return '"' + identifier.replace('"', '""') + '"'


def render_identifier(identifier: str, quote: bool) -> str:
    if quote or not re.match(r"^[A-Za-z_][A-Za-z0-9_]*$", identifier):
        return quote_identifier(identifier)
    return identifier


def clean_identifier(value: str) -> str:
    value = value.strip()
    if "." in value:
        value = value.split(".")[-1]
    if value.startswith('"') and value.endswith('"'):
        return value[1:-1].replace('""', '"')
    if value.startswith("`") and value.endswith("`"):
        return value[1:-1].replace("``", "`")
    return value


def normalize_spaces(value: str) -> str:
    return re.sub(r"\s+", " ", value.strip())


def write_text(path: Path, content: str) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content)
    return path


def sha256_path(path: str | Path) -> str:
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def tail(text: str, limit: int = 4000) -> str:
    return text[-limit:]


if __name__ == "__main__":
    raise SystemExit(main())
