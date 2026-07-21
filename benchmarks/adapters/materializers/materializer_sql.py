"""Shared lexical helpers for the benchmark materializers.

These helpers only identify SQL boundaries.  They deliberately leave type,
constraint, and dialect-specific interpretation to each materializer.
"""

from __future__ import annotations

import re
from collections.abc import Callable
from dataclasses import dataclass
from typing import TypeVar


@dataclass(frozen=True)
class SqlQuotePolicy:
    """Quote and escape forms recognized while locating SQL boundaries."""

    quote_chars: frozenset[str]
    doubled_quote_chars: frozenset[str]
    backslash_escape_chars: frozenset[str]

    def __post_init__(self) -> None:
        if any(len(char) != 1 for char in self.quote_chars):
            raise ValueError("SQL quote characters must each be one character")
        if not self.doubled_quote_chars <= self.quote_chars:
            raise ValueError("doubled quote characters must be enabled quotes")
        if not self.backslash_escape_chars <= self.quote_chars:
            raise ValueError("backslash-escaped quote characters must be enabled quotes")


# The materializers ingest both PostgreSQL- and MySQL-family schemas, so
# boundary scanning recognizes their union of quote delimiters. Backslash is
# ordinary in standard strings but structural in a PostgreSQL E-string.
# MySQL-family consumers bind the explicit policy below instead of changing
# the PostgreSQL-standard default.
STANDARD_MATERIALIZER_QUOTE_POLICY = SqlQuotePolicy(
    quote_chars=frozenset(("'", '"', "`")),
    doubled_quote_chars=frozenset(("'", '"', "`")),
    backslash_escape_chars=frozenset(),
)

# MySQL ordinary quoted strings use backslash escapes unless NO_BACKSLASH_ESCAPES
# is enabled. The WeTune/SQLSolver materializers ingest ordinary MySQL-family
# dumps and queries, so they bind this policy explicitly instead of weakening
# PostgreSQL-standard scanning for every consumer.
MYSQL_MATERIALIZER_QUOTE_POLICY = SqlQuotePolicy(
    quote_chars=frozenset(("'", '"', "`")),
    doubled_quote_chars=frozenset(("'", '"', "`")),
    backslash_escape_chars=frozenset(("'", '"', "`")),
)


T = TypeVar("T")
ASCII_SQL_WHITESPACE = " \t\n\r\f\v"
ASCII_SQL_WHITESPACE_PATTERN = r"[ \t\n\r\f\v]"
POSTGRES_IDENTIFIER_CONTINUATION_CLASS = (
    r"A-Za-z0-9_$\x80-\U0010ffff"
)
_CREATE_TABLE = re.compile(
    rf"(?<![{POSTGRES_IDENTIFIER_CONTINUATION_CLASS}.])"
    rf"CREATE{ASCII_SQL_WHITESPACE_PATTERN}+TABLE"
    rf"(?![{POSTGRES_IDENTIFIER_CONTINUATION_CLASS}.])",
    flags=re.IGNORECASE | re.DOTALL | re.ASCII,
)
_SQL_WHITESPACE = frozenset(ASCII_SQL_WHITESPACE)


@dataclass(frozen=True)
class SqlProtectedRegion:
    """One position-preserving quote or comment extent in SQL text."""

    start: int
    end: int
    kind: str
    delimiter: str
    terminated: bool


def _identifier_start(char: str) -> bool:
    """PostgreSQL's ASCII-or-high-bit unquoted identifier start rule."""

    return (
        char == "_"
        or "A" <= char <= "Z"
        or "a" <= char <= "z"
        or ord(char) >= 128
    )


def _identifier_continue(char: str) -> bool:
    """PostgreSQL dollar-tag continuation (identifier syntax, except dollar)."""

    return _identifier_start(char) or "0" <= char <= "9"


def _dollar_quote_tag_at(text: str, index: int) -> str | None:
    """Return the PostgreSQL dollar-quote delimiter beginning at ``index``."""

    if text[index] != "$":
        return None
    # A delimiter adjoining an identifier is part of that identifier in
    # PostgreSQL, not the beginning of a dollar-quoted string.
    if index > 0 and (
        _identifier_continue(text[index - 1]) or text[index - 1] == "$"
    ):
        return None
    if index + 1 < len(text) and text[index + 1] == "$":
        return "$$"
    if index + 1 >= len(text) or not _identifier_start(text[index + 1]):
        return None

    cursor = index + 2
    while cursor < len(text) and _identifier_continue(text[cursor]):
        cursor += 1
    if cursor < len(text) and text[cursor] == "$":
        return text[index : cursor + 1]
    return None


def _escape_string_quote_at(text: str, index: int) -> bool:
    """Whether the quote at ``index`` starts a PostgreSQL E-string."""

    if text[index] != "'" or index == 0 or text[index - 1] not in ("e", "E"):
        return False
    return index == 1 or not (
        _identifier_continue(text[index - 2]) or text[index - 2] == "$"
    )


def _ordinary_quote_region(
    text: str,
    index: int,
    policy: SqlQuotePolicy,
) -> SqlProtectedRegion:
    quote = text[index]
    backslash_escapes = (
        quote in policy.backslash_escape_chars
        or _escape_string_quote_at(text, index)
    )
    cursor = index + 1
    while cursor < len(text):
        char = text[cursor]
        if char == "\\" and backslash_escapes and cursor + 1 < len(text):
            cursor += 2
            continue
        if char != quote:
            cursor += 1
            continue
        if (
            quote in policy.doubled_quote_chars
            and cursor + 1 < len(text)
            and text[cursor + 1] == quote
        ):
            cursor += 2
            continue
        kind = {
            "'": "single_quote",
            '"': "double_quote",
            "`": "backtick_quote",
        }.get(quote, "quote")
        return SqlProtectedRegion(index, cursor + 1, kind, quote, True)
    kind = {
        "'": "single_quote",
        '"': "double_quote",
        "`": "backtick_quote",
    }.get(quote, "quote")
    return SqlProtectedRegion(index, len(text), kind, quote, False)


def _protected_region_at(
    text: str,
    index: int,
    policy: SqlQuotePolicy,
) -> SqlProtectedRegion | None:
    """Scan one quote or comment beginning at an otherwise ordinary position."""

    if text.startswith("--", index):
        cursor = index + 2
        while cursor < len(text) and text[cursor] not in "\r\n":
            cursor += 1
        return SqlProtectedRegion(index, cursor, "comment", "--", True)

    if text.startswith("/*", index):
        depth = 1
        cursor = index + 2
        while cursor < len(text) and depth:
            if text.startswith("/*", cursor):
                depth += 1
                cursor += 2
            elif text.startswith("*/", cursor):
                depth -= 1
                cursor += 2
            else:
                cursor += 1
        return SqlProtectedRegion(
            index,
            cursor,
            "comment",
            "/*",
            depth == 0,
        )

    if text[index] in policy.quote_chars:
        return _ordinary_quote_region(text, index, policy)

    dollar_tag = _dollar_quote_tag_at(text, index)
    if dollar_tag is not None:
        close_index = text.find(dollar_tag, index + len(dollar_tag))
        end = len(text) if close_index < 0 else close_index + len(dollar_tag)
        return SqlProtectedRegion(
            index,
            end,
            "dollar_quote",
            dollar_tag,
            close_index >= 0,
        )

    return None


def _mask_region(text: str) -> str:
    """Blank a region without changing offsets or line structure."""

    return "".join(char if char in "\r\n" else " " for char in text)


def protected_sql_regions(
    sql: str,
    *,
    quote_policy: SqlQuotePolicy = STANDARD_MATERIALIZER_QUOTE_POLICY,
) -> list[SqlProtectedRegion]:
    """Return all non-overlapping protected regions from the shared scanner."""

    regions: list[SqlProtectedRegion] = []
    index = 0
    while index < len(sql):
        region = _protected_region_at(sql, index, quote_policy)
        if region is None:
            index += 1
            continue
        regions.append(region)
        index = region.end
    return regions


def mask_sql_regions(
    sql: str,
    *,
    mask_quotes: bool = True,
    quote_policy: SqlQuotePolicy = STANDARD_MATERIALIZER_QUOTE_POLICY,
) -> str:
    """Mask protected SQL while preserving offsets and line structure.

    Comments are always masked. Set ``mask_quotes=False`` only when a consumer
    needs the original quote bytes but still wants comments removed.
    """

    output: list[str] = []
    index = 0
    while index < len(sql):
        region = _protected_region_at(sql, index, quote_policy)
        if region is None:
            output.append(sql[index])
            index += 1
            continue
        contents = sql[index : region.end]
        if region.kind == "comment" or mask_quotes:
            output.append(_mask_region(contents))
        else:
            output.append(contents)
        index = region.end
    return "".join(output)


def _region_overlaps(start: int, end: int, region: SqlProtectedRegion) -> bool:
    if start == end:
        return region.start <= start < region.end
    return start < region.end and end > region.start


def substitute_unprotected(
    pattern: re.Pattern[str],
    replacement: str | Callable[[re.Match[str]], str],
    sql: str,
    *,
    start_only: bool = False,
    quote_policy: SqlQuotePolicy = STANDARD_MATERIALIZER_QUOTE_POLICY,
) -> str:
    """Apply a regex only at structurally unprotected SQL positions.

    The default rejects a match overlapping any quote or comment. ``start_only``
    is intentionally explicit: use it only for a pattern whose replacement
    byte-preserves every quoted token in the matched suffix. It rejects matches
    beginning in a protected region but permits such copied literal tails.
    """

    regions = protected_sql_regions(sql, quote_policy=quote_policy)
    pieces: list[str] = []
    last = 0
    changed = False
    for match in pattern.finditer(sql):
        protected_start = any(
            _region_overlaps(match.start(), match.start(), region)
            for region in regions
        )
        protected_match = any(
            _region_overlaps(match.start(), match.end(), region)
            for region in regions
        )
        blocked = protected_start if start_only else protected_match
        if blocked:
            continue
        pieces.append(sql[last : match.start()])
        pieces.append(
            replacement(match)
            if callable(replacement)
            else match.expand(replacement)
        )
        last = match.end()
        changed = True
    if not changed:
        return sql
    pieces.append(sql[last:])
    return "".join(pieces)


def normalize_sql_layout(
    sql: str,
    *,
    strip_trailing_semicolon: bool = False,
    quote_policy: SqlQuotePolicy = STANDARD_MATERIALIZER_QUOTE_POLICY,
) -> str:
    """Remove comments and compact only unprotected SQL whitespace.

    Every byte in an ordinary, doubled, E-string, backtick, or dollar-quoted
    region is retained. Comments and surrounding layout become at most one
    separating space. A requested trailing semicolon is removed only after the
    protected-aware normalization proves it is structural trailing punctuation.
    """

    output: list[str] = []
    pending_space = False
    trailing_semicolon_is_unprotected = False
    index = 0
    while index < len(sql):
        region = _protected_region_at(sql, index, quote_policy)
        if region is not None:
            if region.kind == "comment":
                pending_space = True
            else:
                if pending_space and output:
                    output.append(" ")
                output.append(sql[index : region.end])
                pending_space = False
                # In particular, do not reinterpret the last byte of an
                # unterminated region as structural punctuation.
                trailing_semicolon_is_unprotected = False
            index = region.end
            continue
        char = sql[index]
        if char in _SQL_WHITESPACE:
            pending_space = True
        else:
            if pending_space and output:
                output.append(" ")
            output.append(char)
            pending_space = False
            trailing_semicolon_is_unprotected = char == ";"
        index += 1

    normalized = "".join(output)
    if (
        strip_trailing_semicolon
        and trailing_semicolon_is_unprotected
        and normalized.endswith(";")
    ):
        normalized = normalized[:-1].rstrip(ASCII_SQL_WHITESPACE)
    return normalized


def transform_double_quoted_identifiers(
    sql: str,
    transform: Callable[[str], str],
    *,
    quote_policy: SqlQuotePolicy = STANDARD_MATERIALIZER_QUOTE_POLICY,
) -> str:
    """Transform complete double-quoted identifier regions outside other regions."""

    output: list[str] = []
    index = 0
    while index < len(sql):
        region = _protected_region_at(sql, index, quote_policy)
        if region is None:
            output.append(sql[index])
            index += 1
            continue
        contents = sql[index : region.end]
        if region.kind == "double_quote" and region.terminated:
            output.append(transform(contents[1:-1].replace('""', '"')))
        else:
            output.append(contents)
        index = region.end
    return "".join(output)


def strip_sql_comments(
    sql: str,
    *,
    quote_policy: SqlQuotePolicy = STANDARD_MATERIALIZER_QUOTE_POLICY,
) -> str:
    """Remove line and nested block comments, preserving quoted contents."""

    return mask_sql_regions(
        sql,
        mask_quotes=False,
        quote_policy=quote_policy,
    )


def _split_top_level(
    text: str,
    delimiter: str,
    quote_policy: SqlQuotePolicy,
) -> list[str]:
    if len(delimiter) != 1:
        raise ValueError("top-level delimiter must be one character")

    parts: list[str] = []
    start = 0
    depth = 0
    index = 0
    while index < len(text):
        region = _protected_region_at(text, index, quote_policy)
        if region is not None:
            index = region.end
            continue
        char = text[index]
        if char == "(":
            depth += 1
        elif char == ")":
            depth = max(0, depth - 1)
        elif char == delimiter and depth == 0:
            parts.append(text[start:index])
            start = index + 1
        index += 1
    parts.append(text[start:])
    return parts


def split_top_level_commas(
    text: str,
    *,
    quote_policy: SqlQuotePolicy = STANDARD_MATERIALIZER_QUOTE_POLICY,
) -> list[str]:
    """Split commas outside quotes and nested parentheses."""

    return _split_top_level(text, ",", quote_policy)


def split_sql_statements(
    sql: str,
    *,
    quote_policy: SqlQuotePolicy = STANDARD_MATERIALIZER_QUOTE_POLICY,
) -> list[str]:
    """Split top-level semicolon-delimited statements, preserving empty middles."""

    parts = _split_top_level(sql, ";", quote_policy)
    statements = [part.strip(ASCII_SQL_WHITESPACE) for part in parts[:-1]]
    tail = parts[-1].strip(ASCII_SQL_WHITESPACE)
    if tail:
        statements.append(tail)
    return statements


def find_next_unquoted(
    text: str,
    needle: str,
    start: int,
    *,
    quote_policy: SqlQuotePolicy = STANDARD_MATERIALIZER_QUOTE_POLICY,
) -> int:
    """Return the next single-character needle outside a quoted region."""

    if len(needle) != 1:
        raise ValueError("unquoted search needle must be one character")
    index = max(0, start)
    while index < len(text):
        region = _protected_region_at(text, index, quote_policy)
        if region is not None:
            index = region.end
            continue
        char = text[index]
        if char == needle:
            return index
        index += 1
    return -1


def find_matching_paren(
    text: str,
    open_index: int,
    *,
    quote_policy: SqlQuotePolicy = STANDARD_MATERIALIZER_QUOTE_POLICY,
) -> int:
    """Find the close matching one known unquoted opening parenthesis."""

    if open_index < 0 or open_index >= len(text) or text[open_index] != "(":
        return -1
    depth = 0
    index = open_index
    while index < len(text):
        region = _protected_region_at(text, index, quote_policy)
        if region is not None:
            index = region.end
            continue
        char = text[index]
        if char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
            if depth == 0:
                return index
        index += 1
    return -1


def parse_schema(
    schema_sql: str,
    *,
    clean_identifier: Callable[[str], str],
    parse_table: Callable[[str, str], T],
    quote_policy: SqlQuotePolicy = STANDARD_MATERIALIZER_QUOTE_POLICY,
) -> list[T]:
    """Parse CREATE TABLE extents while delegating table-body semantics."""

    tables: list[T] = []
    searchable_sql = mask_sql_regions(
        schema_sql,
        mask_quotes=True,
        quote_policy=quote_policy,
    )
    position = 0
    while match := _CREATE_TABLE.search(searchable_sql, position):
        next_create = _CREATE_TABLE.search(searchable_sql, match.end())
        statement_end = find_next_unquoted(
            schema_sql,
            ";",
            match.end(),
            quote_policy=quote_policy,
        )
        barriers = [
            (next_create.start(), next_create.start())
            if next_create is not None
            else None,
            (statement_end, statement_end + 1)
            if statement_end >= 0
            else None,
        ]
        first_barrier = min(
            (barrier for barrier in barriers if barrier is not None),
            default=None,
        )
        open_paren = find_next_unquoted(
            schema_sql,
            "(",
            match.end(),
            quote_policy=quote_policy,
        )
        if open_paren < 0 or (
            first_barrier is not None and first_barrier[0] < open_paren
        ):
            if first_barrier is None:
                break
            position = first_barrier[1]
            continue
        table_name_sql = strip_sql_comments(
            schema_sql[match.end() : open_paren],
            quote_policy=quote_policy,
        )
        table_name = clean_identifier(
            table_name_sql.strip(ASCII_SQL_WHITESPACE)
        )
        close_paren = find_matching_paren(
            schema_sql,
            open_paren,
            quote_policy=quote_policy,
        )
        if close_paren < 0 or (
            first_barrier is not None and first_barrier[0] < close_paren
        ):
            if first_barrier is None:
                break
            position = first_barrier[1]
            continue
        table_body_sql = strip_sql_comments(
            schema_sql[open_paren + 1 : close_paren],
            quote_policy=quote_policy,
        )
        tables.append(parse_table(table_name, table_body_sql))
        position = close_paren + 1
    return tables
