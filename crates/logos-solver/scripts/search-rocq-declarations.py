#!/usr/bin/env python3
"""Mechanically search public Rocq declarations in an authority source tree.

The source files are authoritative.  This helper performs no semantic routing,
scoring, ranking, or candidate truncation: filters are exact, results have one
stable lexical order, and every match is reachable through explicit pages.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import stat
import sys
import tempfile
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Sequence


IDENTIFIER = r"[A-Za-z_][A-Za-z0-9_']*"
QUALIFIED_IDENTIFIER = re.compile(rf"{IDENTIFIER}(?:\.{IDENTIFIER})*")
DECLARATION = re.compile(
    rf"(?m)^[ \t]*(?P<qualifiers>(?:(?:Local|Global|Polymorphic|Monomorphic|Program)[ \t]+)*)"
    rf"(?P<kind>Lemma|Theorem|Corollary)[ \t]+(?P<name>{IDENTIFIER})(?![A-Za-z0-9_'])"
)
PROOF_TERMINATOR = re.compile(r"\b(Qed|Defined|Admitted|Abort)\s*\.")
SCOPE_COMMAND = re.compile(
    rf"(?m)^[ \t]*(?:"
    rf"(?P<section>Section)[ \t]+(?P<section_name>{IDENTIFIER})(?![A-Za-z0-9_'])|"
    rf"Module[ \t]+Type[ \t]+(?P<module_type_name>{IDENTIFIER})(?![A-Za-z0-9_'])|"
    rf"Module[ \t]+(?:Export[ \t]+)?"
    rf"(?P<module_name>(?!Type\b|Import\b){IDENTIFIER})(?![A-Za-z0-9_'])|"
    rf"End[ \t]+(?P<end_name>{IDENTIFIER})(?![A-Za-z0-9_']))"
)


class SearchError(RuntimeError):
    """The authority tree or one of its source files is malformed."""


@dataclass(frozen=True)
class SourceRoot:
    path: Path
    logical_prefix: tuple[str, ...]


@dataclass(frozen=True)
class SourceFile:
    path: Path
    root: SourceRoot
    content: bytes


@dataclass(frozen=True)
class ScopeEvent:
    position: int
    action: str
    kind: str | None
    name: str


@dataclass(frozen=True)
class Declaration:
    fqn: str
    name: str
    kind: str
    module: str
    source: str
    line: int
    statement: str
    conclusion_symbol: str | None
    symbols: tuple[str, ...]

    def public_record(self, *, show_statement: bool) -> dict[str, object]:
        record: dict[str, object] = {
            "fqn": self.fqn,
            "name": self.name,
            "kind": self.kind,
            "module": self.module,
            "source": self.source,
            "line": self.line,
            "conclusionSymbol": self.conclusion_symbol,
            "symbols": list(self.symbols),
        }
        if show_statement:
            record["statement"] = self.statement
        return record


@dataclass(frozen=True)
class ExactFilters:
    fqn: str | None = None
    name: str | None = None
    module: str | None = None
    source: str | None = None
    conclusion_symbol: str | None = None
    symbols: tuple[str, ...] = ()

    def accepts(self, declaration: Declaration) -> bool:
        if self.fqn is not None and declaration.fqn != self.fqn:
            return False
        if self.name is not None and declaration.name != self.name:
            return False
        if self.module is not None and declaration.module != self.module:
            return False
        if self.source is not None and declaration.source != self.source:
            return False
        if (
            self.conclusion_symbol is not None
            and declaration.conclusion_symbol != self.conclusion_symbol
        ):
            return False
        available_symbols = set(declaration.symbols)
        return all(symbol in available_symbols for symbol in self.symbols)

    def public_record(self) -> dict[str, object]:
        return {
            "fqn": self.fqn,
            "name": self.name,
            "module": self.module,
            "source": self.source,
            "conclusionSymbol": self.conclusion_symbol,
            "symbols": list(self.symbols),
        }


def mask_comments_and_strings(text: str, *, preserve_strings: bool = False) -> str:
    """Replace comment/string contents with spaces while preserving positions."""
    result = list(text)
    comment_depth = 0
    in_string = False
    index = 0
    while index < len(text):
        pair = text[index : index + 2]
        if comment_depth:
            if pair == "(*":
                result[index] = result[index + 1] = " "
                comment_depth += 1
                index += 2
                continue
            if pair == "*)":
                result[index] = result[index + 1] = " "
                comment_depth -= 1
                index += 2
                continue
            if text[index] != "\n":
                result[index] = " "
            index += 1
            continue
        if in_string:
            if pair == '""':
                if not preserve_strings:
                    result[index] = result[index + 1] = " "
                index += 2
                continue
            if text[index] == '"':
                if not preserve_strings:
                    result[index] = " "
                in_string = False
            elif text[index] != "\n" and not preserve_strings:
                result[index] = " "
            index += 1
            continue
        if pair == "(*":
            result[index] = result[index + 1] = " "
            comment_depth = 1
            index += 2
            continue
        if text[index] == '"':
            if not preserve_strings:
                result[index] = " "
            in_string = True
        index += 1
    if comment_depth:
        raise SearchError("unterminated Rocq comment")
    if in_string:
        raise SearchError("unterminated Rocq string")
    return "".join(result)


def sentence_end(masked_text: str, start: int) -> int:
    """Find a vernacular sentence dot in already masked text."""
    index = start
    while index < len(masked_text):
        if masked_text[index] == "." and (
            index + 1 == len(masked_text) or masked_text[index + 1].isspace()
        ):
            return index
        index += 1
    raise SearchError("unterminated Rocq sentence")


def scope_events(masked_text: str) -> list[ScopeEvent]:
    events: list[ScopeEvent] = []
    for match in SCOPE_COMMAND.finditer(masked_text):
        if match.group("section_name") is not None:
            events.append(
                ScopeEvent(
                    match.start(), "open", "section", match.group("section_name")
                )
            )
            continue
        if match.group("module_type_name") is not None:
            events.append(
                ScopeEvent(
                    match.start(),
                    "open",
                    "module-type",
                    match.group("module_type_name"),
                )
            )
            continue
        if match.group("module_name") is not None:
            end = sentence_end(masked_text, match.end())
            command = masked_text[match.start() : end + 1]
            if ":=" not in command:
                events.append(
                    ScopeEvent(
                        match.start(), "open", "module", match.group("module_name")
                    )
                )
            continue
        events.append(ScopeEvent(match.start(), "close", None, match.group("end_name")))
    return events


def top_level_positions(text: str, needle: str) -> list[int]:
    positions: list[int] = []
    depths = {"(": 0, "[": 0, "{": 0}
    closing = {")": "(", "]": "[", "}": "{"}
    index = 0
    while index < len(text):
        character = text[index]
        if character in depths:
            depths[character] += 1
        elif character in closing:
            opener = closing[character]
            depths[opener] = max(0, depths[opener] - 1)
        elif all(depth == 0 for depth in depths.values()) and text.startswith(
            needle, index
        ):
            positions.append(index)
            index += len(needle) - 1
        index += 1
    return positions


def strip_balanced_outer_parentheses(text: str) -> str:
    value = text.strip()
    while value.startswith("(") and value.endswith(")"):
        depth = 0
        closes_at_end = False
        for index, character in enumerate(value):
            if character == "(":
                depth += 1
            elif character == ")":
                depth -= 1
                if depth == 0:
                    closes_at_end = index == len(value) - 1
                    break
        if not closes_at_end:
            break
        value = value[1:-1].strip()
    return value


def conclusion_symbol(masked_statement: str, name: str) -> str | None:
    """Return the leading identifier of the final top-level consequent."""
    name_match = re.search(
        rf"(?<![A-Za-z0-9_']){re.escape(name)}(?![A-Za-z0-9_'])",
        masked_statement,
    )
    if name_match is None:
        return None
    suffix = masked_statement[name_match.end() :].rstrip()
    if suffix.endswith("."):
        suffix = suffix[:-1]
    colons = top_level_positions(suffix, ":")
    if not colons:
        return None
    proposition = suffix[colons[0] + 1 :].strip()

    changed = True
    while changed and proposition:
        changed = False
        proposition = strip_balanced_outer_parentheses(proposition)
        if re.match(r"^forall\b", proposition):
            commas = top_level_positions(proposition, ",")
            if commas:
                proposition = proposition[commas[0] + 1 :].strip()
                changed = True
                continue
        arrows = top_level_positions(proposition, "->")
        if arrows:
            proposition = proposition[arrows[-1] + 2 :].strip()
            changed = True

    proposition = strip_balanced_outer_parentheses(proposition)
    head = re.match(
        rf"@?(?P<head>{IDENTIFIER}(?:\.{IDENTIFIER})*)(?![A-Za-z0-9_'])",
        proposition,
    )
    return head.group("head") if head is not None else None


def declarations_from_source(
    path: Path,
    *,
    authority_root: Path,
    logical_prefix: tuple[str, ...],
    source_root: Path,
    content: bytes | None = None,
) -> list[Declaration]:
    try:
        # Parse the same bytes used for the cache key, not a second read that
        # could observe a different file. Preserve read_text's universal newlines.
        raw = path.read_bytes() if content is None else content
        text = raw.decode("utf-8").replace("\r\n", "\n").replace("\r", "\n")
    except (OSError, UnicodeError) as error:
        raise SearchError(f"cannot read {path}: {error}") from error
    try:
        masked = mask_comments_and_strings(text)
    except SearchError as error:
        raise SearchError(f"{path}: {error}") from error

    matches = list(DECLARATION.finditer(masked))
    events = scope_events(masked)
    event_index = 0
    scopes: list[tuple[str, str]] = []
    source_relative = path.relative_to(authority_root).as_posix()
    file_parts = path.relative_to(source_root).with_suffix("").parts
    declarations: list[Declaration] = []

    for position, match in enumerate(matches):
        while (
            event_index < len(events) and events[event_index].position < match.start()
        ):
            event = events[event_index]
            if event.action == "open":
                assert event.kind is not None
                scopes.append((event.kind, event.name))
            elif scopes and scopes[-1][1] == event.name:
                scopes.pop()
            event_index += 1

        qualifiers = match.group("qualifiers").split()
        if "Local" in qualifiers:
            continue
        try:
            end = sentence_end(masked, match.end())
        except SearchError as error:
            line = text.count("\n", 0, match.start()) + 1
            raise SearchError(f"{source_relative}:{line}: {error}") from error
        next_start = (
            matches[position + 1].start()
            if position + 1 < len(matches)
            else len(masked)
        )
        terminator = PROOF_TERMINATOR.search(masked, end + 1, next_start)
        if terminator is None or terminator.group(1) != "Qed":
            continue

        kind = match.group("kind")
        name = match.group("name")
        statement = text[match.start("kind") : end + 1].rstrip()
        masked_statement = masked[match.start("kind") : end + 1].rstrip()
        module_parts = (
            *logical_prefix,
            *file_parts,
            *(
                scope_name
                for scope_kind, scope_name in scopes
                if scope_kind == "module"
            ),
        )
        module = ".".join(module_parts)
        fqn = f"{module}.{name}"
        syntactic_symbols = set(QUALIFIED_IDENTIFIER.findall(masked_statement))
        # Rocq may print a goal head either fully qualified or through an open
        # module. Expose both spellings mechanically; this changes no ordering
        # and assigns neither spelling a preference.
        symbols = tuple(
            sorted(
                syntactic_symbols
                | {symbol.rsplit(".", 1)[-1] for symbol in syntactic_symbols}
            )
        )
        declarations.append(
            Declaration(
                fqn=fqn,
                name=name,
                kind=kind,
                module=module,
                source=source_relative,
                line=text.count("\n", 0, match.start("kind")) + 1,
                statement=statement,
                conclusion_symbol=conclusion_symbol(masked_statement, name),
                symbols=symbols,
            )
        )
    return declarations


def authority_source_roots(authority_root: Path) -> tuple[SourceRoot, ...]:
    candidates = (
        SourceRoot(authority_root / "vendor/FormalSQL/src", ("SQLFS",)),
        SourceRoot(authority_root / "theories/FormalSQL", ("Logos", "FormalSQL")),
    )
    available = tuple(candidate for candidate in candidates if candidate.path.is_dir())
    if not available:
        raise SearchError(
            "authority root contains neither vendor/FormalSQL/src nor theories/FormalSQL"
        )
    return available


def authority_sources(authority_root: Path) -> tuple[Path, list[SourceFile]]:
    try:
        root = authority_root.resolve(strict=True)
    except OSError as error:
        raise SearchError(
            f"invalid authority root {authority_root}: {error}"
        ) from error
    if not root.is_dir() or root.is_symlink():
        raise SearchError("authority root must be a real directory")

    sources: list[SourceFile] = []
    for source_root in authority_source_roots(root):
        paths = sorted(
            (
                path
                for path in source_root.path.rglob("*.v")
                if path.is_file() and not path.is_symlink()
            ),
            key=lambda path: path.relative_to(root).as_posix(),
        )
        for path in paths:
            try:
                sources.append(SourceFile(path, source_root, path.read_bytes()))
            except OSError as error:
                raise SearchError(f"cannot read {path}: {error}") from error
    return root, sources


def parse_sources(root: Path, sources: list[SourceFile]) -> list[Declaration]:
    declarations: list[Declaration] = []
    for source in sources:
        declarations.extend(
            declarations_from_source(
                source.path,
                authority_root=root,
                logical_prefix=source.root.logical_prefix,
                source_root=source.root.path,
                content=source.content,
            )
        )

    declarations.sort(
        key=lambda declaration: (declaration.fqn, declaration.source, declaration.line)
    )
    seen: set[str] = set()
    for declaration in declarations:
        if declaration.fqn in seen:
            raise SearchError(f"duplicate declaration FQN: {declaration.fqn}")
        seen.add(declaration.fqn)
    return declarations


def scan_authority(authority_root: Path) -> list[Declaration]:
    """Uncached reference implementation (also used by --no-cache)."""
    return parse_sources(*authority_sources(authority_root))


INDEX_SCHEMA = 1


def index_key(root: Path, sources: list[SourceFile]) -> str:
    digest = hashlib.sha256()

    def add(value: bytes) -> None:
        # Length framing prevents ambiguity between file paths and contents.
        digest.update(len(value).to_bytes(8, "big"))
        digest.update(value)

    add(f"logos-rocq-declarations-{INDEX_SCHEMA}".encode())
    # Any parser/filter implementation change invalidates the derived index.
    add(Path(__file__).read_bytes())
    for source in sources:
        add(source.path.relative_to(root).as_posix().encode())
        add(source.root.path.relative_to(root).as_posix().encode())
        add(".".join(source.root.logical_prefix).encode())
        add(source.content)
    return digest.hexdigest()


def json_bytes(value: object) -> bytes:
    return json.dumps(
        value, sort_keys=True, ensure_ascii=True, separators=(",", ":")
    ).encode("utf-8")


def private_cache_directory(path: Path) -> Path:
    path.mkdir(mode=0o700, parents=True, exist_ok=True)
    info = path.lstat()
    if (
        not stat.S_ISDIR(info.st_mode)
        or info.st_uid != os.getuid()
        or stat.S_IMODE(info.st_mode) & 0o077
    ):
        raise OSError("declaration cache must be an owned private directory")
    return path


def read_index(path: Path, key: str, sources: set[str]) -> list[Declaration]:
    # Never follow a cache-file symlink, including on platforms where the cache
    # directory could have been populated before this process started.
    descriptor = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    with os.fdopen(descriptor, "rb") as stream:
        info = os.fstat(stream.fileno())
        if not stat.S_ISREG(info.st_mode) or info.st_uid != os.getuid():
            raise ValueError("invalid index file")
        document = json.load(stream)
    if (
        not isinstance(document, dict)
        or document.get("schemaVersion") != INDEX_SCHEMA
        or document.get("key") != key
    ):
        raise ValueError("index binding mismatch")
    records = document.get("declarations")
    if (
        not isinstance(records, list)
        or document.get("recordsSha256")
        != hashlib.sha256(json_bytes(records)).hexdigest()
    ):
        raise ValueError("index checksum mismatch")
    declarations: list[Declaration] = []
    for record in records:
        if not isinstance(record, dict):
            raise ValueError("invalid declaration record")
        declaration = Declaration(**record)
        if (
            any(
                not isinstance(record[field], str)
                for field in ("fqn", "name", "kind", "module", "source", "statement")
            )
            or type(declaration.line) is not int
            or declaration.line < 1
            or declaration.source not in sources
            or declaration.kind not in ("Lemma", "Theorem", "Corollary")
            or declaration.fqn != f"{declaration.module}.{declaration.name}"
            or (
                declaration.conclusion_symbol is not None
                and not isinstance(declaration.conclusion_symbol, str)
            )
            or not isinstance(declaration.symbols, list)
            or any(not isinstance(symbol, str) for symbol in declaration.symbols)
            or declaration.symbols != sorted(set(declaration.symbols))
        ):
            raise ValueError("invalid declaration fields")
        declarations.append(
            Declaration(**{**record, "symbols": tuple(declaration.symbols)})
        )
    order = [(item.fqn, item.source, item.line) for item in declarations]
    if order != sorted(order) or len({item.fqn for item in declarations}) != len(order):
        raise ValueError("invalid declaration ordering or duplicate FQN")
    return declarations


def write_index(path: Path, key: str, declarations: list[Declaration]) -> None:
    records = [asdict(declaration) for declaration in declarations]
    document = {
        "schemaVersion": INDEX_SCHEMA,
        "key": key,
        "recordsSha256": hashlib.sha256(json_bytes(records)).hexdigest(),
        "declarations": records,
    }
    # Independent readers see either the previous complete index or the new
    # complete index. Concurrent cold builders are harmless; no lock can stall
    # a search after an interrupted writer.
    with tempfile.NamedTemporaryFile(
        dir=path.parent, prefix=".index-", delete=False
    ) as stream:
        temporary = Path(stream.name)
        try:
            stream.write(json_bytes(document))
            stream.flush()
            os.replace(temporary, path)
        finally:
            temporary.unlink(missing_ok=True)


def cached_authority(
    authority_root: Path, cache_dir: Path | None = None
) -> list[Declaration]:
    # Never trust mtime/size or a caller-supplied digest: check the complete
    # current source set and bytes even on a hit. In the proof container this
    # tree is already immutable, but the standalone CLI also supports edits.
    root, sources = authority_sources(authority_root)
    path: Path | None = None
    try:
        key = index_key(root, sources)
        directory = private_cache_directory(
            cache_dir
            if cache_dir is not None
            else Path(tempfile.gettempdir()) / f"logos-rocq-declarations-{os.getuid()}"
        )
        path = directory / f"{key}.json"
        return read_index(
            path, key, {source.path.relative_to(root).as_posix() for source in sources}
        )
    except (OSError, ValueError, TypeError, KeyError, RecursionError):
        # Derived, disposable data only. Missing/corrupt/unusable caches must
        # not change results or suppress source/parser errors.
        pass
    declarations = parse_sources(root, sources)
    if path is not None:
        try:
            write_index(path, key, declarations)
        except OSError:
            pass
    return declarations


def search_authority(
    authority_root: Path,
    *,
    filters: ExactFilters,
    page: int,
    page_size: int,
    show_statement: bool,
    cache_dir: Path | None = None,
    use_cache: bool = True,
) -> dict[str, object]:
    if page < 1:
        raise SearchError("page must be at least 1")
    if page_size < 1:
        raise SearchError("page size must be at least 1")
    surface = authority_root / "lemma-surface.json"
    if surface.is_file():
        index = json.loads(surface.read_text())
        if index.get("schemaVersion") != 1:
            raise SearchError("unsupported lemma surface version")
        declarations = [
            Declaration(**{**r, "symbols": tuple(r["symbols"])})
            for r in index["declarations"]
        ]
    else:
        declarations = (
            cached_authority(authority_root, cache_dir)
            if use_cache
            else scan_authority(authority_root)
        )
    matches = [
        declaration for declaration in declarations if filters.accepts(declaration)
    ]
    matched = len(matches)
    page_count = (matched + page_size - 1) // page_size
    start = (page - 1) * page_size
    selected = matches[start : start + page_size]
    return {
        "schemaVersion": 1,
        "authorityRoot": str(authority_root),
        "ordering": ["fqn", "source", "line"],
        "filters": filters.public_record(),
        "matched": matched,
        "page": page,
        "pageSize": page_size,
        "pageCount": page_count,
        "hasPrevious": page > 1 and matched > 0,
        "hasNext": page < page_count,
        "entries": [
            declaration.public_record(show_statement=show_statement)
            for declaration in selected
        ],
    }


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--authority-root",
        type=Path,
        default=Path(os.environ.get("LOGOS_REPO_ROOT", "/workspace/logos")),
        help="authority snapshot root (default: LOGOS_REPO_ROOT or /workspace/logos)",
    )
    parser.add_argument("--fqn", help="exact fully qualified declaration name")
    parser.add_argument("--name", help="exact unqualified declaration name")
    parser.add_argument("--module", help="exact fully qualified enclosing module")
    parser.add_argument("--source", help="exact authority-root-relative source path")
    parser.add_argument(
        "--conclusion-symbol",
        help="exact leading identifier of the final syntactic consequent",
    )
    parser.add_argument(
        "--symbol",
        action="append",
        default=[],
        help="exact statement identifier; repeat to require every symbol",
    )
    parser.add_argument("--page", type=int, default=1)
    parser.add_argument("--page-size", type=int, default=50)
    parser.add_argument("--show-statement", action="store_true")
    parser.add_argument(
        "--cache-dir",
        type=Path,
        help="private disposable index directory (default: $TMPDIR/logos-rocq-declarations-UID)",
    )
    parser.add_argument(
        "--no-cache",
        action="store_true",
        help="parse sources without reading/writing an index",
    )
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    arguments = parse_args(sys.argv[1:] if argv is None else argv)
    filters = ExactFilters(
        fqn=arguments.fqn,
        name=arguments.name,
        module=arguments.module,
        source=arguments.source,
        conclusion_symbol=arguments.conclusion_symbol,
        symbols=tuple(arguments.symbol),
    )
    try:
        result = search_authority(
            arguments.authority_root,
            filters=filters,
            page=arguments.page,
            page_size=arguments.page_size,
            show_statement=arguments.show_statement,
            cache_dir=arguments.cache_dir,
            use_cache=not arguments.no_cache,
        )
    except SearchError as error:
        print(f"Rocq declaration search failed: {error}", file=sys.stderr)
        return 2
    json.dump(result, sys.stdout, indent=2, ensure_ascii=False, sort_keys=True)
    sys.stdout.write("\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
