#!/usr/bin/env python3
"""Canonical digest of the dirty Logos source tree, including submodules."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import tempfile
from pathlib import Path
from typing import Any


EXCLUDED_PREFIXES = (
    ".cache/",
    ".pytest_cache/",
    ".ruff_cache/",
    # `run-logos` consumes an already generated benchmark input tree.  The
    # materializers are upstream producers of that tree, not part of the
    # solver/proof/checker authority closure.  Binding their dirty work here
    # makes an unrelated preprocessing edit interrupt an in-flight proof run
    # even though every selected schema/sql1/sql2 file is bound separately by
    # the input manifest.
    "benchmarks/adapters/materializers/",
    "logs/",
    "target/",
    "var/",
)
EXCLUDED_DIRECTORY_NAMES = {
    ".cache",
    ".opam-rocq",
    ".pytest_cache",
    ".ruff_cache",
    "_build",
    "build",
    "dist",
    "logs",
    "node_modules",
    "target",
}
EXCLUDED_NAMES = {
    ".Makefile.rocq.d",
    "Makefile.rocq",
    "Makefile.rocq.conf",
}
EXCLUDED_SUFFIXES = (".aux", ".glob", ".vo", ".vok", ".vos")


class SourceTreeError(RuntimeError):
    pass


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def sha256_text(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def git_output(repository: Path, *arguments: str) -> bytes:
    completed = subprocess.run(
        ["git", "-C", str(repository), *arguments],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if completed.returncode != 0:
        diagnostic = completed.stderr.decode("utf-8", errors="replace").strip()
        raise SourceTreeError(
            f"git {' '.join(arguments)} failed in {repository} with exit code "
            f"{completed.returncode}: {diagnostic}"
        )
    return completed.stdout


def excluded(relative: str) -> bool:
    path = Path(relative)
    normalized = path.as_posix()
    return (
        any(
            normalized == prefix[:-1] or normalized.startswith(prefix)
            for prefix in EXCLUDED_PREFIXES
        )
        or any(part in EXCLUDED_DIRECTORY_NAMES for part in path.parts[:-1])
        or path.name in EXCLUDED_NAMES
        or path.name.endswith(EXCLUDED_SUFFIXES)
        or "__pycache__" in path.parts
    )


def source_path_record(repository: Path, relative: str) -> dict[str, Any]:
    path = repository / relative
    try:
        metadata = path.lstat()
    except FileNotFoundError:
        return {"path": relative, "kind": "missing"}
    if path.is_symlink():
        target = os.readlink(path)
        return {
            "path": relative,
            "kind": "symlink",
            "targetSha256": sha256_text(target),
            "targetBytes": len(target.encode("utf-8")),
        }
    if path.is_file():
        return {
            "path": relative,
            "kind": "file",
            "sha256": sha256_file(path),
            "bytes": metadata.st_size,
            "executable": bool(metadata.st_mode & 0o111),
        }
    return {"path": relative, "kind": "other"}


def repository_manifest(repository: Path, workspace_relative: str) -> dict[str, Any]:
    repository = repository.resolve()
    head = git_output(repository, "rev-parse", "HEAD").decode("ascii").strip()
    changed = set(
        filter(
            None,
            git_output(
                repository,
                "diff",
                "--name-only",
                "-z",
                "--no-renames",
                "--ignore-submodules=all",
                "HEAD",
                "--",
            )
            .decode("utf-8", errors="surrogateescape")
            .split("\0"),
        )
    )
    changed.update(
        filter(
            None,
            git_output(repository, "ls-files", "-z", "--others", "--exclude-standard")
            .decode("utf-8", errors="surrogateescape")
            .split("\0"),
        )
    )
    entries = [
        source_path_record(repository, path)
        for path in sorted(changed)
        if not excluded(path)
    ]

    submodules: list[dict[str, Any]] = []
    for raw in git_output(repository, "ls-files", "--stage", "-z").split(b"\0"):
        if not raw:
            continue
        metadata, separator, raw_path = raw.partition(b"\t")
        if not separator or not metadata.startswith(b"160000 "):
            continue
        relative = raw_path.decode("utf-8", errors="surrogateescape")
        if excluded(relative):
            continue
        fields = metadata.decode("ascii").split()
        index_object = fields[1] if len(fields) >= 2 else None
        submodule = repository / relative
        if not submodule.is_dir():
            submodules.append(
                {
                    "path": relative,
                    "kind": "missing-submodule",
                    "indexObject": index_object,
                    "dirty": True,
                }
            )
            continue
        nested = repository_manifest(submodule, f"{workspace_relative}/{relative}")
        nested["path"] = relative
        nested["indexObject"] = index_object
        submodules.append(nested)
    submodules.sort(key=lambda value: value["path"])
    return {
        "path": workspace_relative,
        "head": head,
        "dirty": bool(
            entries
            or any(
                value.get("dirty") or value.get("head") != value.get("indexObject")
                for value in submodules
            )
        ),
        "entries": entries,
        "submodules": submodules,
    }


def build_manifest(
    repository: Path, workspace_relative: str = "Logos"
) -> dict[str, Any]:
    return {
        "schemaVersion": 1,
        "kind": "canonical-dirty-source-tree",
        "excluded": {
            "prefixes": list(EXCLUDED_PREFIXES),
            "directoryNames": sorted(EXCLUDED_DIRECTORY_NAMES),
            "names": sorted(EXCLUDED_NAMES),
            "suffixes": list(EXCLUDED_SUFFIXES),
        },
        "repository": repository_manifest(repository, workspace_relative),
    }


def canonical_bytes(value: dict[str, Any]) -> bytes:
    return (json.dumps(value, indent=2, ensure_ascii=True) + "\n").encode("utf-8")


def manifest_sha256(value: dict[str, Any]) -> str:
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def atomic_write(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{path.name}.", dir=path.parent
    )
    temporary = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(data)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    finally:
        try:
            temporary.unlink()
        except FileNotFoundError:
            pass


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--repository",
        type=Path,
        default=Path(__file__).resolve().parents[1],
    )
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    manifest = build_manifest(args.repository)
    atomic_write(args.output, canonical_bytes(manifest))
    print(manifest_sha256(manifest))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
