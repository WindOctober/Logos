"""Load machine-local Logos configuration without evaluating shell code."""

from __future__ import annotations

import ast
import os
import re
from pathlib import Path


_ENVIRONMENT_NAME = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")


class LogosEnvironmentError(ValueError):
    """The repository-local .env file is malformed."""


def load_logos_env(logos_root: Path) -> Path | None:
    """Load ``<logos_root>/.env`` while preserving explicit process values."""

    path = logos_root / ".env"
    if not path.exists():
        return None
    if path.is_symlink() or not path.is_file():
        raise LogosEnvironmentError(f"Logos .env is not a regular file: {path}")

    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except OSError as error:
        raise LogosEnvironmentError(f"cannot read Logos .env: {error}") from error

    for line_number, raw_line in enumerate(lines, start=1):
        line = raw_line.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("export "):
            line = line[len("export ") :].lstrip()
        if "=" not in line:
            raise LogosEnvironmentError(f"{path}:{line_number}: expected NAME=VALUE")
        name, raw_value = line.split("=", 1)
        name = name.strip()
        if not _ENVIRONMENT_NAME.fullmatch(name):
            raise LogosEnvironmentError(
                f"{path}:{line_number}: invalid environment name {name!r}"
            )
        value = _parse_value(path, line_number, raw_value.strip())
        os.environ.setdefault(name, value)
    return path


def configured_path(
    logos_root: Path,
    name: str,
    *,
    default: Path | None = None,
    required: bool = False,
) -> Path | None:
    """Resolve a configured path, interpreting relative values from Logos."""

    value = os.environ.get(name)
    if value is None or not value.strip():
        if default is not None:
            return default.resolve()
        if required:
            raise LogosEnvironmentError(
                f"{name} is unset; configure it in {logos_root / '.env'}"
            )
        return None
    path = Path(value).expanduser()
    if not path.is_absolute():
        path = logos_root / path
    return path.resolve()


def _parse_value(path: Path, line_number: int, value: str) -> str:
    if not value:
        return ""
    if value[0] not in {"'", '"'}:
        return value
    try:
        parsed = ast.literal_eval(value)
    except (SyntaxError, ValueError) as error:
        raise LogosEnvironmentError(
            f"{path}:{line_number}: malformed quoted value"
        ) from error
    if not isinstance(parsed, str):
        raise LogosEnvironmentError(
            f"{path}:{line_number}: quoted value must be a string"
        )
    return parsed
