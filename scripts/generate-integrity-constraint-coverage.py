#!/usr/bin/env python3
"""Generate bounded, fail-closed coverage for the frozen integrity campaign."""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
import tempfile
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
MATERIALIZER_DIR = ROOT / "benchmarks/adapters/materializers"
if str(MATERIALIZER_DIR) not in sys.path:
    sys.path.insert(0, str(MATERIALIZER_DIR))

from materializer_sql import (  # noqa: E402
    MYSQL_MATERIALIZER_QUOTE_POLICY,
    mask_sql_regions,
    split_sql_statements,
)


COVERAGE_SCHEMA_VERSION = 1
DEFAULT_COHORT = "benchmarks/core/authority/cohort-389.json"
DEFAULT_METADATA_ROOT = "benchmarks/core/.generated/sqlsolver"
DEFAULT_OUTPUT = "var/integrity-constraint-coverage/coverage.json"
MAX_METADATA_BYTES = 2 * 1024 * 1024
MAX_SCHEMA_BYTES = 16 * 1024 * 1024
MAX_SIDECAR_BYTES = 32 * 1024 * 1024
FROZEN_TYPE_AUTHORITY = "parser_facing_normalized_ddl"
FROZEN_SIDECAR_AUTHORITY = "integrity_declarations_only"
FROZEN_SIDECAR_RAW_TYPE_SEMANTICS = (
    "sourceType/sourceDeclaration are authoritative for benchmark semantics; "
    "normalizedFrontendType is a tool-facing lowering."
)
FROZEN_SIDECAR_RAW_TYPE_SEMANTICS_DISPOSITION = (
    "preserved_for_audit_but_overridden_by_typeAuthority"
)
FROZEN_UNIQUE_SEMANTICS = "sql_unique_allows_multiple_nulls"
FROZEN_CONSTRAINT_SOURCES = {
    "uniqueIndexes": {"create_unique_index"},
    "foreignKeys": {"alter_table", "create_table"},
    "checks": {"create_table"},
}
FROZEN_FOREIGN_KEY_ACTIONS = {
    "",
    "ON DELETE CASCADE",
    "ON DELETE CASCADE ON UPDATE CASCADE",
    "ON DELETE RESTRICT",
    "ON DELETE SET NULL",
}

PAIR_KIND_MAP = {
    "not_null": "not_null",
    "primary": "primary_key",
    "foreign": "foreign_key",
}
SIDECAR_KIND_MAP = {
    "primaryKeys": "primary_key",
    "uniqueKeys": "unique",
    "uniqueIndexes": "partial_expression_unique_index",
    "foreignKeys": "foreign_key",
    "checks": "check",
}
REQUIRED_CONSTRAINT_KINDS = [
    "not_null",
    "primary_key",
    "unique",
    "foreign_key",
    "check",
    "partial_expression_unique_index",
]
SIDECAR_TOP_LEVEL_FIELDS = {
    "checks",
    "foreignKeys",
    "primaryKeys",
    "semanticSchema",
    "uniqueIndexes",
    "uniqueKeys",
    "unsupportedSemanticConstraints",
}
SIDECAR_ENTRY_FIELDS = {
    "primaryKeys": {"table", "columns"},
    "uniqueKeys": {"table", "columns", "nullableColumns", "semantics"},
    "uniqueIndexes": {"source", "table", "terms", "where"},
    "foreignKeys": {"actions", "columns", "refColumns", "refTable", "source", "table"},
    "checks": {"expression", "source", "table"},
}


class CoverageError(ValueError):
    pass


def require_object(value: Any, label: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise CoverageError(f"{label} must be a JSON object")
    return value


def read_json_bounded(path: Path, maximum_bytes: int) -> Any:
    if not path.is_file():
        raise CoverageError(f"missing {path}")
    size = path.stat().st_size
    if size > maximum_bytes:
        raise CoverageError(f"{path} is {size} bytes; bounded limit is {maximum_bytes}")
    try:
        return json.loads(path.read_text())
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise CoverageError(f"cannot read {path}: {error}") from error


def read_text_bounded(path: Path, maximum_bytes: int) -> str:
    if not path.is_file():
        raise CoverageError(f"missing {path}")
    size = path.stat().st_size
    if size > maximum_bytes:
        raise CoverageError(f"{path} is {size} bytes; bounded limit is {maximum_bytes}")
    try:
        return path.read_text()
    except (OSError, UnicodeDecodeError) as error:
        raise CoverageError(f"cannot read {path}: {error}") from error


def resolve_under_root(root: Path, value: str | Path, label: str) -> Path:
    root = root.resolve()
    path = Path(value)
    resolved = path.resolve() if path.is_absolute() else (root / path).resolve()
    try:
        resolved.relative_to(root)
    except ValueError as error:
        raise CoverageError(f"{label} escapes repository root: {value}") from error
    return resolved


def require_nonempty_string(value: Any, label: str) -> str:
    if not isinstance(value, str) or not value:
        raise CoverageError(f"{label} must be a nonempty string")
    return value


def require_string_list(value: Any, label: str, *, nonempty: bool) -> list[str]:
    if not isinstance(value, list) or any(
        not isinstance(item, str) or not item for item in value
    ):
        raise CoverageError(f"{label} must be a list of nonempty strings")
    if nonempty and not value:
        raise CoverageError(f"{label} must not be empty")
    return value


def validate_pair_endpoint(value: Any, label: str) -> None:
    endpoint = require_nonempty_string(value, label)
    if "__" not in endpoint or endpoint.startswith("__") or endpoint.endswith("__"):
        raise CoverageError(f"{label} is not a TABLE__COLUMN endpoint: {endpoint!r}")


def derive_pair_kinds(metadata: dict[str, Any], label: str) -> set[str]:
    constraints = metadata.get("constraints", [])
    if not isinstance(constraints, list):
        raise CoverageError(f"{label} constraints must be a list")
    kinds: set[str] = set()
    for index, constraint in enumerate(constraints):
        if not isinstance(constraint, dict) or len(constraint) != 1:
            raise CoverageError(
                f"{label} constraints[{index}] must have exactly one kind"
            )
        raw_kind, payload = next(iter(constraint.items()))
        kind = PAIR_KIND_MAP.get(raw_kind)
        if kind is None:
            raise CoverageError(
                f"{label} has unknown pair constraint kind {raw_kind!r}"
            )
        if raw_kind == "not_null":
            payload = require_object(payload, f"{label} constraints[{index}].not_null")
            if set(payload) != {"value"}:
                raise CoverageError(
                    f"{label} constraints[{index}].not_null is malformed"
                )
            validate_pair_endpoint(
                payload["value"], f"{label} constraints[{index}].value"
            )
        else:
            expected_length = 2 if raw_kind == "foreign" else None
            if not isinstance(payload, list) or not payload:
                raise CoverageError(
                    f"{label} constraints[{index}].{raw_kind} must be nonempty"
                )
            if expected_length is not None and len(payload) != expected_length:
                raise CoverageError(
                    f"{label} constraints[{index}].foreign must contain two endpoints"
                )
            for endpoint_index, endpoint in enumerate(payload):
                endpoint = require_object(
                    endpoint,
                    f"{label} constraints[{index}].{raw_kind}[{endpoint_index}]",
                )
                if set(endpoint) != {"value"}:
                    raise CoverageError(
                        f"{label} constraints[{index}].{raw_kind}[{endpoint_index}] is malformed"
                    )
                validate_pair_endpoint(
                    endpoint["value"],
                    f"{label} constraints[{index}].{raw_kind}[{endpoint_index}].value",
                )
        kinds.add(kind)
    return kinds


def derive_ddl_kinds(schema_sql: str, label: str) -> set[str]:
    kinds: set[str] = set()
    for index, statement in enumerate(
        split_sql_statements(
            schema_sql,
            quote_policy=MYSQL_MATERIALIZER_QUOTE_POLICY,
        )
    ):
        masked = mask_sql_regions(
            statement,
            quote_policy=MYSQL_MATERIALIZER_QUOTE_POLICY,
        ).upper()
        unsupported_patterns = {
            "EXCLUDE constraint": r"\bEXCLUDE\b",
            "NULLS NOT DISTINCT uniqueness": r"\bNULLS\s+NOT\s+DISTINCT\b",
            "non-SIMPLE foreign-key match": r"\bMATCH\s+(?:FULL|PARTIAL)\b",
            "deferrable constraint": r"\b(?:DEFERRABLE|INITIALLY)\b",
            "CREATE ASSERTION": r"\bCREATE\s+ASSERTION\b",
        }
        for description, pattern in unsupported_patterns.items():
            if re.search(pattern, masked):
                raise CoverageError(
                    f"{label} statement {index + 1} uses unsupported {description}"
                )
        is_unique_index = bool(re.search(r"\bCREATE\s+UNIQUE\s+INDEX\b", masked))
        if is_unique_index:
            kinds.add("partial_expression_unique_index")
        elif re.search(r"\bUNIQUE\b", masked):
            kinds.add("unique")
        if re.search(r"\bNOT\s+NULL\b", masked):
            kinds.add("not_null")
        if re.search(r"\bPRIMARY\s+KEY\b", masked):
            kinds.add("primary_key")
        if re.search(r"\bFOREIGN\s+KEY\b|\bREFERENCES\b", masked):
            kinds.add("foreign_key")
        if re.search(r"\bCHECK\s*\(", masked):
            kinds.add("check")
        if re.search(r"\bCONSTRAINT\b", masked) and not re.search(
            r"\b(?:PRIMARY\s+KEY|UNIQUE|FOREIGN\s+KEY|CHECK)\b",
            masked,
        ):
            raise CoverageError(
                f"{label} statement {index + 1} has an unrecognized CONSTRAINT form"
            )
    return kinds


def validate_sidecar_entry_fields(
    entry: dict[str, Any], field: str, label: str
) -> None:
    expected_fields = SIDECAR_ENTRY_FIELDS[field]
    missing = expected_fields - set(entry)
    unknown = set(entry) - expected_fields
    if missing or unknown:
        raise CoverageError(
            f"{label} fields mismatch; missing={sorted(missing)}, unknown={sorted(unknown)}"
        )
    require_nonempty_string(entry.get("table"), f"{label}.table")
    if field in {"primaryKeys", "uniqueKeys"}:
        columns = require_string_list(
            entry.get("columns"), f"{label}.columns", nonempty=True
        )
        if len(columns) != len(set(columns)):
            raise CoverageError(f"{label}.columns contains duplicates")
        if field == "uniqueKeys":
            nullable = require_string_list(
                entry.get("nullableColumns"),
                f"{label}.nullableColumns",
                nonempty=False,
            )
            if len(nullable) != len(set(nullable)):
                raise CoverageError(f"{label}.nullableColumns contains duplicates")
            if entry.get("semantics") != FROZEN_UNIQUE_SEMANTICS:
                raise CoverageError(
                    f"{label}.semantics must be {FROZEN_UNIQUE_SEMANTICS!r}"
                )
    elif field == "foreignKeys":
        columns = require_string_list(
            entry.get("columns"), f"{label}.columns", nonempty=True
        )
        referenced = require_string_list(
            entry.get("refColumns"), f"{label}.refColumns", nonempty=True
        )
        require_nonempty_string(entry.get("refTable"), f"{label}.refTable")
        if len(columns) != len(referenced):
            raise CoverageError(f"{label} has mismatched local/referenced arity")
        actions = entry.get("actions")
        if not isinstance(actions, str) or actions not in FROZEN_FOREIGN_KEY_ACTIONS:
            raise CoverageError(
                f"{label}.actions is outside the frozen action metadata"
            )
    elif field == "checks":
        require_nonempty_string(entry.get("expression"), f"{label}.expression")
    elif field == "uniqueIndexes":
        require_string_list(entry.get("terms"), f"{label}.terms", nonempty=True)
        if not isinstance(entry.get("where"), str):
            raise CoverageError(f"{label}.where must be a string")
    if field in FROZEN_CONSTRAINT_SOURCES:
        source = require_nonempty_string(entry.get("source"), f"{label}.source")
        if source not in FROZEN_CONSTRAINT_SOURCES[field]:
            raise CoverageError(
                f"{label}.source {source!r} is outside the frozen source discriminators"
            )


def require_sidecar_columns(
    semantic_columns: dict[tuple[str, str], bool],
    table: str,
    columns: list[str],
    label: str,
) -> None:
    for column in columns:
        if (table, column) not in semantic_columns:
            raise CoverageError(f"{label} references unknown column {table}.{column}")


def count_sidecar_type_lowerings(sidecar: dict[str, Any]) -> int:
    return sum(
        1
        for table in sidecar["semanticSchema"]["tables"]
        for column in table["columns"]
        if " ".join(str(column.get("sourceType", "")).split()).upper()
        != " ".join(str(column.get("normalizedFrontendType", "")).split()).upper()
    )


def derive_wetune_sidecar_kinds(
    root: Path,
    metadata: dict[str, Any],
    metadata_path: Path,
) -> set[str]:
    label = str(metadata_path.relative_to(root))
    app_name = require_nonempty_string(metadata.get("appName"), f"{label}.appName")
    semantic = require_object(
        metadata.get("semanticConstraints"), f"{label}.semanticConstraints"
    )
    source = require_nonempty_string(
        semantic.get("source"), f"{label}.semanticConstraints.source"
    )
    expected_source = (
        Path("benchmarks/core/wetune/schemas/core")
        / f"{app_name}.base.schema.constraints.json"
    )
    if Path(source) != expected_source:
        raise CoverageError(
            f"{label} selects {source!r}; frozen scope requires {expected_source.as_posix()!r}"
        )
    sidecar_path = resolve_under_root(root, source, f"{label} sidecar")
    sidecar = require_object(
        read_json_bounded(sidecar_path, MAX_SIDECAR_BYTES),
        str(sidecar_path.relative_to(root)),
    )
    if set(sidecar) != SIDECAR_TOP_LEVEL_FIELDS:
        missing = sorted(SIDECAR_TOP_LEVEL_FIELDS - set(sidecar))
        unknown = sorted(set(sidecar) - SIDECAR_TOP_LEVEL_FIELDS)
        raise CoverageError(
            f"{sidecar_path.relative_to(root)} sidecar fields mismatch; "
            f"missing={missing}, unknown={unknown}"
        )
    unsupported = sidecar["unsupportedSemanticConstraints"]
    if not isinstance(unsupported, list):
        raise CoverageError(
            f"{sidecar_path.relative_to(root)} unsupportedSemanticConstraints must be a list"
        )
    if unsupported:
        raise CoverageError(
            f"{sidecar_path.relative_to(root)} contains {len(unsupported)} unsupported forms"
        )

    kinds: set[str] = set()
    semantic_schema = require_object(
        sidecar["semanticSchema"],
        f"{sidecar_path.relative_to(root)}.semanticSchema",
    )
    if semantic_schema.get("typeSemantics") != FROZEN_SIDECAR_RAW_TYPE_SEMANTICS:
        raise CoverageError(
            f"{sidecar_path.relative_to(root)}.semanticSchema.typeSemantics does not "
            "match the frozen raw-source audit statement"
        )
    tables = semantic_schema.get("tables")
    if not isinstance(tables, list):
        raise CoverageError(
            f"{sidecar_path.relative_to(root)}.semanticSchema.tables must be a list"
        )
    semantic_columns: dict[tuple[str, str], bool] = {}
    table_names: set[str] = set()
    for table_index, table_value in enumerate(tables):
        table = require_object(
            table_value,
            f"{sidecar_path.relative_to(root)}.semanticSchema.tables[{table_index}]",
        )
        table_name = require_nonempty_string(
            table.get("name"), f"semantic table {table_index}.name"
        )
        if table_name in table_names:
            raise CoverageError(f"semantic schema repeats table {table_name!r}")
        table_names.add(table_name)
        columns = table.get("columns")
        if not isinstance(columns, list):
            raise CoverageError(f"semantic table {table_index}.columns must be a list")
        for column_index, column_value in enumerate(columns):
            column = require_object(
                column_value,
                f"semantic table {table_index}.columns[{column_index}]",
            )
            column_name = require_nonempty_string(
                column.get("name"), f"semantic column {column_index}.name"
            )
            not_null = column.get("notNull")
            if not isinstance(not_null, bool):
                raise CoverageError(
                    f"semantic column {column_index}.notNull must be Boolean"
                )
            key = (table_name, column_name)
            if key in semantic_columns:
                raise CoverageError(
                    f"semantic schema repeats column {table_name}.{column_name}"
                )
            semantic_columns[key] = not_null
            if not_null:
                kinds.add("not_null")

    expected_summary = {
        "columns": len(semantic_columns),
        "typeLowerings": count_sidecar_type_lowerings(sidecar),
        "primaryKeys": len(sidecar["primaryKeys"]),
        "uniqueKeys": len(sidecar["uniqueKeys"]),
        "uniqueIndexes": len(sidecar["uniqueIndexes"]),
        "foreignKeys": len(sidecar["foreignKeys"]),
        "checks": len(sidecar["checks"]),
        "unsupportedSemanticConstraints": 0,
        "includedInSqlsolverDdl": False,
    }
    for key, expected in expected_summary.items():
        if semantic.get(key) != expected:
            raise CoverageError(
                f"{label}.semanticConstraints.{key} is {semantic.get(key)!r}, "
                f"expected {expected!r} from the selected sidecar"
            )

    for field, kind in SIDECAR_KIND_MAP.items():
        entries = sidecar[field]
        if not isinstance(entries, list):
            raise CoverageError(
                f"{sidecar_path.relative_to(root)}.{field} must be a list"
            )
        for index, entry_value in enumerate(entries):
            entry = require_object(
                entry_value,
                f"{sidecar_path.relative_to(root)}.{field}[{index}]",
            )
            validate_sidecar_entry_fields(
                entry,
                field,
                f"{sidecar_path.relative_to(root)}.{field}[{index}]",
            )
            table = entry["table"]
            if table not in table_names:
                raise CoverageError(
                    f"{sidecar_path.relative_to(root)}.{field}[{index}] references "
                    f"unknown table {table!r}"
                )
            if field in {"primaryKeys", "uniqueKeys", "foreignKeys"}:
                columns = entry["columns"]
                require_sidecar_columns(
                    semantic_columns,
                    table,
                    columns,
                    f"{sidecar_path.relative_to(root)}.{field}[{index}]",
                )
            if field == "primaryKeys":
                nullable = [
                    column
                    for column in entry["columns"]
                    if not semantic_columns[(table, column)]
                ]
                if nullable:
                    raise CoverageError(
                        f"{sidecar_path.relative_to(root)}.{field}[{index}] has nullable "
                        f"primary-key columns {nullable}"
                    )
            elif field == "uniqueKeys":
                expected_nullable = [
                    column
                    for column in entry["columns"]
                    if not semantic_columns[(table, column)]
                ]
                if entry["nullableColumns"] != expected_nullable:
                    raise CoverageError(
                        f"{sidecar_path.relative_to(root)}.{field}[{index}].nullableColumns "
                        f"is inconsistent; expected {expected_nullable}"
                    )
            elif field == "foreignKeys":
                referenced_table = entry["refTable"]
                if referenced_table not in table_names:
                    raise CoverageError(
                        f"{sidecar_path.relative_to(root)}.{field}[{index}] references "
                        f"unknown table {referenced_table!r}"
                    )
                require_sidecar_columns(
                    semantic_columns,
                    referenced_table,
                    entry["refColumns"],
                    f"{sidecar_path.relative_to(root)}.{field}[{index}]",
                )
        if entries:
            kinds.add(kind)
    return kinds


def validate_contract_reference(metadata: dict[str, Any], label: str) -> None:
    contract = require_object(
        metadata.get("integrityContract"), f"{label}.integrityContract"
    )
    if contract.get("authoritativeForLogos") is not True:
        raise CoverageError(
            f"{label} does not identify an authoritative Logos contract"
        )
    if contract.get("silentDrops") != 0:
        raise CoverageError(
            f"{label} does not report zero contract-source silent drops"
        )
    if metadata.get("sourceBenchmark") == "wetune-issues":
        if contract.get("sourceKind") != "wetune_base_schema_sidecar":
            raise CoverageError(f"{label} has the wrong WeTune integrity source kind")
        semantic = require_object(
            metadata.get("semanticConstraints"), f"{label}.semanticConstraints"
        )
        if contract.get("typeAuthority") != FROZEN_TYPE_AUTHORITY:
            raise CoverageError(f"{label} has the wrong frozen type authority")
        if contract.get("sidecarAuthority") != FROZEN_SIDECAR_AUTHORITY:
            raise CoverageError(f"{label} has the wrong frozen sidecar authority")
        if contract.get("sidecarRawTypeSemantics") != FROZEN_SIDECAR_RAW_TYPE_SEMANTICS:
            raise CoverageError(
                f"{label} does not preserve the raw sidecar type statement"
            )
        if (
            contract.get("sidecarRawTypeSemanticsDisposition")
            != FROZEN_SIDECAR_RAW_TYPE_SEMANTICS_DISPOSITION
        ):
            raise CoverageError(
                f"{label} does not record that normalized type authority overrides "
                "the preserved raw sidecar statement"
            )
        if contract.get("parserFacingDdl") != "schema.sql":
            raise CoverageError(f"{label} has the wrong parser-facing DDL source")
        if contract.get("semanticSidecar") != semantic.get("source"):
            raise CoverageError(
                f"{label} integrity sidecar disagrees with semanticConstraints.source"
            )
        if contract.get("identifierRenames") != "metadata.json#/renamedIdentifiers":
            raise CoverageError(
                f"{label} does not bind renamedIdentifiers into its contract"
            )
        renames = metadata.get("renamedIdentifiers")
        if not isinstance(renames, dict) or any(
            not isinstance(key, str) or not isinstance(value, str)
            for key, value in renames.items()
        ):
            raise CoverageError(f"{label}.renamedIdentifiers must be a string map")
        if contract.get("sqlsolverDdlComplete") is not False:
            raise CoverageError(f"{label} must record the SQLSolver DDL limitation")
    else:
        sources = contract.get("sources")
        if not isinstance(sources, list) or not sources:
            raise CoverageError(f"{label} contract sources must be a nonempty list")
        source_pairs = {
            (item.get("kind"), item.get("path"))
            for item in sources
            if isinstance(item, dict)
        }
        if ("parser_facing_ddl", "schema.sql") not in source_pairs:
            raise CoverageError(f"{label} contract omits parser-facing DDL")
        if (
            metadata.get("constraintScope") == "pair"
            and (
                "pair_metadata",
                "metadata.json#/constraints",
            )
            not in source_pairs
        ):
            raise CoverageError(f"{label} contract omits same-row pair metadata")


def generate_coverage(
    *,
    root: Path,
    cohort_path: Path,
    metadata_root: Path,
    aligned: bool,
) -> dict[str, Any]:
    root = root.resolve()
    cohort_path = resolve_under_root(root, cohort_path, "cohort path")
    metadata_root = resolve_under_root(root, metadata_root, "metadata root")
    cohort = require_object(
        read_json_bounded(cohort_path, MAX_METADATA_BYTES), "cohort"
    )
    expected_cases = require_string_list(
        cohort.get("cases"),
        "cohort.cases",
        nonempty=True,
    )
    if len(expected_cases) != len(set(expected_cases)):
        raise CoverageError("cohort.cases contains duplicates")
    if cohort.get("caseCount") != len(expected_cases):
        raise CoverageError("cohort.caseCount does not match cohort.cases")
    expected_case_set = set(expected_cases)
    required_order = REQUIRED_CONSTRAINT_KINDS

    metadata_paths = sorted(metadata_root.glob("**/metadata.json"))
    if len(metadata_paths) != len(expected_cases):
        raise CoverageError(
            f"cohort requires {len(expected_cases)} metadata rows, "
            f"found {len(metadata_paths)}"
        )
    cases: list[dict[str, Any]] = []
    seen_authority_cases: set[str] = set()
    allowed_kinds = set(required_order)
    for metadata_path in metadata_paths:
        label = str(metadata_path.relative_to(root))
        metadata = require_object(
            read_json_bounded(metadata_path, MAX_METADATA_BYTES),
            label,
        )
        case_id = require_nonempty_string(
            metadata.get("flatCaseId"), f"{label}.flatCaseId"
        )
        relative_parts = metadata_path.relative_to(metadata_root).parts
        if len(relative_parts) < 3:
            raise CoverageError(f"metadata path has no profile/case layout: {label}")
        profile = relative_parts[0]
        if profile == "nonwetune-flat":
            authority_case_id = f"nonwetune-flat__{case_id}"
        elif profile == "wetune-issues":
            authority_case_id = case_id
        else:
            raise CoverageError(f"unknown metadata profile {profile!r} in {label}")
        if authority_case_id in seen_authority_cases:
            raise CoverageError(f"duplicate authority case {authority_case_id!r}")
        if authority_case_id not in expected_case_set:
            raise CoverageError(f"case {authority_case_id!r} is absent from the cohort")
        seen_authority_cases.add(authority_case_id)
        validate_contract_reference(metadata, label)

        kinds = derive_pair_kinds(metadata, label)
        schema_path = metadata_path.with_name("schema.sql")
        schema_sql = read_text_bounded(schema_path, MAX_SCHEMA_BYTES)
        kinds.update(derive_ddl_kinds(schema_sql, str(schema_path.relative_to(root))))
        if metadata.get("sourceBenchmark") == "wetune-issues":
            kinds.update(derive_wetune_sidecar_kinds(root, metadata, metadata_path))
        unknown_kinds = kinds - allowed_kinds
        if unknown_kinds:
            raise CoverageError(
                f"{case_id} derives unknown kinds {sorted(unknown_kinds)}"
            )
        ordered_kinds = [kind for kind in required_order if kind in kinds]
        cases.append(
            {
                "case_id": case_id,
                "status": "modeled" if ordered_kinds else "no_integrity_constraints",
                "constraint_kinds": ordered_kinds,
                "unresolved_constraints": [],
                "silent_drops": 0 if aligned else None,
                "rocq_aligned": aligned,
                "validator_aligned": aligned,
                "agent_context_aligned": aligned,
            }
        )
    missing_cases = expected_case_set - seen_authority_cases
    if missing_cases:
        raise CoverageError(f"cohort cases have no metadata: {sorted(missing_cases)}")
    cases.sort(key=lambda entry: entry["case_id"])
    return {
        "schemaVersion": COVERAGE_SCHEMA_VERSION,
        "cases": cases,
        "unresolved_benchmark_constraints": [],
        "silent_drops": 0 if aligned else None,
    }


def write_json_atomic(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary_name: str | None = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="w",
            encoding="utf-8",
            dir=path.parent,
            prefix=f".{path.name}.",
            suffix=".tmp",
            delete=False,
        ) as handle:
            temporary_name = handle.name
            json.dump(value, handle, indent=2, sort_keys=False)
            handle.write("\n")
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary_name, path)
        temporary_name = None
    finally:
        if temporary_name is not None:
            Path(temporary_name).unlink(missing_ok=True)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate exact frozen integrity-constraint coverage. Alignment claims and "
            "zero silent-drop values require the explicit --aligned attestation."
        )
    )
    parser.add_argument("--root", default=str(ROOT))
    parser.add_argument("--cohort", default=DEFAULT_COHORT)
    parser.add_argument("--metadata-root", default=DEFAULT_METADATA_ROOT)
    parser.add_argument("--output", default=DEFAULT_OUTPUT)
    parser.add_argument(
        "--aligned",
        action="store_true",
        help="Attest that Rocq, validator, and agent-context checks have passed.",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        root = Path(args.root).resolve()
        coverage = generate_coverage(
            root=root,
            cohort_path=Path(args.cohort),
            metadata_root=Path(args.metadata_root),
            aligned=args.aligned,
        )
        output = resolve_under_root(root, args.output, "output path")
        write_json_atomic(output, coverage)
    except CoverageError as error:
        print(f"coverage generation failed: {error}", file=sys.stderr)
        return 1
    print(
        f"wrote {len(coverage['cases'])} cases to {output.relative_to(root)} "
        f"(aligned={args.aligned})",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
