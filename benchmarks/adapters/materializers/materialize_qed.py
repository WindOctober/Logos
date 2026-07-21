#!/usr/bin/env python3
import argparse
import importlib.util
from importlib.machinery import SourceFileLoader
import json
import re
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

try:
    from materializer_sql import (
        ASCII_SQL_WHITESPACE_PATTERN,
        POSTGRES_IDENTIFIER_CONTINUATION_CLASS,
        mask_sql_regions,
        parse_schema,
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
        split_top_level_commas,
        strip_sql_comments,
        substitute_unprotected,
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
    parser.add_argument("--case", action="append", help="Case id regex. May be repeated.")
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
                status = materialize_case(config, case, output_dir, skip_parser=args.skip_parser)
                materialized += 1
                if not args.skip_parser and status != "parsed":
                    parser_failed += 1
                print(f"materialized {benchmark_id}/{case.case_id}: {status}", file=sys.stderr)
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
        print("failed: the selected QED materialization produced zero cases", file=sys.stderr)
    return 1 if failed or materialized == 0 else 0


def remove_selected_outputs(output_dir: Path, target: str) -> None:
    if target == "all":
        if output_dir.exists():
            shutil.rmtree(output_dir)
        return
    selected = output_dir / ("wetune-issues" if target == "wetune" else "nonwetune-flat")
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
    return any(pattern.search(case.case_id) or pattern.search(flat_case_id) for pattern in patterns)


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


def materialize_case(
    config: dict[str, Any],
    case: Any,
    output_dir: Path,
    skip_parser: bool,
) -> str:
    benchmark_id = case.benchmark["id"]
    flat_case_id = flat_id(benchmark_id, case.case_id)
    case_dir = output_dir / ("wetune-issues" if benchmark_id == "wetune-issues" else "nonwetune-flat") / flat_case_id
    if benchmark_id == "wetune-issues":
        case_dir = output_dir / "wetune-issues" / case.case_id
    case_dir.mkdir(parents=True, exist_ok=True)

    read_dialect = case.read_dialect or case.benchmark.get("readDialect") or "postgres"
    write_dialect = "postgres"
    adapter = case.benchmark.get("adapter", config["defaults"].get("adapter", "none"))

    with tempfile.TemporaryDirectory(prefix="logos-qed-") as tmp:
        tmp_dir = Path(tmp)
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
        quote_schema_identifiers = adapter == "sqlglot" or benchmark_id == "wetune-issues"
        schema_sql, constraint_coverage = render_qed_schema(
            case.schema_sql,
            before_sql + "\n" + after_sql,
            quote_identifiers=quote_schema_identifiers,
            constraints=case.constraints,
        )

    qed_sql = schema_sql + "\n" + ensure_sql_terminated(before_sql) + ensure_sql_terminated(after_sql)
    qed_sql = patch_qed_interval_precision(qed_sql)
    write_text(case_dir / "qed.sql", qed_sql)

    parser_status = {"skipped": True} if skip_parser else run_qed_parser(case_dir / "qed.sql")
    parser_problem = None if skip_parser else classify_qed_parser_problem(parser_status)
    json_repair = None
    if (
        not skip_parser
        and parser_problem is None
        and parser_status.get("jsonExists")
    ):
        try:
            json_repair = repair_qed_json(
                case_dir / "qed.json",
                expected_table_keys=constraint_coverage["renderedKeys"],
            )
            apply_qed_json_repair_coverage(constraint_coverage, json_repair)
        except QedJsonRepairError as exc:
            json_repair = {"status": "error", "message": str(exc)}
            parser_problem = {"kind": "parser-error", "message": str(exc)}
    if parser_problem and (case_dir / "qed.json").exists():
        (case_dir / "qed.json").unlink()
        parser_status["jsonExists"] = False
    status = (
        "not-parsed"
        if skip_parser
        else ("parsed" if parser_status.get("jsonExists") and parser_problem is None else "parser-error")
    )

    write_text(
        case_dir / "metadata.json",
        json.dumps(
            {
                **build_metadata(config, case, flat_case_id),
                "profile": "qed",
                "status": status,
                "qedInput": "qed.sql",
                "qedJson": "qed.json" if (case_dir / "qed.json").exists() else None,
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
                "constraintCompatibility": constraint_coverage["compatibility"],
                "constraintCoverage": constraint_coverage,
                "qedJsonRepair": json_repair,
                "parser": parser_status,
                "parserProblem": parser_problem,
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
    for generated in ("qed.json", "qed.rkt"):
        path = case_dir / generated
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
    write_text(case_dir / "qed-parser.stdout.log", started.stdout)
    write_text(case_dir / "qed-parser.stderr.log", started.stderr)
    return {
        "command": command,
        "returnCode": started.returncode,
        "jsonExists": (case_dir / "qed.json").exists(),
        "rktExists": (case_dir / "qed.rkt").exists(),
        "stdoutTail": tail(started.stdout),
        "stderrTail": tail(started.stderr),
    }


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
            raise QedJsonRepairError(f"cannot read QED metadata {metadata_file}: {exc}") from exc
        if not isinstance(loaded_metadata, dict):
            raise QedJsonRepairError(f"QED metadata is not an object: {metadata_file}")
        metadata = loaded_metadata
        if expected_table_keys is None:
            coverage = metadata.get("constraintCoverage")
            if not isinstance(coverage, dict) or not isinstance(coverage.get("renderedKeys"), list):
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
        table_expected["keys"].append(
            {"kind": kind, "columns": list(columns)}
        )

    try:
        document = json.loads(json_path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        raise QedJsonRepairError(f"cannot read QED JSON {json_path}: {exc}") from exc
    if not isinstance(document, dict) or not isinstance(document.get("schemas"), list):
        raise QedJsonRepairError(f"QED JSON has no schema array: {json_path}")

    schemas_by_name: dict[str, dict[str, Any]] = {}
    for raw_schema in document["schemas"]:
        if not isinstance(raw_schema, dict) or not isinstance(raw_schema.get("name"), str):
            raise QedJsonRepairError("QED JSON contains a schema without a string name")
        raw_keys = raw_schema.get("key")
        if (
            not isinstance(raw_keys, list)
            or any(
                not isinstance(key, list)
                or any(not isinstance(index, int) or isinstance(index, bool) for index in key)
                for key in raw_keys
            )
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
    }
    try:
        json_path.write_text(
            json.dumps(document, indent=2, ensure_ascii=False, sort_keys=True) + "\n"
        )
    except OSError as exc:
        raise QedJsonRepairError(f"cannot write repaired QED JSON {json_path}: {exc}") from exc

    if metadata is not None and metadata_file is not None:
        coverage = metadata.get("constraintCoverage")
        if not isinstance(coverage, dict):
            raise QedJsonRepairError(
                "QED metadata lacks an object-valued constraintCoverage"
            )
        apply_qed_json_repair_coverage(coverage, attestation)
        metadata["constraintCompatibility"] = coverage["compatibility"]
        metadata["qedJsonRepair"] = attestation
        metadata["qedJson"] = json_path.name
        try:
            metadata_file.write_text(
                json.dumps(metadata, indent=2, ensure_ascii=False, sort_keys=True) + "\n"
            )
        except OSError as exc:
            raise QedJsonRepairError(
                f"cannot record QED JSON repair in {metadata_file}: {exc}"
            ) from exc
    return attestation


def classify_qed_parser_problem(parser_status: dict[str, Any]) -> dict[str, str] | None:
    text = "\n".join(
        str(parser_status.get(key, ""))
        for key in ("stdoutTail", "stderrTail")
    )
    if not text.strip():
        return None
    patterns = [
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
                "message": match.group(1).strip() if match.groups() else match.group(0).strip(),
            }
    return None


def build_metadata(config: dict[str, Any], case: Any, flat_case_id: str) -> dict[str, Any]:
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
        "semanticProfile": benchmark.get("semanticProfile", defaults["semanticProfile"]),
        "bagSemantics": benchmark.get("bagSemantics", defaults["bagSemantics"]),
        "nullSemantics": benchmark.get("nullSemantics", defaults["nullSemantics"]),
        "featureTags": case.feature_tags,
    }


def render_qed_schema(
    schema_sql: str,
    query_sql: str,
    quote_identifiers: bool,
    constraints: Any = None,
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
        "applied": [
            entry
            for table in tables
            for entry in table.applied_constraints
        ],
        "omitted": [
            entry
            for table in tables
            for entry in table.omitted_constraints
        ],
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

    rendered = []
    for table in tables:
        declarations = []
        for column in table.columns:
            suffix = " NOT NULL" if column.not_null else ""
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
        table.name.lower() for table in tables if identifier_is_referenced(query_sql, table.name)
    )
    selected = [
        table
        for table in tables
        if not referenced_tables or table.name.lower() in referenced_tables
    ]
    return selected or list(tables)


def identifier_is_referenced(sql: str, identifier: str, forbid_preceding_dot: bool = False) -> bool:
    quoted = quote_identifier(identifier)
    quoted_prefix = r"(?<!\.)" if forbid_preceding_dot else ""
    if re.search(rf"{quoted_prefix}{re.escape(quoted)}(?!\s*\.)", sql):
        return True
    bare_prefix = r"(?<![.A-Za-z0-9_])" if forbid_preceding_dot else r"(?<![A-Za-z0-9_])"
    return bool(re.search(rf"(?is){bare_prefix}{re.escape(identifier)}(?![A-Za-z0-9_])", sql))


def collect_table_aliases(sql: str) -> dict[str, str]:
    aliases: dict[str, str] = {}
    relation_re = re.compile(
        r'(?is)(?:\bFROM\b|\bJOIN\b)\s*'
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


def deduplicate_constraint_entries(entries: list[dict[str, Any]]) -> list[dict[str, Any]]:
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
    return next((column for column in table.columns if column.name.casefold() == folded), None)


def canonical_key(table: Table, columns: list[str] | tuple[str, ...]) -> tuple[str, ...] | None:
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


def apply_primary_key(table: Table, columns: list[str] | tuple[str, ...]) -> tuple[str, ...] | None:
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


def apply_unique_key(table: Table, columns: list[str] | tuple[str, ...]) -> tuple[str, ...] | None:
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
        table.columns.append(Column(name=name, type_sql=normalize_type_for_qed(rest), not_null=not_null))
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
        selected_owner = selected.get(owner.name.casefold()) if owner is not None else None
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
                or any(table.name.casefold() != owner.name.casefold() for table, _, _ in resolved)
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
                        rawReferences=[value for _, _, value in resolved if value is not None],
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
        if not isinstance(raw_table, dict) or not isinstance(raw_table.get("name"), str):
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
                add_applied_constraint(
                    coverage, "not_null", source, table, [canonical]
                )

    for raw_key in constraints.get("primaryKeys") or []:
        if not isinstance(raw_key, dict) or not isinstance(raw_key.get("table"), str):
            continue
        table = selected.get(raw_key["table"].casefold())
        if table is None:
            continue
        columns = raw_key.get("columns") or []
        key = apply_primary_key(table, columns) if all(isinstance(item, str) for item in columns) else None
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
        if not isinstance(raw_index, dict) or not isinstance(raw_index.get("table"), str):
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
        if not isinstance(raw_foreign, dict) or not isinstance(raw_foreign.get("table"), str):
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
        if not isinstance(raw_check, dict) or not isinstance(raw_check.get("table"), str):
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
        table_name = raw_unsupported.get("table") if isinstance(raw_unsupported, dict) else None
        table = selected.get(table_name.casefold()) if isinstance(table_name, str) else None
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
        apply_pair_constraint_metadata(selected_tables, all_tables, constraints, coverage)
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


def patch_qed_sql(sql: str) -> str:
    return patch_qed_interval_precision(strip_sql_comments(sql))


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


def tail(text: str, limit: int = 4000) -> str:
    return text[-limit:]


if __name__ == "__main__":
    raise SystemExit(main())
