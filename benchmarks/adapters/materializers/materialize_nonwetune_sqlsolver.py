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
from pathlib import Path
from typing import Any

from calcite_postgres_coercions import materialize_calcite_coercions
from materializer_sql import normalize_sql_layout
from solver_frontend import (
    SQLSOLVER_POSTGRES_IDENTIFIER_POLICY,
    SQLSOLVER_PREFLIGHT_POLICY,
    materialize_sqlsolver_query,
    pair_preservation_established,
    solver_materialization_config,
)
from sqlsolver_schema_constraints import materialize_pair_constraints


ROOT = Path(__file__).resolve().parents[3]
EXPORTER_PATH = ROOT / "scripts/export-benchmark-ir"
DEFAULT_CONFIG = "benchmarks/core/ingestion.json"
DEFAULT_OUTPUT = "benchmarks/core/.generated/sqlsolver/nonwetune-flat"
CALCITE_IR_ROOT = ROOT / "benchmarks/core/.generated/calcite-ir"
EXCLUDED_BENCHMARKS = {"wetune-issues"}


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Materialize non-WeTune benchmark cases as SQLSolver inputs. "
            "Query SQL follows the Calcite-ingestion adapter policy; schema DDL is "
            "lowered through SQLGlot to MySQL syntax for SQLSolver's DDL frontend."
        )
    )
    parser.add_argument("--config", default=DEFAULT_CONFIG)
    parser.add_argument("--output-dir", default=DEFAULT_OUTPUT)
    parser.add_argument("--benchmark", action="append")
    parser.add_argument(
        "--case", action="append", help="Case id regex. May be repeated."
    )
    parser.add_argument("--limit", type=int)
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args()

    exporter = load_exporter()
    config_path = resolve_path(args.config)
    config = json.loads(config_path.read_text())
    output_dir = resolve_path(args.output_dir)
    selected = set(args.benchmark or [])
    case_patterns = [re.compile(pattern) for pattern in args.case or []]

    if args.force and output_dir.exists():
        shutil.rmtree(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    materialized = 0
    failed = 0
    for benchmark in config["benchmarks"]:
        benchmark_id = benchmark["id"]
        if benchmark_id in EXCLUDED_BENCHMARKS:
            continue
        if selected and benchmark_id not in selected:
            continue
        for case in exporter.iter_cases(config, benchmark):
            if case_patterns and not any(
                pattern.search(case.case_id) for pattern in case_patterns
            ):
                continue
            if args.limit is not None and materialized >= args.limit:
                return finish(materialized, failed)
            try:
                materialize_case(config, case, output_dir, exporter)
                materialized += 1
                print(
                    f"materialized {benchmark_id}/{case.case_id}",
                    file=sys.stderr,
                )
            except Exception as exc:
                failed += 1
                print(
                    f"failed {benchmark_id}/{case.case_id}: {exc}",
                    file=sys.stderr,
                )
    return finish(materialized, failed)


def finish(materialized: int, failed: int) -> int:
    print(f"summary: materialized={materialized} failed={failed}", file=sys.stderr)
    return 1 if failed else 0


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
    config: dict[str, Any], case: Any, output_dir: Path, exporter: Any
) -> None:
    benchmark = case.benchmark
    flat_case_id = f"{benchmark['id']}__{case.case_id}"
    case_dir = output_dir / flat_case_id
    case_dir.mkdir(parents=True, exist_ok=True)

    read_dialect = case.read_dialect or benchmark.get("readDialect") or "postgres"
    write_dialect = case.write_dialect or benchmark.get("writeDialect") or "postgres"
    adapter = benchmark.get("adapter", config["defaults"].get("adapter", "none"))
    solver_config = solver_materialization_config(benchmark, "sqlsolver")
    before_sql, after_sql, date_day_bridge = exporter.patch_tsql_date_day_pair(case)
    before_sql, before_coercions = materialize_calcite_coercions(
        repository_root=ROOT,
        authority_root=CALCITE_IR_ROOT,
        benchmark_id=benchmark["id"],
        case_id=case.case_id,
        source_metadata=case.source_metadata,
        schema_sql=case.schema_sql,
        side="before",
        sql=before_sql,
    )
    after_sql, after_coercions = materialize_calcite_coercions(
        repository_root=ROOT,
        authority_root=CALCITE_IR_ROOT,
        benchmark_id=benchmark["id"],
        case_id=case.case_id,
        source_metadata=case.source_metadata,
        schema_sql=case.schema_sql,
        side="after",
        sql=after_sql,
    )

    with tempfile.TemporaryDirectory(prefix="logos-sqlsolver-nonwetune-") as tmp:
        tmp_dir = Path(tmp)
        schema_source = write_text(tmp_dir / "schema.source.sql", case.schema_sql)
        sql1_source = write_text(
            tmp_dir / "sql1.source.sql", ensure_sql_terminated(before_sql)
        )
        sql2_source = write_text(
            tmp_dir / "sql2.source.sql", ensure_sql_terminated(after_sql)
        )

        schema_target = tmp_dir / "schema.sql"
        schema_report = tmp_dir / "schema.normalization.json"
        normalize_sql(
            source=schema_source,
            target=schema_target,
            report=schema_report,
            read=read_dialect,
            write="mysql",
            identify=False,
        )
        materialized_schema, constraint_materialization = materialize_pair_constraints(
            schema_target.read_text(),
            case.constraints,
        )

        query_reports: dict[str, dict[str, Any]] = {}
        if adapter == "sqlglot":
            sql1_target = tmp_dir / "sql1.sql"
            sql2_target = tmp_dir / "sql2.sql"
            before_report = tmp_dir / "sql1.normalization.json"
            after_report = tmp_dir / "sql2.normalization.json"
            normalize_sql(
                source=sql1_source,
                target=sql1_target,
                report=before_report,
                read=read_dialect,
                write=write_dialect,
                identify=False,
            )
            normalize_sql(
                source=sql2_source,
                target=sql2_target,
                report=after_report,
                read=read_dialect,
                write=write_dialect,
                identify=False,
            )
            query_reports["before"] = json.loads(before_report.read_text())
            query_reports["after"] = json.loads(after_report.read_text())
        else:
            sql1_target = sql1_source
            sql2_target = sql2_source
            query_reports["before"] = {"skipped": True}
            query_reports["after"] = {"skipped": True}

        solver_preflight = None
        solver_frontend_status = None
        if solver_config is not None:
            query_policy = solver_config.get("queryPolicy")
            preflight_policy = solver_config.get("preflight")
            if query_policy != SQLSOLVER_POSTGRES_IDENTIFIER_POLICY:
                raise ValueError(
                    f"{flat_case_id} has unknown SQLSolver query policy "
                    f"{query_policy!r}"
                )
            if preflight_policy != SQLSOLVER_PREFLIGHT_POLICY:
                raise ValueError(
                    f"{flat_case_id} has unknown SQLSolver preflight policy "
                    f"{preflight_policy!r}"
                )
            sql1_materialized, before_solver_report = materialize_sqlsolver_query(
                sql1_target.read_text(),
                read_dialect=read_dialect,
                policy=query_policy,
            )
            sql2_materialized, after_solver_report = materialize_sqlsolver_query(
                sql2_target.read_text(),
                read_dialect=read_dialect,
                policy=query_policy,
            )
            query_reports["before"] = {
                "ingestionNormalization": query_reports["before"],
                "solverBoundary": before_solver_report,
            }
            query_reports["after"] = {
                "ingestionNormalization": query_reports["after"],
                "solverBoundary": after_solver_report,
            }
            preflight_schema = write_text(
                tmp_dir / "schema.preflight.sql", materialized_schema
            )
            preflight_sql1 = write_text(
                tmp_dir / "sql1.preflight.sql", sql1_materialized
            )
            preflight_sql2 = write_text(
                tmp_dir / "sql2.preflight.sql", sql2_materialized
            )
            target_preflight = run_sqlsolver_preflight(
                schema=preflight_schema,
                sql1=preflight_sql1,
                sql2=preflight_sql2,
            )
            preservation_established = pair_preservation_established(
                before_solver_report, after_solver_report
            )
            target_status = target_preflight.get("status")
            admitted = preservation_established and target_status == "planned"
            solver_frontend_status = (
                "ready"
                if admitted
                else ("Timeout" if target_status == "timeout" else "Unsupport")
            )
            solver_preflight = {
                "policy": preflight_policy,
                "status": solver_frontend_status,
                "semanticPreservationEstablished": preservation_established,
                "proverSubmissionAllowed": admitted,
                "unsupportedStage": (
                    None
                    if admitted
                    else (
                        "materialization-preservation"
                        if not preservation_established
                        else (
                            "target-frontend-timeout"
                            if target_status == "timeout"
                            else "target-frontend"
                        )
                    )
                ),
                "targetFrontend": target_preflight,
            }
        else:
            sql1_materialized = ensure_one_line(sql1_target.read_text())
            sql2_materialized = ensure_one_line(sql2_target.read_text())

        write_text(case_dir / "schema.sql", materialized_schema)
        write_text(case_dir / "sql1.sql", sql1_materialized)
        write_text(case_dir / "sql2.sql", sql2_materialized)
        write_text(
            case_dir / "metadata.json",
            json.dumps(
                {
                    **build_materialized_metadata(
                        config,
                        case,
                        flat_case_id,
                        constraint_materialization,
                    ),
                    **(
                        {"pairedTsqlDateDayBridge": date_day_bridge}
                        if date_day_bridge is not None
                        else {}
                    ),
                    **(
                        {
                            "calciteCoercionMaterialization": {
                                "before": before_coercions,
                                "after": after_coercions,
                            }
                        }
                        if before_coercions is not None or after_coercions is not None
                        else {}
                    ),
                    **(
                        {
                            "solverFrontendStatus": solver_frontend_status,
                            "solverFrontendPreflight": solver_preflight,
                        }
                        if solver_config is not None
                        else {}
                    ),
                    "normalizationForSolverRun": {
                        "schema": {
                            "readDialect": read_dialect,
                            "writeDialect": "mysql",
                            "report": json.loads(schema_report.read_text()),
                            "semanticNote": (
                                "DDL-only dialect materialization for SQLSolver's "
                                "MySQL schema parser. SQLGlot maps unbounded VARCHAR "
                                "to TEXT without adding a 255-character bound."
                            ),
                        },
                        "before": query_reports["before"],
                        "after": query_reports["after"],
                    },
                },
                indent=2,
                sort_keys=True,
            )
            + "\n",
        )


def normalize_sql(
    source: Path,
    target: Path,
    report: Path,
    read: str,
    write: str,
    identify: bool,
) -> None:
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
    ]
    if identify:
        command.append("--identify")
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


def run_sqlsolver_preflight(*, schema: Path, sql1: Path, sql2: Path) -> dict[str, Any]:
    command = [
        str(ROOT / "benchmarks/scripts/sqlsolver-preflight"),
        "--schema",
        str(schema),
        "--sql1",
        str(sql1),
        "--sql2",
        str(sql2),
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
        raise RuntimeError(
            "SQLSolver frontend preflight failed as infrastructure: "
            + completed.stderr.strip()
        )
    try:
        report = json.loads(completed.stdout)
    except json.JSONDecodeError as exc:
        raise RuntimeError("SQLSolver frontend preflight emitted invalid JSON") from exc
    if (
        not isinstance(report, dict)
        or report.get("actualTargetFrontend") is not True
        or report.get("proofSearchInvoked") is not False
        or report.get("status") not in {"planned", "unsupported", "timeout"}
    ):
        raise RuntimeError("SQLSolver frontend preflight report is malformed")
    return report


def build_metadata(
    config: dict[str, Any], case: Any, flat_case_id: str
) -> dict[str, Any]:
    defaults = config["defaults"]
    benchmark = case.benchmark
    raw_constraints = case.constraints
    if raw_constraints is None:
        constraints: list[dict[str, Any]] = []
    elif isinstance(raw_constraints, list):
        constraints = raw_constraints
    else:
        raise ValueError(
            f"{flat_case_id} constraints must be a list or null, "
            f"got {type(raw_constraints).__name__}"
        )
    constraint_scope = benchmark.get("constraintScope", "none")
    contract_sources: list[dict[str, str]] = [
        {"kind": "parser_facing_ddl", "path": "schema.sql"}
    ]
    if constraint_scope == "pair":
        contract_sources.append(
            {"kind": "pair_metadata", "path": "metadata.json#/constraints"}
        )
    return {
        "sourceBenchmark": benchmark["id"],
        "sourceCase": case.case_id,
        "flatCaseId": flat_case_id,
        "source": case.source_metadata,
        "schemaScope": benchmark["schemaScope"],
        "constraintScope": constraint_scope,
        "constraints": constraints,
        "integrityContract": {
            "authoritativeForLogos": True,
            "sources": contract_sources,
            "silentDrops": 0,
            "sqlsolverDdlComplete": not constraints,
            "sqlsolverDdlLimitation": (
                "SQLSolver reads schema.sql only; pair-level declarations are "
                "retained in adjacent metadata for the authoritative Logos contract."
                if constraints
                else None
            ),
        },
        "adapter": benchmark.get("adapter", defaults.get("adapter", "none")),
        "sourceDialect": case.source_dialect or benchmark.get("sourceDialect"),
        "readDialect": case.read_dialect or benchmark.get("readDialect"),
        "writeDialect": case.write_dialect
        or benchmark.get("writeDialect", defaults.get("writeDialect")),
        "frontendTargetDialectPurpose": benchmark.get(
            "frontendTargetDialectPurpose",
            defaults.get("frontendTargetDialectPurpose"),
        ),
        "semanticProfile": benchmark.get(
            "semanticProfile", defaults["semanticProfile"]
        ),
        "bagSemantics": benchmark.get("bagSemantics", defaults["bagSemantics"]),
        "nullSemantics": benchmark.get("nullSemantics", defaults["nullSemantics"]),
        "featureTags": case.feature_tags,
        "profile": "sqlsolver",
    }


def build_materialized_metadata(
    config: dict[str, Any],
    case: Any,
    flat_case_id: str,
    constraint_materialization: dict[str, Any],
) -> dict[str, Any]:
    metadata = build_metadata(config, case, flat_case_id)
    contract = metadata["integrityContract"]
    contract["sqlsolverDdlComplete"] = constraint_materialization["ddlComplete"]
    contract["sqlsolverDdlLimitation"] = None
    metadata["constraintMaterialization"] = constraint_materialization
    return metadata


def ensure_sql_terminated(sql: str) -> str:
    stripped = sql.strip()
    if not stripped:
        return "\n"
    return stripped if stripped.endswith(";") else stripped + ";\n"


def ensure_one_line(sql: str) -> str:
    return normalize_sql_layout(sql, strip_trailing_semicolon=True) + "\n"


def write_text(path: Path, content: str) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content)
    return path


if __name__ == "__main__":
    raise SystemExit(main())
