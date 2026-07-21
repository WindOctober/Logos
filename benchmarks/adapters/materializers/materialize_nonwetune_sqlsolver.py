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

from materializer_sql import normalize_sql_layout


ROOT = Path(__file__).resolve().parents[3]
EXPORTER_PATH = ROOT / "scripts/export-benchmark-ir"
DEFAULT_CONFIG = "benchmarks/core/ingestion.json"
DEFAULT_OUTPUT = "benchmarks/core/.generated/sqlsolver/nonwetune-flat"
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
    parser.add_argument("--case", action="append", help="Case id regex. May be repeated.")
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
            if case_patterns and not any(pattern.search(case.case_id) for pattern in case_patterns):
                continue
            if args.limit is not None and materialized >= args.limit:
                return finish(materialized, failed)
            try:
                materialize_case(config, case, output_dir)
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


def materialize_case(config: dict[str, Any], case: Any, output_dir: Path) -> None:
    benchmark = case.benchmark
    flat_case_id = f"{benchmark['id']}__{case.case_id}"
    case_dir = output_dir / flat_case_id
    case_dir.mkdir(parents=True, exist_ok=True)

    read_dialect = case.read_dialect or benchmark.get("readDialect") or "postgres"
    write_dialect = case.write_dialect or benchmark.get("writeDialect") or "postgres"
    adapter = benchmark.get("adapter", config["defaults"].get("adapter", "none"))

    with tempfile.TemporaryDirectory(prefix="logos-sqlsolver-nonwetune-") as tmp:
        tmp_dir = Path(tmp)
        schema_source = write_text(tmp_dir / "schema.source.sql", case.schema_sql)
        sql1_source = write_text(tmp_dir / "sql1.source.sql", ensure_sql_terminated(case.before_sql))
        sql2_source = write_text(tmp_dir / "sql2.source.sql", ensure_sql_terminated(case.after_sql))

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

        write_text(case_dir / "schema.sql", schema_target.read_text())
        write_text(case_dir / "sql1.sql", ensure_one_line(sql1_target.read_text()))
        write_text(case_dir / "sql2.sql", ensure_one_line(sql2_target.read_text()))
        write_text(
            case_dir / "metadata.json",
            json.dumps(
                {
                    **build_metadata(config, case, flat_case_id),
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


def build_metadata(config: dict[str, Any], case: Any, flat_case_id: str) -> dict[str, Any]:
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
        "semanticProfile": benchmark.get("semanticProfile", defaults["semanticProfile"]),
        "bagSemantics": benchmark.get("bagSemantics", defaults["bagSemantics"]),
        "nullSemantics": benchmark.get("nullSemantics", defaults["nullSemantics"]),
        "featureTags": case.feature_tags,
        "profile": "sqlsolver",
    }


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
