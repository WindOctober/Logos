#!/usr/bin/env python3
"""Batch-generate Logos solver LLM assessment cache files for benchmark cases."""

from __future__ import annotations

import argparse
import importlib.util
import json
import re
import subprocess
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from importlib.machinery import SourceFileLoader
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
EXPORTER_PATH = ROOT / "scripts/export-benchmark-ir"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--config", type=Path, default=Path("benchmarks/core/ingestion.json"))
    parser.add_argument(
        "--prepared-root",
        type=Path,
        default=Path("var/logos-solver-cex/llm-assessment-batch/inputs"),
    )
    parser.add_argument("--benchmark", action="append")
    parser.add_argument("--case", action="append", help="Case id regex. May be repeated.")
    parser.add_argument("--log-root", type=Path, default=Path("var/logos-solver-cex/llm-assessment-batch/logs"))
    parser.add_argument("--cache-dir", type=Path, default=Path("var/logos-solver-cex/llm-assessments"))
    parser.add_argument("--jobs", type=int, default=16)
    parser.add_argument("--limit", type=int)
    parser.add_argument("--force", action="store_true")
    parser.add_argument("--solver-bin", type=Path, default=Path("target/debug/logos-solver"))
    parser.add_argument("--summary", type=Path, default=Path("var/logos-solver-cex/llm-assessment-batch/summary.json"))
    args = parser.parse_args()

    args.log_root.mkdir(parents=True, exist_ok=True)
    args.cache_dir.mkdir(parents=True, exist_ok=True)
    args.summary.parent.mkdir(parents=True, exist_ok=True)
    args.prepared_root.mkdir(parents=True, exist_ok=True)
    cases = discover_canonical_cases(args)
    if args.limit is not None:
        cases = cases[: args.limit]

    run_solver_assessment_batch(args, cases)


@dataclass(frozen=True)
class SolverCase:
    case_id: str
    benchmark_id: str | None
    source_case_id: str | None
    case_dir: Path
    schema: Path
    source: Path
    target: Path
    calcite_ir_command: str


def discover_canonical_cases(args: argparse.Namespace) -> list[SolverCase]:
    exporter = load_exporter()
    config_path = resolve_path(args.config)
    config = json.loads(config_path.read_text())
    selected = set(args.benchmark or [])
    case_patterns = [re.compile(pattern) for pattern in args.case or []]

    cases: list[SolverCase] = []
    for benchmark in config["benchmarks"]:
        benchmark_id = benchmark["id"]
        if selected and benchmark_id not in selected:
            continue
        for case in exporter.iter_cases(config, benchmark):
            if case_patterns and not any(pattern.search(case.case_id) for pattern in case_patterns):
                continue
            case_dir = args.prepared_root / benchmark_id / case.case_id
            case_dir.mkdir(parents=True, exist_ok=True)
            schema = write_text(case_dir / "schema.sql", case.schema_sql)
            source = write_text(case_dir / "source.sql", ensure_sql_terminated(case.before_sql))
            target = write_text(case_dir / "target.sql", ensure_sql_terminated(case.after_sql))
            metadata = build_assessment_batch_metadata(config, case, benchmark_id)
            write_text(case_dir / "metadata.json", json.dumps(metadata, indent=2, sort_keys=True) + "\n")
            cases.append(
                SolverCase(
                    case_id=f"{benchmark_id}__{case.case_id}",
                    benchmark_id=benchmark_id,
                    source_case_id=case.case_id,
                    case_dir=case_dir,
                    schema=schema,
                    source=source,
                    target=target,
                    calcite_ir_command=frontend_command(config, case),
                )
            )
    return cases


def frontend_command(config: dict[str, Any], case: Any) -> str:
    adapter = case.benchmark.get("adapter", config["defaults"].get("adapter", "none"))
    if adapter == "none":
        return "scripts/calcite-ir"
    if adapter == "sqlglot":
        read = case.read_dialect or case.benchmark["readDialect"]
        write = case.write_dialect or case.benchmark["writeDialect"]
        return f"scripts/calcite-ir-sqlglot --read {shell_word(read)} --write {shell_word(write)}"
    raise ValueError(f"unsupported adapter: {adapter}")


def build_assessment_batch_metadata(config: dict[str, Any], case: Any, benchmark_id: str) -> dict[str, Any]:
    defaults = config["defaults"]
    benchmark = case.benchmark
    return {
        "sourceBenchmark": benchmark_id,
        "sourceCase": case.case_id,
        "source": case.source_metadata,
        "schemaScope": benchmark["schemaScope"],
        "constraintScope": benchmark.get("constraintScope", "none"),
        "constraints": case.constraints,
        "adapter": benchmark.get("adapter", defaults.get("adapter", "none")),
        "sourceDialect": case.source_dialect or benchmark.get("sourceDialect"),
        "readDialect": case.read_dialect or benchmark.get("readDialect"),
        "writeDialect": case.write_dialect or benchmark.get("writeDialect", defaults.get("writeDialect")),
        "frontendCommand": frontend_command(config, case),
        "profile": "logos-solver-assessment-batch",
    }


def run_solver_assessment_batch(args: argparse.Namespace, cases: list[SolverCase]) -> None:
    started = time.monotonic()
    reports = []
    jobs = max(args.jobs, 1)
    with ThreadPoolExecutor(max_workers=jobs) as executor:
        futures = [executor.submit(run_solver_assessment_case, args, case) for case in cases]
        for future in as_completed(futures):
            reports.append(future.result())
    reports.sort(key=lambda report: report["caseId"])

    summary = {
        "preparedRoot": str(args.prepared_root),
        "logRoot": str(args.log_root),
        "cacheDir": str(args.cache_dir),
        "jobs": jobs,
        "force": args.force,
        "total": len(reports),
        "ok": sum(1 for report in reports if report["status"] == "ok"),
        "failed": sum(1 for report in reports if report["status"] == "failed"),
        "elapsedMs": int((time.monotonic() - started) * 1000),
        "cases": reports,
    }
    write_text(args.summary, json.dumps(summary, indent=2, sort_keys=True) + "\n")
    if summary["failed"]:
        raise SystemExit(1)


def run_solver_assessment_case(args: argparse.Namespace, case: SolverCase) -> dict[str, Any]:
    started = time.monotonic()
    log_dir = args.log_root / case.case_id
    cmd = solver_command_prefix(args) + [
        "check",
        "--schema",
        str(case.schema),
        "--source",
        str(case.source),
        "--target",
        str(case.target),
        "--calcite-ir-command",
        case.calcite_ir_command,
        "--llm-assessment-only",
        "--disable-proof-agent",
        "--output",
        "json",
        "--llm-assessment-cache-dir",
        str(args.cache_dir),
        "--log-dir",
        str(log_dir),
    ]
    if not args.force:
        cmd.append("--reuse-llm-assessment")
    if args.force:
        cmd.append("--force-llm-assessment")

    completed = subprocess.run(cmd, text=True, capture_output=True)
    report = None
    error = None
    if completed.stdout.strip():
        try:
            report = json.loads(completed.stdout)
        except json.JSONDecodeError as exc:
            error = f"failed to parse solver JSON output: {exc}"
    if completed.returncode != 0 and error is None:
        error = completed.stderr.strip() or f"solver exited with code {completed.returncode}"

    return {
        "caseId": case.case_id,
        "benchmarkId": case.benchmark_id,
        "sourceCaseId": case.source_case_id,
        "caseDir": str(case.case_dir),
        "logDir": str(log_dir),
        "calciteIrCommand": case.calcite_ir_command,
        "status": "ok" if completed.returncode == 0 and error is None else "failed",
        "elapsedMs": int((time.monotonic() - started) * 1000),
        "error": error,
        "stderr": completed.stderr,
        "report": report,
    }


def solver_command_prefix(args: argparse.Namespace) -> list[str]:
    if args.solver_bin.exists():
        return [str(args.solver_bin)]
    return ["cargo", "run", "-q", "-p", "logos-solver", "--"]


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


def ensure_sql_terminated(sql: str) -> str:
    stripped = sql.strip()
    if not stripped:
        return "\n"
    return stripped if stripped.endswith(";") else stripped + ";\n"


def write_text(path: Path, content: str) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content)
    return path


def shell_word(value: str) -> str:
    return "'" + value.replace("'", "'\\''") + "'"


if __name__ == "__main__":
    main()
