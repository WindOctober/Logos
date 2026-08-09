import copy
import hashlib
import json
import runpy
import tempfile
import textwrap
import unittest
from pathlib import Path
from unittest import mock


RUNNER = Path(__file__).with_name("run-logos-transform")


class TransformRunnerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.runner = runpy.run_path(str(RUNNER), run_name="transform_runner_test")

    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.input_root = self.root / "generated"
        self.fake_solver = self.root / "fake-logos-solver"
        self.fake_solver.write_text(
            textwrap.dedent(
                """\
                #!/usr/bin/python3
                import hashlib
                import json
                import pathlib
                import sys
                import time

                def option(name):
                    index = sys.argv.index(name)
                    return pathlib.Path(sys.argv[index + 1])

                def write_json(path, value):
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_text(
                        json.dumps(value, indent=2, ensure_ascii=False) + "\\n",
                        encoding="utf-8",
                    )

                def digest(path):
                    return hashlib.sha256(path.read_bytes()).hexdigest()

                def compact_digest(value):
                    payload = json.dumps(
                        value, ensure_ascii=False, separators=(",", ":")
                    ).encode("utf-8")
                    return hashlib.sha256(payload).hexdigest()

                def one_statement(sql):
                    statement = sql.strip()
                    if statement.endswith(";"):
                        statement = statement[:-1].rstrip()
                    return statement

                schema = option("--schema")
                source = option("--source")
                target = option("--target")
                case_dir = option("--log-dir")
                metadata = source.parent / "metadata.json"
                metadata_document = json.loads(metadata.read_text(encoding="utf-8"))
                flat_case_id = metadata_document["flatCaseId"]
                schema_text = schema.read_bytes().decode("utf-8")
                source_text = source.read_bytes().decode("utf-8")
                target_text = target.read_bytes().decode("utf-8")
                if "FAIL" in source_text:
                    print("fixture frontend contract rejected", file=sys.stderr)
                    raise SystemExit(3)
                if "SLOW" in source_text:
                    time.sleep(2)

                environment = {
                    "defaultCollation": "C",
                    "characterClassification": "C",
                    "localeProvider": "libc",
                    "serverEncoding": "UTF8",
                }
                integrity = {
                    "caseId": flat_case_id,
                    "source": str(metadata.resolve()),
                    "tables": [],
                }
                verification = {
                    "sqlEnvironment": environment,
                    "integrityContract": integrity,
                    "schema": {"path": str(schema.resolve()), "sql": schema_text},
                    "sourceQuery": {"path": str(source.resolve()), "sql": source_text},
                    "targetQuery": {"path": str(target.resolve()), "sql": target_text},
                }
                schema_ir = {
                    "tables": [{
                        "name": "t",
                        "columns": [{"name": "a", "ty": "integer", "nullable": True}],
                        "constraints": {},
                    }]
                }
                source_ir = [{
                    "sourceSql": one_statement(source_text),
                    "rel": {"kind": "fixture", "case": flat_case_id},
                    "analysisErrors": [],
                }]
                target_ir = [{
                    "sourceSql": one_statement(target_text),
                    "rel": {"kind": "fixture", "case": flat_case_id},
                    "analysisErrors": [],
                }]
                input_dir = case_dir / "input"
                write_json(input_dir / "verification-input.json", verification)
                write_json(input_dir / "integrity-contract.json", integrity)
                (input_dir / "integrity-contract.txt").write_text(
                    flat_case_id + "\\n", encoding="utf-8"
                )
                (input_dir / "integrity-schema-probe.sql").write_text(
                    "SELECT 1;\\n", encoding="utf-8"
                )
                write_json(input_dir / "integrity-validator-checks.json", [])
                write_json(input_dir / "sql-environment.json", environment)
                write_json(input_dir / "schema-ir.json", schema_ir)
                write_json(input_dir / "source-ir.json", source_ir)
                write_json(input_dir / "target-ir.json", target_ir)

                workspace = case_dir / "proof-stage/formal-sql"
                module_dir = workspace
                module_dir.mkdir(parents=True)
                fields = {
                    "problemPath": "Problem.v",
                    "goalPath": "Goal.v",
                    "witnessPath": "Witness.v",
                    "proofAgentPromptPath": "proof-agent-prompt.md",
                    "rocqCheckScriptPath": "check-proof.sh",
                    "dockerAgentScriptPath": "run-agent.sh",
                }
                proof_workspace = {"generatedModuleDir": str(module_dir)}
                module_text = {
                    "Schema.v": "schema:" + flat_case_id + "\\n",
                    "Queries.v": "queries:" + flat_case_id + "\\n",
                    "Problem.v": "problem:" + flat_case_id + "\\n",
                    "Goal.v": "goal:" + flat_case_id + "\\n",
                    "Witness.v": "witness:" + flat_case_id + "\\n",
                    "proof-agent-prompt.md": "prompt:" + flat_case_id + "\\n",
                    "check-proof.sh": "check:" + flat_case_id + "\\n",
                    "run-agent.sh": "agent:" + flat_case_id + "\\n",
                }
                for field, name in fields.items():
                    path = workspace / name
                    path.write_text(module_text[name], encoding="utf-8")
                    proof_workspace[field] = str(path)
                for name in ("Schema.v", "Queries.v"):
                    (workspace / name).write_text(module_text[name], encoding="utf-8")
                (workspace / "source.sql").write_text(source_text, encoding="utf-8")
                (workspace / "target.sql").write_text(target_text, encoding="utf-8")

                lowering = {
                    "backend": "formal_sql_rocq",
                    "sqlEnvironment": environment,
                    "inputBindings": {
                        "schemaVersion": 1,
                        "caseId": flat_case_id,
                        "schemaSqlSha256": digest(schema),
                        "sourceSqlSha256": digest(source),
                        "targetSqlSha256": digest(target),
                        "verificationInputSha256": digest(input_dir / "verification-input.json"),
                        "integrityContractSha256": digest(input_dir / "integrity-contract.json"),
                        "schemaIrSha256": digest(input_dir / "schema-ir.json"),
                        "sourceIrSha256": digest(input_dir / "source-ir.json"),
                        "targetIrSha256": digest(input_dir / "target-ir.json"),
                    },
                    "schema": {
                        "status": "lowered",
                        "schema": {"rocqModule": module_text["Schema.v"]},
                        "diagnostics": [],
                    },
                    "source": {
                        "status": "lowered",
                        "statements": [{"status": "lowered", "diagnostics": []}],
                        "diagnostics": [],
                    },
                    "target": {
                        "status": "lowered",
                        "statements": [{"status": "lowered", "diagnostics": []}],
                        "diagnostics": [],
                    },
                    "queryModule": {"rocqModule": module_text["Queries.v"]},
                    "proofModule": {"rocqModule": module_text["Problem.v"]},
                    "goalModule": {"rocqModule": module_text["Goal.v"]},
                }
                lowering_path = case_dir / "proof-stage/formal-sql-lowering.json"
                write_json(lowering_path, lowering)
                observation = {
                    "schemaVersion": 1,
                    "verificationInputKey": flat_case_id,
                    "verificationInputSha256": compact_digest(verification),
                    "loweringSha256": compact_digest(lowering),
                    "source": [],
                    "target": [],
                }
                write_json(workspace / "observation-certificates.json", observation)
                query_shape = {
                    "sourceSqlSha256": digest(source),
                    "targetSqlSha256": digest(target),
                    "schemaModuleSha256": digest(workspace / "Schema.v"),
                    "queriesModuleSha256": digest(workspace / "Queries.v"),
                }
                write_json(workspace / "query-shape.json", query_shape)

                def context_binding(name):
                    path = workspace / name
                    return {"path": name, "bytes": path.stat().st_size, "sha256": digest(path)}

                context = {
                    "sourceSql": context_binding("source.sql"),
                    "targetSql": context_binding("target.sql"),
                    "schemaModule": context_binding("Schema.v"),
                    "queriesModule": context_binding("Queries.v"),
                    "observationCertificates": context_binding("observation-certificates.json"),
                }
                write_json(workspace / "context-manifest.json", context)
                report = {
                    "logDir": str(case_dir),
                    "outcome": "transform_only",
                    "proof": {
                        "backendStatus": "workspace_generated",
                        "proofWorkspace": proof_workspace,
                    },
                }
                (case_dir / "report.json").write_text(
                    json.dumps(report) + "\\n", encoding="utf-8"
                )
                if "MUTATE" in source_text:
                    source.write_text(source_text + "-- changed\\n", encoding="utf-8")
                """
            ),
            encoding="utf-8",
        )
        self.fake_solver.chmod(0o755)
        fake_rocq_bin = self.root / "_opam/bin"
        fake_rocq_bin.mkdir(parents=True)
        (self.root / "_opam/lib/coq").mkdir(parents=True)
        self.fake_rocq = fake_rocq_bin / "rocq"
        self.fake_rocq.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
        self.fake_rocq.chmod(0o755)

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def make_case(
        self,
        cohort: str,
        directory: str,
        benchmark: str,
        source_case: str,
        marker: str = "",
    ) -> Path:
        case_dir = self.input_root / cohort / directory
        case_dir.mkdir(parents=True)
        (case_dir / "schema.sql").write_text(
            "CREATE TABLE t (a INTEGER);\n", encoding="utf-8"
        )
        (case_dir / "sql1.sql").write_text(
            f"SELECT a FROM t /* {marker} */;\n", encoding="utf-8"
        )
        (case_dir / "sql2.sql").write_text("SELECT a FROM t;\n", encoding="utf-8")
        (case_dir / "metadata.json").write_text(
            json.dumps(
                {
                    "flatCaseId": f"{benchmark}__{source_case}",
                    "sourceBenchmark": benchmark,
                    "sourceCase": source_case,
                }
            )
            + "\n",
            encoding="utf-8",
        )
        return case_dir

    def config_for(self, run_dir: Path, cases: list, *, timeout_seconds: float = 2):
        run_dir.mkdir()
        input_manifest, input_files = self.runner["input_manifest_record"](
            run_dir, cases, cases
        )
        source_document = {"fixture": "source"}
        source_path = run_dir / "framework-source-tree-manifest.json"
        source_path.write_bytes(self.runner["canonical_json_bytes"](source_document))
        source_digest = hashlib.sha256(source_path.read_bytes()).hexdigest()
        frontend_document = {"fixture": "frontend"}
        frontend_path = run_dir / "frontend-stack-manifest.json"
        frontend_path.write_bytes(
            self.runner["canonical_json_bytes"](frontend_document)
        )
        frontend_digest = hashlib.sha256(frontend_path.read_bytes()).hexdigest()
        config = self.runner["RunConfig"](
            input_root=self.input_root.resolve(),
            run_dir=run_dir.resolve(),
            solver_bin=self.fake_solver.resolve(),
            jobs=2,
            case_timeout_seconds=timeout_seconds,
            termination_grace_seconds=0.05,
            proof_rocq_opam_switch=self.root.resolve(),
            sql_time_zone="UTC",
            sql_default_collation="C",
            sql_character_classification="C",
            sql_locale_provider="libc",
            sql_server_encoding="UTF8",
            input_manifest=input_manifest,
            input_files=input_files,
            solver_binary=self.runner["executable_record"](
                self.fake_solver, "fake solver"
            ),
            framework_source_tree={
                "manifestPath": str(source_path.resolve()),
                "manifestSha256": source_digest,
            },
            frontend_stack={
                "manifestPath": str(frontend_path.resolve()),
                "manifestSha256": frontend_digest,
            },
            runner_binary=self.runner["regular_file_record"](
                RUNNER, "transform runner"
            ),
        )
        dependencies = {
            "build_source_tree_manifest": lambda _root: source_document,
            "source_tree_manifest_sha256": lambda _document: source_digest,
            "build_frontend_stack_manifest": lambda: frontend_document,
            "canonical_frontend_environment": lambda **_kwargs: {
                "PATH": "/usr/bin:/bin",
                "HOME": "/nonexistent",
                "LC_ALL": "C",
            },
        }
        return config, dependencies

    def resolve_recorded(self, value: str) -> Path:
        return self.runner["resolve_recorded_path"](value, "test artifact")

    def test_selectors_are_shared_with_the_canonical_runner(self) -> None:
        self.make_case("rbot-dsb", "one", "rbot-dsb", "one")
        self.make_case("rbot-tpch", "two", "rbot-tpch", "two")
        cases = self.runner["discover_cases"](self.input_root)
        args = self.runner["argument_parser"]().parse_args(
            ["--benchmark", "rbot-tpch", "--match", "two$"]
        )
        selected = self.runner["select_cases"](cases, args)
        self.assertEqual([case.case_id for case in selected], ["rbot-tpch__two"])

    def test_integrity_source_accepts_only_case_manifest_authorities(self) -> None:
        metadata = self.root / "metadata.json"
        sidecar = self.root / "constraints.json"
        unrelated = self.root / "other.json"
        for path in (metadata, sidecar, unrelated):
            path.write_text("{}\n", encoding="utf-8")

        matches = self.runner["integrity_source_matches_case"]
        canonical = {
            "metadata": metadata.resolve(),
            "semanticSidecar": sidecar.resolve(),
        }
        self.assertTrue(matches(canonical, str(metadata.resolve())))
        self.assertTrue(matches(canonical, str(sidecar.resolve())))
        self.assertFalse(matches(canonical, str(unrelated.resolve())))
        self.assertFalse(
            matches({"metadata": metadata.resolve()}, str(sidecar.resolve()))
        )

    def test_atomic_complete_summary_binds_every_input_and_workspace(self) -> None:
        first = self.make_case("rbot-dsb", "one", "rbot-dsb", "one")
        second = self.make_case("rbot-tpch", "two", "rbot-tpch", "two")
        cases = self.runner["discover_cases"](self.input_root)
        run_dir = self.root / "complete-run"
        config, dependencies = self.config_for(run_dir, cases)
        with mock.patch.dict(self.runner["FULL_RUNNER"], dependencies):
            exit_code = self.runner["run_selected_cases"](
                cases, cases, config, {"benchmarks": [], "cases": []}
            )
        self.assertEqual(exit_code, 0)
        summary = json.loads((run_dir / "runner-summary.json").read_text())
        self.assertEqual(summary["status"], "complete")
        self.assertEqual(summary["counts"]["selected"], 2)
        self.assertEqual(summary["counts"]["pending"], 0)
        self.assertEqual(summary["counts"]["completed"], 2)
        self.assertTrue(summary["integrityVerification"]["verified"])
        self.assertEqual(
            summary["integrityVerification"]["transformArtifactEvidenceCaseCount"],
            2,
        )
        self.assertRegex(
            summary["integrityVerification"]["transformArtifactEvidenceSha256"],
            r"^[0-9a-f]{64}$",
        )
        self.assertEqual(
            summary["inputManifest"]["algorithm"], "logos-input-manifest-v2"
        )
        self.assertEqual(summary["inputManifest"]["manifestSchemaVersion"], 2)
        inputs = {first.name: first, second.name: second}
        for result in summary["results"]:
            case_dir = run_dir / "cases" / result["caseId"]
            self.assertEqual(result["status"], "completed")
            self.assertEqual(result["source"]["status"], "lowered")
            self.assertEqual(result["target"]["status"], "lowered")
            self.assertEqual(result["solverCommand"].count("--transform-only"), 1)
            self.assertEqual(
                result["solverCommand"].count("--disable-counterexample-search"),
                1,
            )
            self.assertEqual(result["solverCommand"].count("--disable-proof-agent"), 1)
            self.assertEqual(result["outcome"], "transform_only")
            self.assertEqual(result["backendStatus"], "workspace_generated")
            self.assertEqual(len(result["workspaceEvidence"]), 6)
            self.assertEqual(result["generatedModuleEvidence"]["fileCount"], 13)
            self.assertEqual(
                result["generatedModuleEvidence"]["algorithm"],
                "logos-generated-module-tree-v1",
            )
            transform_evidence = result["transformArtifactEvidence"]
            self.assertEqual(
                transform_evidence["algorithm"],
                "logos-transform-artifact-set-v1",
            )
            self.assertEqual(transform_evidence["artifactCount"], 10)
            self.assertEqual(
                {row["artifact"] for row in transform_evidence["artifacts"]},
                set(self.runner["REQUIRED_TRANSFORM_ARTIFACT_PATHS"]),
            )
            self.assertEqual(
                transform_evidence["artifactsSha256"],
                hashlib.sha256(
                    self.runner["canonical_json_bytes"](transform_evidence["artifacts"])
                ).hexdigest(),
            )
            for row in transform_evidence["artifacts"]:
                artifact_path = self.resolve_recorded(row["path"])
                self.assertEqual(
                    artifact_path,
                    (case_dir / row["artifact"]).resolve(),
                )
                self.assertFalse(artifact_path.is_symlink())
                self.assertTrue(artifact_path.is_file())
                self.assertEqual(row["bytes"], artifact_path.stat().st_size)
                self.assertEqual(
                    row["sha256"],
                    hashlib.sha256(artifact_path.read_bytes()).hexdigest(),
                )
            self.assertEqual(
                self.resolve_recorded(result["reportPath"]),
                (case_dir / "report.json").resolve(),
            )
            durable = json.loads((case_dir / "runner-result.json").read_text())
            status = json.loads((case_dir / "status.json").read_text())
            self.assertEqual(durable, result)
            self.assertEqual(status["status"], "completed")
            input_dir = inputs[Path(result["inputDir"]).name]
            for field, filename in (
                ("schema", "schema.sql"),
                ("source", "sql1.sql"),
                ("target", "sql2.sql"),
                ("metadata", "metadata.json"),
            ):
                self.assertEqual(
                    result["inputFiles"][field]["sha256"],
                    hashlib.sha256((input_dir / filename).read_bytes()).hexdigest(),
                )
        self.assertEqual(list(run_dir.rglob(".*.tmp")), [])

    def test_exact_raw_sql_binding_preserves_crlf_bytes(self) -> None:
        case = self.make_case("rbot-dsb", "crlf", "rbot-dsb", "crlf")
        raw_sql = {
            "schema.sql": b"CREATE TABLE t (a INTEGER);\r\n",
            "sql1.sql": b"SELECT a FROM t /* source */;\r\n",
            "sql2.sql": b"SELECT a FROM t /* target */;\r\n",
        }
        for filename, payload in raw_sql.items():
            (case / filename).write_bytes(payload)
        cases = self.runner["discover_cases"](self.input_root)
        run_dir = self.root / "crlf-run"
        config, dependencies = self.config_for(run_dir, cases)
        with mock.patch.dict(self.runner["FULL_RUNNER"], dependencies):
            self.assertEqual(
                self.runner["run_selected_cases"](
                    cases, cases, config, {"benchmarks": ["rbot-dsb"]}
                ),
                0,
            )
        summary = json.loads((run_dir / "runner-summary.json").read_text())
        self.assertEqual(summary["counts"]["completed"], 1)
        case_dir = run_dir / "cases" / summary["results"][0]["caseId"]
        verification = json.loads(
            (case_dir / "input/verification-input.json").read_text()
        )
        self.assertEqual(
            verification["schema"]["sql"].encode("utf-8"), raw_sql["schema.sql"]
        )
        self.assertEqual(
            verification["sourceQuery"]["sql"].encode("utf-8"),
            raw_sql["sql1.sql"],
        )
        self.assertEqual(
            verification["targetQuery"]["sql"].encode("utf-8"),
            raw_sql["sql2.sql"],
        )

    def test_terminal_integrity_rejects_deleted_transform_artifact(self) -> None:
        self.make_case("rbot-dsb", "delete", "rbot-dsb", "delete")
        cases = self.runner["discover_cases"](self.input_root)
        run_dir = self.root / "deleted-artifact-run"
        config, dependencies = self.config_for(run_dir, cases)
        with mock.patch.dict(self.runner["FULL_RUNNER"], dependencies):
            self.assertEqual(
                self.runner["run_selected_cases"](
                    cases, cases, config, {"benchmarks": ["rbot-dsb"]}
                ),
                0,
            )
        summary = json.loads((run_dir / "runner-summary.json").read_text())
        result = summary["results"][0]
        case_dir = run_dir / "cases" / result["caseId"]
        (case_dir / "input/integrity-schema-probe.sql").unlink()
        with mock.patch.dict(self.runner["FULL_RUNNER"], dependencies):
            with self.assertRaisesRegex(
                self.runner["RunnerError"], "transform artifact changed"
            ):
                self.runner["verify_run_integrity"](
                    cases, cases, config, summary["results"]
                )

    def test_terminal_integrity_rejects_mutated_transform_artifact(self) -> None:
        self.make_case("rbot-dsb", "mutated", "rbot-dsb", "mutated")
        cases = self.runner["discover_cases"](self.input_root)
        run_dir = self.root / "mutated-artifact-run"
        config, dependencies = self.config_for(run_dir, cases)
        with mock.patch.dict(self.runner["FULL_RUNNER"], dependencies):
            self.assertEqual(
                self.runner["run_selected_cases"](
                    cases, cases, config, {"benchmarks": ["rbot-dsb"]}
                ),
                0,
            )
        summary = json.loads((run_dir / "runner-summary.json").read_text())
        result = summary["results"][0]
        case_dir = run_dir / "cases" / result["caseId"]
        source_ir = case_dir / "input/source-ir.json"
        source_ir.write_bytes(source_ir.read_bytes() + b"mutated\n")
        with mock.patch.dict(self.runner["FULL_RUNNER"], dependencies):
            with self.assertRaisesRegex(
                self.runner["RunnerError"], "transform artifact changed"
            ):
                self.runner["verify_run_integrity"](
                    cases, cases, config, summary["results"]
                )

    def test_terminal_integrity_rejects_borrowed_cross_case_artifact(self) -> None:
        self.make_case("rbot-dsb", "first", "rbot-dsb", "first")
        self.make_case("rbot-tpch", "second", "rbot-tpch", "second")
        cases = self.runner["discover_cases"](self.input_root)
        run_dir = self.root / "borrowed-artifact-run"
        config, dependencies = self.config_for(run_dir, cases)
        with mock.patch.dict(self.runner["FULL_RUNNER"], dependencies):
            self.assertEqual(
                self.runner["run_selected_cases"](
                    cases, cases, config, {"benchmarks": []}
                ),
                0,
            )
        summary = json.loads((run_dir / "runner-summary.json").read_text())
        results = copy.deepcopy(summary["results"])
        first, second = results
        first_rows = first["transformArtifactEvidence"]["artifacts"]
        second_rows = second["transformArtifactEvidence"]["artifacts"]
        first_index = next(
            index
            for index, row in enumerate(first_rows)
            if row["artifact"] == "input/source-ir.json"
        )
        borrowed = next(
            copy.deepcopy(row)
            for row in second_rows
            if row["artifact"] == "input/source-ir.json"
        )
        first_rows[first_index] = borrowed
        first["transformArtifactEvidence"]["artifactsSha256"] = hashlib.sha256(
            self.runner["canonical_json_bytes"](first_rows)
        ).hexdigest()
        first_case_dir = run_dir / "cases" / first["caseId"]
        self.runner["atomic_write_json"](first_case_dir / "runner-result.json", first)
        with mock.patch.dict(self.runner["FULL_RUNNER"], dependencies):
            with self.assertRaisesRegex(
                self.runner["RunnerError"], "borrows another case"
            ):
                self.runner["verify_run_integrity"](cases, cases, config, results)

    def test_terminal_integrity_rejects_local_cross_case_source_ir_copy(self) -> None:
        self.make_case("rbot-dsb", "first", "rbot-dsb", "first", "FIRST")
        self.make_case("rbot-tpch", "second", "rbot-tpch", "second", "SECOND")
        cases = self.runner["discover_cases"](self.input_root)
        run_dir = self.root / "local-source-ir-copy-run"
        config, dependencies = self.config_for(run_dir, cases)
        with mock.patch.dict(self.runner["FULL_RUNNER"], dependencies):
            self.assertEqual(
                self.runner["run_selected_cases"](
                    cases, cases, config, {"benchmarks": []}
                ),
                0,
            )
        summary = json.loads((run_dir / "runner-summary.json").read_text())
        results = copy.deepcopy(summary["results"])
        first, second = results
        first_case_dir = run_dir / "cases" / first["caseId"]
        second_case_dir = run_dir / "cases" / second["caseId"]
        (first_case_dir / "input/source-ir.json").write_bytes(
            (second_case_dir / "input/source-ir.json").read_bytes()
        )
        first["transformArtifactEvidence"] = self.runner[
            "transform_artifact_set_record"
        ](first_case_dir)
        self.runner["atomic_write_json"](first_case_dir / "runner-result.json", first)
        with mock.patch.dict(self.runner["FULL_RUNNER"], dependencies):
            with self.assertRaisesRegex(
                self.runner["RunnerError"],
                "accepted source IR does not match the selected SQL splitter contract",
            ):
                self.runner["verify_run_integrity"](cases, cases, config, results)

    def test_terminal_integrity_rejects_local_cross_case_lowering_copy(self) -> None:
        self.make_case("rbot-dsb", "first", "rbot-dsb", "first", "FIRST")
        self.make_case("rbot-tpch", "second", "rbot-tpch", "second", "SECOND")
        cases = self.runner["discover_cases"](self.input_root)
        run_dir = self.root / "local-lowering-copy-run"
        config, dependencies = self.config_for(run_dir, cases)
        with mock.patch.dict(self.runner["FULL_RUNNER"], dependencies):
            self.assertEqual(
                self.runner["run_selected_cases"](
                    cases, cases, config, {"benchmarks": []}
                ),
                0,
            )
        summary = json.loads((run_dir / "runner-summary.json").read_text())
        results = copy.deepcopy(summary["results"])
        first, second = results
        first_case_dir = run_dir / "cases" / first["caseId"]
        second_case_dir = run_dir / "cases" / second["caseId"]
        lowering = Path("proof-stage/formal-sql-lowering.json")
        (first_case_dir / lowering).write_bytes((second_case_dir / lowering).read_bytes())
        first["transformArtifactEvidence"] = self.runner[
            "transform_artifact_set_record"
        ](first_case_dir)
        self.runner["atomic_write_json"](first_case_dir / "runner-result.json", first)
        with mock.patch.dict(self.runner["FULL_RUNNER"], dependencies):
            with self.assertRaisesRegex(
                self.runner["RunnerError"],
                "FormalSQL lowering input bindings are stale or cross-case",
            ):
                self.runner["verify_run_integrity"](cases, cases, config, results)

    def test_calcite_splitter_contract_protects_tokens_and_ignores_comments(
        self,
    ) -> None:
        sql = (
            "\n-- comment-only prefix;\n"
            "SELECT ';', E'escaped\\';still quoted', \"semi;colon\";\n"
            "/* outer /* nested; */ still comment */\n"
            "SELECT $$dollar;quoted$$, [bracket;quoted], `backtick;quoted`;\n"
            "-- comment-only suffix;\n"
        )
        self.assertEqual(
            self.runner["split_calcite_query_program"](sql),
            [
                "-- comment-only prefix;\n"
                "SELECT ';', E'escaped\\';still quoted', \"semi;colon\"",
                "/* outer /* nested; */ still comment */\n"
                "SELECT $$dollar;quoted$$, [bracket;quoted], `backtick;quoted`",
            ],
        )

    def test_timeout_is_terminal_and_does_not_prevent_complete_accounting(self) -> None:
        self.make_case("rbot-dsb", "slow", "rbot-dsb", "slow", "SLOW")
        cases = self.runner["discover_cases"](self.input_root)
        run_dir = self.root / "timeout-run"
        config, dependencies = self.config_for(run_dir, cases, timeout_seconds=0.05)
        with mock.patch.dict(self.runner["FULL_RUNNER"], dependencies):
            exit_code = self.runner["run_selected_cases"](
                cases, cases, config, {"benchmarks": ["rbot-dsb"]}
            )
        self.assertEqual(exit_code, 0)
        summary = json.loads((run_dir / "runner-summary.json").read_text())
        self.assertEqual(summary["status"], "complete")
        self.assertEqual(summary["counts"]["selected"], 1)
        self.assertEqual(summary["counts"]["timedOut"], 1)
        self.assertEqual(summary["counts"]["pending"], 0)
        self.assertTrue(summary["integrityVerification"]["verified"])
        self.assertEqual(summary["results"][0]["status"], "timed_out")
        self.assertFalse(summary["results"][0]["reportEvidence"]["present"])

    def test_input_mutation_prevents_a_complete_integrity_summary(self) -> None:
        self.make_case("rbot-dsb", "mutate", "rbot-dsb", "mutate", "MUTATE")
        cases = self.runner["discover_cases"](self.input_root)
        run_dir = self.root / "mutation-run"
        config, dependencies = self.config_for(run_dir, cases)
        with mock.patch.dict(self.runner["FULL_RUNNER"], dependencies):
            exit_code = self.runner["run_selected_cases"](
                cases, cases, config, {"benchmarks": ["rbot-dsb"]}
            )
        self.assertEqual(exit_code, 2)
        summary = json.loads((run_dir / "runner-summary.json").read_text())
        self.assertEqual(summary["status"], "interrupted")
        self.assertFalse(summary["integrityVerification"]["verified"])
        self.assertIn("inputs changed", summary["integrityError"])

    def test_nonzero_without_report_preserves_bounded_stderr_diagnostic(self) -> None:
        self.make_case("rbot-dsb", "fail", "rbot-dsb", "fail", "FAIL")
        cases = self.runner["discover_cases"](self.input_root)
        run_dir = self.root / "failure-run"
        config, dependencies = self.config_for(run_dir, cases)
        with mock.patch.dict(self.runner["FULL_RUNNER"], dependencies):
            exit_code = self.runner["run_selected_cases"](
                cases, cases, config, {"benchmarks": ["rbot-dsb"]}
            )
        self.assertEqual(exit_code, 0)
        summary = json.loads((run_dir / "runner-summary.json").read_text())
        self.assertEqual(summary["status"], "complete")
        self.assertEqual(summary["counts"]["failed"], 1)
        result = summary["results"][0]
        self.assertEqual(result["returnCode"], 3)
        self.assertEqual(result["stderrTail"], "fixture frontend contract rejected")
        self.assertIn("solver produced no report.json", result["runnerError"])
        self.assertIn("fixture frontend contract rejected", result["runnerError"])


if __name__ == "__main__":
    unittest.main()
