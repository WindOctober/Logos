use std::collections::{BTreeMap, BTreeSet};
use std::io::{Read, Write};
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::{MetadataExt, PermissionsExt, symlink};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use logos_ir::ir::SqlStringType;

use super::audit::{
    audit_proof_workspace, audit_rocq_text, classify_precondition_source,
    classify_verification_claim, extract_precondition_definition, problem_declares_final_theorem,
    reject_conditional_verification_claim, strip_rocq_comments,
};
use super::checker::{
    CheckMode, is_trusted_rocq_environment_failure, persist_trusted_environment_preflight_evidence,
    trusted_rocq_check_command,
};
use super::context::{validate_proof_agent_context, write_proof_agent_context};
use super::diagnostics::{CompileCheckpoint, DiagnosticBroker};
use super::goal::{formal_sql_bound_goal_module, formal_sql_goal_module};
use super::navigation::{
    build_ordered_signatures, compact_skeleton_forest, encode_tree_value,
    expand_compact_skeleton_node, parse_skeleton_tree, validate_compacted_skeleton_forest,
};
use super::workspace::archive_trusted_diagnostic_cache;
use super::{
    AgentRunArtifact, DEFAULT_PROOF_AGENT_COMMAND, DEFAULT_PROOF_AGENT_RESUME_COMMAND,
    EXPLICITLY_EXCLUDED_HOST_ENVIRONMENT, EXPLICITLY_EXCLUDED_HOST_ENVIRONMENT_PREFIXES,
    FIXED_HOST_LOCALE, FORMAL_SQL_DECLARATION_SEARCH_SCRIPT, FORMAL_SQL_DOCKER_AGENT_SCRIPT,
    FORMAL_SQL_GOAL_MODULE, FORMAL_SQL_PROOF_AGENT_PROMPT, FORMAL_SQL_ROCQ_CHECK_REQUEST_SCRIPT,
    FORMAL_SQL_SEMANTIC_PRIMER, FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT,
    PROOF_AGENT_HOST_TMP_DIRECTORY, PROOF_AGENT_LAUNCHER_EXPLICIT_ENVIRONMENT,
    PROOF_AGENT_LAUNCHER_HOST_ENVIRONMENT_ALLOWLIST, PROOF_AGENT_LAUNCHER_PATH, PROOF_SOURCE_FILES,
    ProofAgentRoundStage, ProofAgentSessionHome, TRUSTED_CHECKER_EXPLICIT_ENVIRONMENT,
    TRUSTED_CHECKER_HOME, TRUSTED_CHECKER_PATH, TRUSTED_PROBLEM_IMPORT_LINES,
    TRUSTED_ROCQ_IMPORT_ROOTS, TRUSTED_ROCQ_IMPORTS, TrustedRocqImport, TrustedRocqRoot,
    canonical_json_sha256, capture_trusted_proof_sources, is_codex_session_id,
    load_counterexample_handoff, ordered_direct_trusted_rocq_imports,
    persist_initial_problem_compile_checkpoint_evidence, proof_agent_host_tmp_directory,
    proof_agent_instruction_body, proof_agent_launcher_command,
    proof_agent_launcher_environment_policy, proof_agent_round_budget, proof_backend_status,
    remove_proof_workspace_for_formal_witness_restart, render_proof_agent_prompt,
    render_proof_agent_resume_command, restore_problem_compile_checkpoint, sha256_hex,
    snapshot_proof_workspace, static_prompt_and_primer_bytes, trusted_checker_environment_policy,
    validate_authority_closure, write_trusted_proof_agent_launcher, write_trusted_rocq_checker,
};
use crate::artifacts::ArtifactWriter;
use crate::core::{
    FormalAttribute, FormalAttributeType, FormalFunctionTerm, FormalQueryExpr, FormalScalarExpr,
    FormalSchema, FormalTable, FormalTableConstraints, FormalUniqueIndexConstraint, LoweredProgram,
    LoweredQuery, LoweringStatus, SqlEnvironment, SqlTimeZone, VerificationInput, VerificationMode,
    emit_rocq_query_expr_proof_module_for_mode, query_expr_output_signature,
};
use crate::engine::config::{Config, ExecutionMode};
use crate::engine::report::{
    AcceptedDiagnosticSourceAudit, AgentAudit, AgentRunLog, BackendStatus,
    DiagnosticArtifactBinding, DiagnosticCheckerInvocation, PreconditionSource,
    ProblemCompileCheckpointEvidence, ProofAgentDecision, ProofCheckpointTransition,
    ProofCounterexampleHandoff, ProofSessionRestartReason, ProofWorkspace,
    ProofWorkspaceTransition, ProofWorkspaceTransitionReason, RejectedDiagnosticSourceAudit,
    TrustedCheckInvocation, TrustedDiagnosticCacheEvidence, VerificationClaimKind,
};
use crate::usage::LlmUsage;
use crate::validation::{
    FormalWitnessColumn, FormalWitnessRow, FormalWitnessSnapshot, FormalWitnessTable,
    FormalWitnessValue,
};

const ROOT_MAKEFILE: &str = include_str!("../../../../Makefile");

fn proof_test_config(root: &Path) -> Config {
    Config {
        calcite_ir_command: String::new(),
        execution_mode: ExecutionMode::Verify,
        disable_counterexample_search: false,
        reuse_llm_assessment: false,
        force_llm_assessment: false,
        llm_assessment_cache_dir: root.join("assessment-cache"),
        proposal_command: String::new(),
        proposal_resume_command: String::new(),
        postgres_url: None,
        statement_timeout_ms: 1_000,
        sql_time_zone: SqlTimeZone::utc(),
        sql_environment: SqlEnvironment::default(),
        verification_mode: VerificationMode::OutcomeUnconditional,
        proof_agent_command: String::new(),
        proof_agent_resume_command: String::new(),
        proof_agent_memory_limit_mib: 512,
        proof_agent_storage_limit_mib: 512,
        rocq_session_limits: Default::default(),
        proof_agent_timeout_seconds: 60,
        proof_check_timeout_seconds: 60,
        proof_docker_image: "test-image".to_owned(),
        proof_rocq_opam_switch: None,
        logos_repo_root: None,
    }
}

#[test]
fn only_verification_mode_enables_the_proof_agent() {
    for mode in [
        ExecutionMode::Verify,
        ExecutionMode::PrepareWorkspace,
        ExecutionMode::TransformOnly,
        ExecutionMode::AssessmentOnly,
        ExecutionMode::TypedWitnessAudit,
    ] {
        let mut config = proof_test_config(Path::new("/unused"));
        config.execution_mode = mode;
        let report = super::base_proof_agent_configuration(&config, None).unwrap();
        assert_eq!(report.enabled, mode == ExecutionMode::Verify);
    }
}

#[test]
fn typed_witness_values_render_exact_string_typmods_and_numeric_carriers() {
    assert_eq!(
        super::witness::rocq_witness_string_typmod(SqlStringType::Varchar { length: Some(16) }),
        "StringVarcharN 16"
    );
    assert_eq!(
        super::witness::rocq_witness_value(
            &FormalWitnessValue::NumericFinite {
                coefficient: "-12345".to_owned(),
                scale: 2,
            },
            FormalAttributeType::Decimal {
                precision: 7,
                scale: 2,
            },
        )
        .unwrap(),
        "Value_numeric (Some (numeric_of_scaled (-12345)%Z (2)%Z))"
    );
    assert_eq!(
        super::witness::rocq_witness_value(
            &FormalWitnessValue::NumericNaN,
            FormalAttributeType::Numeric,
        )
        .unwrap(),
        "Value_numeric (Some NumericNaN)"
    );
    assert_eq!(
        super::witness::rocq_witness_value(
            &FormalWitnessValue::Float64Bits((-0.0_f64).to_bits()),
            FormalAttributeType::Double,
        )
        .unwrap(),
        "Value_double (Some (Float64OfBits (9223372036854775808)%Z))"
    );
    assert_eq!(
        super::witness::rocq_witness_value(
            &FormalWitnessValue::Timestamp("946684800000000".to_owned()),
            FormalAttributeType::Timestamp { precision: Some(6) },
        )
        .unwrap(),
        "Value_timestamp (Some (946684800000000)%Z)"
    );
}

#[test]
fn witness_codegen_specializes_cardinality_only_for_nonempty_tables() {
    let attribute = FormalAttribute {
        name: "id".to_owned(),
        ty: FormalAttributeType::Int32,
    };
    let table = |relation: &str| FormalTable {
        relation: relation.to_owned(),
        attributes: vec![attribute.clone()],
        constraints: if relation == "nonempty_table" {
            FormalTableConstraints {
                not_null: vec![attribute.clone()],
                primary_key: Some(vec![attribute.clone()]),
                unique_indexes: vec![FormalUniqueIndexConstraint {
                    terms: vec![FormalFunctionTerm::Attribute {
                        name: "id".to_owned(),
                        ty: FormalAttributeType::Int32,
                    }],
                    predicate: None,
                }],
                ..FormalTableConstraints::default()
            }
        } else {
            FormalTableConstraints::default()
        },
    };
    let witness_table = |relation: &str, rows| FormalWitnessTable {
        relation: relation.to_owned(),
        columns: vec![FormalWitnessColumn {
            name: "id".to_owned(),
            ty: FormalAttributeType::Int32,
        }],
        rows,
    };
    let schema = FormalSchema {
        tables: vec![table("empty_table"), table("nonempty_table")],
        rocq_module: String::new(),
    };
    let snapshot = FormalWitnessSnapshot {
        schema_version: 1,
        tables: vec![
            witness_table("empty_table", vec![]),
            witness_table(
                "nonempty_table",
                vec![FormalWitnessRow {
                    cells: vec![FormalWitnessValue::Int32(7)],
                }],
            ),
        ],
    };

    let modules = super::witness::formal_sql_witness_modules(&schema, Some(&snapshot)).unwrap();
    let data = modules.data.as_ref().unwrap();
    assert!(data.contains("Lemma generated_witness_instance_cardinal"));
    assert!(!data.contains("generated_witness_table_0_attributes"));
    assert!(data.contains("Definition generated_witness_table_1_attributes"));
    assert!(!data.contains("Definition generated_witness_table_0_rows"));
    assert!(data.contains("Definition generated_witness_table_1_rows"));
    assert!(!data.contains("generated_witness_table_0_instance_cardinal"));
    assert!(data.contains("generated_witness_table_1_instance_cardinal"));
    assert!(data.contains("WitnessTable (Rel (\"nonempty_table\"))"));
    assert!(
        modules
            .witness
            .contains("From Stdlib Require Import List String.")
    );
    assert!(modules.witness.contains("Open Scope string_scope."));
    assert!(
        modules
            .witness
            .contains("generated_witness_table_constraint_0_conforms")
    );
    assert_eq!(modules.constraint_modules.len(), 8);
    for expected in [
        "Table0001NotNull",
        "Table0001Primary",
        "Table0001Index0000Nonempty",
        "Table0001Index0000Predicate",
        "Table0001Index0000Terms",
        "Table0001Index0000Unique",
        "Table0001Index0000",
        "TableConstraint0001",
    ] {
        assert!(
            modules
                .constraint_modules
                .iter()
                .any(|(name, _)| name == expected)
        );
    }
    assert!(
        modules
            .constraint_modules
            .iter()
            .any(|(_, source)| source.contains("generated_witness_table_constraint_1_conforms"))
    );
    let table_assembly = modules
        .constraint_modules
        .iter()
        .find(|(name, _)| name == "TableConstraint0001")
        .map(|(_, source)| source)
        .expect("populated table assembly module");
    assert!(table_assembly.contains("rewrite Schema.generated_table_constraint_1_unique_indexes"));
    assert!(!table_assembly.contains("unfold Schema.generated_table_constraint_1"));
    let index_terms = modules
        .constraint_modules
        .iter()
        .find(|(name, _)| name == "Table0001Index0000Terms")
        .map(|(_, source)| source)
        .expect("partial-index term certificate module");
    assert!(index_terms.contains("if unique_index_row_participates"));
    assert!(!index_terms.contains("unique_index_all_row_terms_succeedb_sound"));
    let index_assembly = modules
        .constraint_modules
        .iter()
        .find(|(name, _)| name == "Table0001Index0000")
        .map(|(_, source)| source)
        .expect("partial-index assembly module");
    assert!(index_assembly.contains("unique_index_conforms_of_reflected_components"));
    assert!(
        modules
            .witness
            .contains("generated_witness_table_constraints_conform")
    );
    assert!(
        modules
            .witness
            .contains("witness_database_conforms_of_certificates")
    );
    assert!(
        !modules
            .witness
            .contains("Lemma generated_witness_reflection")
    );
}

fn command_environment(command: &Command) -> BTreeMap<String, String> {
    command
        .get_envs()
        .map(|(name, value)| {
            (
                name.to_string_lossy().into_owned(),
                value
                    .expect("launch policy never uses per-name removals after env_clear")
                    .to_string_lossy()
                    .into_owned(),
            )
        })
        .collect()
}

fn send_diagnostic_broker_request(
    socket: &std::path::Path,
    candidate_root: &std::path::Path,
    mut request: serde_json::Value,
) -> serde_json::Value {
    let candidate = request
        .get("candidatePath")
        .and_then(serde_json::Value::as_str)
        .map(|candidate_path| candidate_root.join(candidate_path))
        .and_then(|candidate_path| std::fs::read(candidate_path).ok())
        .unwrap_or_default();
    request
        .as_object_mut()
        .expect("broker test request must be a JSON object")
        .entry("candidateBytes")
        .or_insert_with(|| serde_json::json!(candidate.len()));
    let mut stream = UnixStream::connect(socket).expect("connect to diagnostic broker");
    let mut payload = serde_json::to_vec(&request).expect("serialize broker request");
    payload.push(b'\n');
    stream.write_all(&payload).expect("write broker request");
    stream
        .write_all(&candidate)
        .expect("stream broker candidate bytes");
    let mut response = String::new();
    stream
        .read_to_string(&mut response)
        .expect("read broker response");
    serde_json::from_str(&response).expect("parse broker response")
}

fn complete_broker_witness_fixture(proof: &Path) {
    // These broker fixtures predate the split WitnessData/WitnessModules
    // contract. Keep them exercising the broker, not failing at snapshot.
    std::fs::write(proof.join("WitnessData.v"), "(* witness data *)\n").unwrap();
    std::fs::create_dir_all(proof.join("WitnessModules")).unwrap();
    std::fs::write(proof.join("WitnessModules/ORDER"), "").unwrap();
}

#[test]
#[ignore = "run via test-trusted-rocq-check-sandbox.sh with LOGOS_ROCQ_BROKER_TEST_BIN"]
fn real_incremental_sandbox_diagnostics() {
    fn copy_tree(source: &Path, destination: &Path) {
        std::fs::create_dir_all(destination).unwrap();
        for entry in std::fs::read_dir(source).unwrap() {
            let entry = entry.unwrap();
            if entry.file_type().unwrap().is_dir() {
                copy_tree(&entry.path(), &destination.join(entry.file_name()));
            } else {
                assert!(entry.file_type().unwrap().is_file());
                std::fs::copy(entry.path(), destination.join(entry.file_name())).unwrap();
            }
        }
    }
    let env_path =
        |name: &str| PathBuf::from(std::env::var_os(name).expect("sandbox fixture environment"));
    let authority = env_path("LOGOS_TEST_ROCQ_AUTHORITY");
    let switch = env_path("LOGOS_TEST_ROCQ_SWITCH");
    let temp = tempfile::tempdir().unwrap();
    let workspace = temp.path().join("workspace");
    let checker = temp.path().join("trusted-launcher/checker.sh");
    std::fs::create_dir_all(checker.parent().unwrap()).unwrap();
    std::fs::write(&checker, FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT).unwrap();
    copy_tree(&env_path("LOGOS_TEST_ROCQ_WORKSPACE"), &workspace);
    let cache = super::workspace::trusted_diagnostic_cache_directory(&checker);
    copy_tree(&env_path("LOGOS_TEST_ROCQ_CACHE"), &cache);
    let prefix = "From Logos.FormalSQL Require Import ProofAgentFacade.\nFrom LogosGenerated Require Import Schema Queries Witness.\nTheorem sandbox_problem_marker : sandbox_query_marker.\nProof.";
    let run = |source: &str,
               mode: super::diagnostics::CandidateKind,
               path: &str,
               session: Option<&mut crate::engine::rocq_session::IncrementalDiagnostics>,
               seconds: u64| {
        let input = if mode == super::diagnostics::CandidateKind::Module {
            workspace.join(path)
        } else {
            workspace.join("Problem.v")
        };
        std::fs::write(input, source).unwrap();
        let (invocation, output) = super::checker::run_host_diagnostic_rocq_check(
            &checker,
            &workspace,
            &authority,
            Some(&switch),
            mode,
            path,
            seconds,
            seconds,
            session.map(|session| (session, source)),
            None,
            super::checker::DiagnosticOperation::Check,
        );
        (invocation, output.expect("launch real checker"))
    };
    let mut baseline_ms = 0;
    for index in 0..5 {
        let (invocation, output) = run(
            &format!("{prefix} exact {index}. Qed."),
            super::diagnostics::CandidateKind::Problem,
            "Problem.v",
            None,
            30,
        );
        assert_eq!(
            output.status.code(),
            Some(1),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        baseline_ms += invocation.elapsed_ms;
    }
    let mut session = crate::engine::rocq_session::IncrementalDiagnostics::new(
        crate::engine::rocq_session::SessionLimits {
            max_sessions: 2,
            ..Default::default()
        },
    );
    let mut incremental_ms = 0;
    for index in 0..5 {
        let (invocation, output) = run(
            &format!("{prefix} exact {index}. Qed."),
            super::diagnostics::CandidateKind::Problem,
            "Problem.v",
            Some(&mut session),
            30,
        );
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(output.status.code(), Some(1), "{stderr}");
        if index == 0 {
            assert!(stderr.contains("cold=true"), "{stderr}");
            incremental_ms += invocation.elapsed_ms;
            continue;
        }
        assert!(stderr.contains("compiler_required=false"), "{stderr}");
        assert!(stderr.contains("Current goals:"), "{stderr}");
        assert!(
            stderr.contains(if index == 1 {
                "reused_sentences=0"
            } else {
                "reused_sentences=4"
            }),
            "{stderr}"
        );
        incremental_ms += invocation.elapsed_ms;
    }
    eprintln!(
        "five sandboxed failing revisions: baseline={baseline_ms}ms incremental={incremental_ms}ms (includes cold session startup)"
    );

    let good = format!("{prefix} exact I. Qed.");
    let (_, output) = run(
        &good,
        super::diagnostics::CandidateKind::Problem,
        "Problem.v",
        Some(&mut session),
        30,
    );
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        temp.path()
            .join("problem-compile-cache/Problem.vo")
            .is_file()
    );
    assert_eq!(
        std::fs::read_to_string(temp.path().join("problem-compile-cache/Problem.v")).unwrap(),
        good
    );
    let final_check = trusted_rocq_check_command(
        &checker,
        &workspace,
        &authority,
        Some(&switch),
        Duration::from_secs(60),
        CheckMode::Full,
    )
    .output()
    .unwrap();
    assert!(
        final_check.status.success(),
        "{}",
        String::from_utf8_lossy(&final_check.stderr)
    );

    let (_, output) = run(
        "Lemma isolated_scratch : True. Proof. exact I. Qed.",
        super::diagnostics::CandidateKind::Scratch,
        "scratch/probe.v",
        Some(&mut session),
        30,
    );
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        std::fs::read_to_string(temp.path().join("problem-compile-cache/Problem.v")).unwrap(),
        good
    );

    // A REPL reaching EOF with an open proof must not count as a pass.
    let (_, output) = run(
        &format!("{good}\nLemma unfinished : True. Proof."),
        super::diagnostics::CandidateKind::Problem,
        "Problem.v",
        Some(&mut session),
        30,
    );
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("compiler_required=true"));

    let (_, output) = run(
        "Lemma incremental_fact : True. Proof. exact I. Qed.",
        super::diagnostics::CandidateKind::Module,
        "ProofModules/IncrementalFact.v",
        Some(&mut session),
        30,
    );
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(cache.join("ProofModules/IncrementalFact.vo").is_file());
    let (_, output) = run(
        &good,
        super::diagnostics::CandidateKind::Problem,
        "Problem.v",
        Some(&mut session),
        30,
    );
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(String::from_utf8_lossy(&output.stderr).contains("cold=true"));

    // Re-arm and warm the session before checking a tactic timeout.
    for index in 0..2 {
        let (_, output) = run(
            &format!("{prefix} exact {index}. Qed."),
            super::diagnostics::CandidateKind::Problem,
            "Problem.v",
            Some(&mut session),
            30,
        );
        assert_eq!(output.status.code(), Some(1));
    }

    let (invocation, output) = run(
        &format!("{prefix} repeat (pose proof I). Qed."),
        super::diagnostics::CandidateKind::Problem,
        "Problem.v",
        Some(&mut session),
        1,
    );
    assert!(
        invocation.timed_out,
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(output.status.code(), Some(124));
    assert!(String::from_utf8_lossy(&output.stderr).contains("session_discarded=true"));
    let (_, output) = run(
        &good,
        super::diagnostics::CandidateKind::Problem,
        "Problem.v",
        Some(&mut session),
        30,
    );
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(String::from_utf8_lossy(&output.stderr).contains("cold=true"));
    drop(session);
    // Exercise the real upload/audit/broker path too: its state must retain
    // the session across connections, but never advance a scratch checkpoint.
    let stage = temp.path().join("agent-stage");
    let artifacts = temp.path().join("artifacts");
    std::fs::create_dir_all(stage.join("scratch")).unwrap();
    std::fs::create_dir_all(&artifacts).unwrap();
    let broker = DiagnosticBroker::start(
        &artifacts,
        1,
        1,
        &checker,
        &workspace,
        &authority,
        Some(&switch),
        None,
        2 * 1024 * 1024 * 1024,
        Instant::now() + Duration::from_secs(90),
    )
    .unwrap();
    for index in 0..4 {
        let tactic = if index == 3 {
            "I".to_owned()
        } else {
            index.to_string()
        };
        let source = format!("Lemma broker_probe : True. Proof. exact {tactic}. Qed.");
        std::fs::write(stage.join("scratch/probe.v"), &source).unwrap();
        let response = send_diagnostic_broker_request(
            broker.socket_path(),
            &stage,
            serde_json::json!({
                "schemaVersion": 2, "nonce": broker.nonce(), "mode": "scratch",
                "candidatePath": "scratch/probe.v", "purpose": "semantic-equivalence",
                "candidateSha256": sha256_hex(source.as_bytes()), "requestedTimeoutSeconds": 30,
            }),
        );
        assert_eq!(response["compilePassed"], index == 3, "{response}");
        assert_eq!(response["compileCheckpointAdvanced"], false, "{response}");
        if index == 2 {
            assert!(
                response["stderr"]
                    .as_str()
                    .unwrap()
                    .contains("reused_sentences=2"),
                "{response}"
            );
        }
    }
    // A persisted scratch draft is submitted in MODULE mode from its first
    // revision. The real wrapper maps only its wire path; the existing
    // broker must audit/publish it under the final logical module name.
    let wrapper = stage.join("run-rocq-check.sh");
    std::fs::write(&wrapper, FORMAL_SQL_ROCQ_CHECK_REQUEST_SCRIPT).unwrap();
    std::fs::create_dir_all(stage.join("scratch/ProofModules")).unwrap();
    let draft = stage.join("scratch/ProofModules/DraftBridge.v");
    let check_draft = || {
        Command::new("bash")
            .arg(&wrapper)
            .args([
                "--mode",
                "module",
                "--candidate",
                "scratch/ProofModules/DraftBridge.v",
                "--purpose",
                "semantic-equivalence",
                "--timeout-seconds",
                "30",
            ])
            .env("LOGOS_PROOF_DIAGNOSTIC_SOCKET", broker.socket_path())
            .env("LOGOS_PROOF_DIAGNOSTIC_NONCE", broker.nonce())
            .output()
            .unwrap()
    };
    std::fs::write(&draft, "Lemma draft_fact : True. Proof. exact 0. Qed.\n").unwrap();
    assert!(!check_draft().status.success());
    assert!(!workspace.join("ProofModules/DraftBridge.v").exists());
    assert!(!cache.join("ProofModules/DraftBridge.vo").exists());
    assert!(draft.is_file(), "failed draft remains editable");

    let draft_source = "Lemma draft_fact : True. Proof. exact I. Qed.\n";
    std::fs::write(&draft, draft_source).unwrap();
    let published = check_draft();
    assert!(
        published.status.success(),
        "{}",
        String::from_utf8_lossy(&published.stderr)
    );
    assert!(String::from_utf8_lossy(&published.stdout).contains("No copy or second module check"));
    assert_eq!(
        std::fs::read_to_string(workspace.join("ProofModules/DraftBridge.v")).unwrap(),
        draft_source
    );
    assert!(
        !stage.join("ProofModules/DraftBridge.v").exists(),
        "no client-side source copy is required"
    );
    let object = std::fs::read(cache.join("ProofModules/DraftBridge.vo")).unwrap();
    assert!(!object.is_empty());
    let repeated = check_draft();
    assert!(
        repeated.status.success(),
        "{}",
        String::from_utf8_lossy(&repeated.stderr)
    );
    assert!(String::from_utf8_lossy(&repeated.stderr).contains("already_cached=true"));
    assert_eq!(
        std::fs::read(cache.join("ProofModules/DraftBridge.vo")).unwrap(),
        object
    );

    std::fs::write(
        &draft,
        format!("{draft_source}(* changed after publication *)\n"),
    )
    .unwrap();
    let changed = check_draft();
    assert!(!changed.status.success());
    assert!(String::from_utf8_lossy(&changed.stderr).contains("immutable"));
    assert_eq!(
        std::fs::read_to_string(workspace.join("ProofModules/DraftBridge.v")).unwrap(),
        draft_source
    );
    assert_eq!(
        std::fs::read(cache.join("ProofModules/DraftBridge.vo")).unwrap(),
        object
    );

    let assembled = "From LogosGenerated Require Import Schema Queries Witness.\nFrom LogosGenerated.ProofModules Require Import DraftBridge.\nTheorem sandbox_problem_marker : sandbox_query_marker.\nProof. exact draft_fact. Qed.".to_owned();
    std::fs::write(stage.join("Problem.v"), &assembled).unwrap();
    let response = send_diagnostic_broker_request(
        broker.socket_path(),
        &stage,
        serde_json::json!({
            "schemaVersion": 2, "nonce": broker.nonce(), "mode": "problem",
            "candidatePath": "Problem.v", "purpose": "assembly",
            "candidateSha256": sha256_hex(assembled.as_bytes()), "requestedTimeoutSeconds": 30,
        }),
    );
    assert_eq!(response["compilePassed"], true, "{response}");
    let probe = |mode: &str, path: &str, source: &str, stop: usize, timeout: u64| {
        let file = stage.join(path);
        std::fs::create_dir_all(file.parent().unwrap()).unwrap();
        std::fs::write(file, source).unwrap();
        send_diagnostic_broker_request(
            broker.socket_path(),
            &stage,
            serde_json::json!({
                "schemaVersion": 2, "nonce": broker.nonce(), "mode": mode,
                "candidatePath": path, "purpose": "semantic-equivalence",
                "candidateSha256": sha256_hex(source.as_bytes()), "requestedTimeoutSeconds": timeout,
                "probe": {"stopAfter": stop},
            }),
        )
    };
    // The checkpoint dedup guard does not prevent examining its earlier goals.
    let response = probe("problem", "Problem.v", &assembled, 4, 30);
    assert_eq!(response["probe"]["passed"], true, "{response}");
    assert_eq!(response["compilePassed"], false);
    assert!(
        response["stdout"].as_str().unwrap().contains("goal"),
        "{response}"
    );
    let probe_source = "Lemma local_fact : True. Proof. exact I. Qed.\nDefinition unfinished := {";
    let path = "ProofModules/LocalProbe.v";
    // The suffix cannot be framed, but is never parsed/audited/executed here.
    // Probe a solved proof as well, then rewind to the open proof state.
    for stop in [2, 3, 4, 2] {
        let response = probe("module", path, probe_source, stop, 30);
        assert_eq!(response["probe"]["passed"], true, "{response}");
        assert_eq!(response["compilePassed"], false);
        assert_eq!(response["compileCheckpointAdvanced"], false);
        assert!(
            response["stderr"]
                .as_str()
                .unwrap()
                .contains("compiler_required=false")
        );
        assert!(!workspace.join(path).exists());
        assert!(!cache.join("ProofModules/LocalProbe.vo").exists());
    }
    let response = probe(
        "module",
        path,
        "Lemma local_fact : True. Proof. exact 0.",
        3,
        30,
    );
    assert_eq!(response["probe"]["passed"], false, "{response}");
    assert_eq!(response["exitCode"], 1);
    let response = probe(
        "scratch",
        "scratch/local.v",
        "Lemma local : True. Proof.",
        2,
        30,
    );
    assert_eq!(response["probe"]["passed"], true, "{response}");
    assert!(!workspace.join("scratch/local.v").exists());
    let response = probe(
        "scratch",
        "scratch/local.v",
        "Lemma local : True. Proof. repeat (pose proof I).",
        3,
        1,
    );
    assert_eq!(response["timedOut"], true, "{response}");
    assert_eq!(response["probe"]["passed"], false);
    // Invalid prefix framing and disallowed commands must not fall back to coqc.
    let response = probe("module", path, probe_source, 5, 30);
    assert!(response["sequence"].is_null(), "{response}");
    let response = probe("module", path, "Axiom bad : True.", 1, 30);
    assert!(response["sequence"].is_null(), "{response}");
    assert!(response["error"].as_str().unwrap().contains("audit"));
    // Full checks still execute the suffix; probe success cannot certify it.
    for (source, passes) in [
        (probe_source, false),
        ("Lemma local_fact : True. Proof. exact I. Qed.", true),
    ] {
        std::fs::write(stage.join(path), source).unwrap();
        let response = send_diagnostic_broker_request(
            broker.socket_path(),
            &stage,
            serde_json::json!({
                "schemaVersion": 2, "nonce": broker.nonce(), "mode": "module",
                "candidatePath": path, "purpose": "semantic-equivalence",
                "candidateSha256": sha256_hex(source.as_bytes()), "requestedTimeoutSeconds": 30,
            }),
        );
        assert_eq!(response["compilePassed"], passes, "{response}");
        assert_eq!(workspace.join(path).exists(), passes);
    }
    let outcome = broker.finish().unwrap();
    assert_eq!(outcome.invocations.len(), 18);
    assert!(outcome.latest_checkpoint.is_some());
    assert_eq!(outcome.latest_checkpoint.as_ref().unwrap().sequence, 8);
    for invocation in &outcome.invocations[8..16] {
        assert!(invocation.probe.is_some());
        assert_eq!(invocation.compile_passed, Some(false));
    }
    let shared = artifacts.join("proof-stage/proof-agent/diagnostic-inputs/0001");
    for sequence in 1..=8 {
        let checked = artifacts.join(format!(
            "proof-stage/proof-agent/rounds/01/interactive-diagnostics/{sequence:02}/checked-workspace"
        ));
        for name in [
            "Schema.v",
            "Queries.v",
            "WitnessData.v",
            "Witness.v",
            "Goal.v",
            "WitnessModules/ORDER",
        ] {
            let original = std::fs::metadata(workspace.join(name)).unwrap();
            let saved = std::fs::metadata(shared.join(name)).unwrap();
            let linked = std::fs::symlink_metadata(checked.join(name)).unwrap();
            assert!(linked.is_file());
            assert_ne!(saved.ino(), original.ino());
            assert_eq!((saved.dev(), saved.ino()), (linked.dev(), linked.ino()));
        }
        assert!(checked.join("shared-inputs.json").is_file());
    }
    for invocation in &outcome.invocations[4..7] {
        assert_eq!(invocation.mode.as_deref(), Some("module"));
        assert_eq!(
            invocation.candidate_path.as_deref(),
            Some("ProofModules/DraftBridge.v")
        );
        assert_eq!(invocation.compile_checkpoint_advanced, Some(false));
    }
    assert_eq!(outcome.invocations[4].compile_passed, Some(false));
    assert_eq!(outcome.invocations[5].compile_passed, Some(true));
    // Final assembly imports the original object at its original logical
    // name and still passes the unchanged kernel-check closure.
    std::fs::write(workspace.join("Problem.v"), assembled).unwrap();
    let final_check = trusted_rocq_check_command(
        &checker,
        &workspace,
        &authority,
        Some(&switch),
        Duration::from_secs(60),
        CheckMode::Full,
    )
    .output()
    .unwrap();
    assert!(
        final_check.status.success(),
        "{}",
        String::from_utf8_lossy(&final_check.stderr)
    );
    assert_eq!(
        std::fs::read(cache.join("ProofModules/DraftBridge.vo")).unwrap(),
        object
    );
    assert_eq!(
        std::fs::read_dir(temp.path().join("host-tmp"))
            .unwrap()
            .count(),
        0,
        "dropping/timing out sessions must clean their sandbox scratch trees"
    );
}

fn signature_test_attribute(name: &str) -> FormalAttribute {
    FormalAttribute {
        name: name.to_owned(),
        ty: FormalAttributeType::Int32,
    }
}

fn signature_test_table(relation: &str, names: &[&str]) -> FormalQueryExpr {
    FormalQueryExpr::Table {
        relation: relation.to_owned(),
        columns: names
            .iter()
            .map(|name| signature_test_attribute(name))
            .collect(),
    }
}

fn signature_test_lowered_query(query: FormalQueryExpr) -> LoweredQuery {
    let output_signature = query_expr_output_signature(&query).expect("valid test signature");
    LoweredQuery {
        status: LoweringStatus::Lowered,
        bindings: Vec::new(),
        query_expr: Some(query),
        output_signature: Some(output_signature),
        diagnostics: Vec::new(),
    }
}

#[test]
fn ordered_signature_navigation_is_occurrence_exact_root_reachable_and_covers_subqueries() {
    let source_frontier = FormalQueryExpr::CrossJoin {
        left: Box::new(signature_test_table("source_left", &["a"])),
        right: Box::new(signature_test_table("source_right", &["b"])),
    };
    let target_frontier = FormalQueryExpr::CrossJoin {
        left: Box::new(signature_test_table("target_left", &["a", "b"])),
        right: Box::new(FormalQueryExpr::EmptyTuple),
    };
    let source_incompatible_root = FormalQueryExpr::Distinct {
        input: Box::new(source_frontier.clone()),
    };
    let target_incompatible_root = FormalQueryExpr::OrderBy {
        keys: Vec::new(),
        input: Box::new(target_frontier.clone()),
    };
    let correlated = FormalQueryExpr::Selection {
        predicate: FormalScalarExpr::Exists {
            query: Box::new(signature_test_table("subquery", &["x"])),
        },
        input: Box::new(signature_test_table("outer", &["a"])),
    };
    let source = LoweredProgram {
        status: LoweringStatus::Lowered,
        statements: vec![
            signature_test_lowered_query(source_frontier),
            signature_test_lowered_query(source_incompatible_root),
            signature_test_lowered_query(correlated.clone()),
        ],
        diagnostics: Vec::new(),
    };
    let target = LoweredProgram {
        status: LoweringStatus::Lowered,
        statements: vec![
            signature_test_lowered_query(target_frontier),
            signature_test_lowered_query(target_incompatible_root),
            signature_test_lowered_query(correlated),
        ],
        diagnostics: Vec::new(),
    };

    let text =
        build_ordered_signatures(&source, &target).expect("build ordered-signature navigation");
    let artifact: serde_json::Value = serde_json::from_str(&text).expect("parse artifact");
    assert_eq!(artifact["schemaVersion"], 2);
    assert!(artifact.get("indexing").is_none());
    assert!(
        artifact["authority"]
            .as_str()
            .expect("authority text")
            .contains("navigation_only")
    );
    assert!(
        artifact["signatureIdentity"]
            .as_str()
            .expect("signature identity")
            .contains("Vec<FormalAttribute>::eq")
    );
    let nodes = artifact["nodes"].as_array().expect("node array");
    assert!(nodes.iter().any(|node| {
        node["side"] == "source"
            && node["statementIndex"] == 3
            && node["rolePath"] == "root.predicate.exists.query"
    }));
    assert!(nodes.iter().any(|node| {
        node["nodeId"] == "S3.N0" && node["rolePath"] == "root" && node["preorderIndex"] == 0
    }));
    let source_subquery = nodes
        .iter()
        .find(|node| {
            node["side"] == "source"
                && node["statementIndex"] == 3
                && node["rolePath"] == "root.predicate.exists.query"
        })
        .expect("source subquery occurrence");
    let target_subquery = nodes
        .iter()
        .find(|node| {
            node["side"] == "target"
                && node["statementIndex"] == 3
                && node["rolePath"] == "root.predicate.exists.query"
        })
        .expect("target subquery occurrence");
    assert_ne!(source_subquery["nodeId"], target_subquery["nodeId"]);
    assert_eq!(
        source_subquery["signatureId"],
        target_subquery["signatureId"]
    );
    let declared_node_count = artifact["sourceProgram"]
        .as_array()
        .expect("source program")
        .iter()
        .chain(
            artifact["targetProgram"]
                .as_array()
                .expect("target program")
                .iter(),
        )
        .map(|statement| statement["nodeCount"].as_u64().expect("node count") as usize)
        .sum::<usize>();
    assert_eq!(declared_node_count, nodes.len());
    let comparisons = artifact["comparisons"]
        .as_array()
        .expect("comparison array");
    assert!(comparisons.iter().any(|comparison| {
        comparison["statementIndex"] == 1
            && comparison["rolePath"] == "root.left"
            && comparison["signatureEqual"] == false
            && comparison["mismatch"]["kind"] == "arity"
    }));
    let frontiers = artifact["normalizationFrontierHints"]
        .as_array()
        .expect("frontier array");
    assert!(
        frontiers
            .iter()
            .any(|frontier| { frontier["statementIndex"] == 1 && frontier["rolePath"] == "root" })
    );
    assert!(!frontiers.iter().any(|frontier| {
        frontier["statementIndex"] == 2 && frontier["rolePath"] == "root.input"
    }));
}

#[test]
fn ordered_signature_navigation_rejects_declared_root_signature_drift() {
    let query = signature_test_table("t", &["a"]);
    let mut lowered = signature_test_lowered_query(query);
    lowered.output_signature = Some(vec![signature_test_attribute("different")]);
    let source = LoweredProgram {
        status: LoweringStatus::Lowered,
        statements: vec![lowered],
        diagnostics: Vec::new(),
    };
    let target = LoweredProgram {
        status: LoweringStatus::Lowered,
        statements: vec![signature_test_lowered_query(signature_test_table(
            "t",
            &["a"],
        ))],
        diagnostics: Vec::new(),
    };
    let error = build_ordered_signatures(&source, &target)
        .expect_err("signature drift must fail closed")
        .to_string();
    assert!(error.contains("ordered-signature context drift"));
    assert!(error.contains("source statement 1"));
}

#[test]
fn ordered_signature_navigation_accepts_artifacts_larger_than_the_legacy_128_kib() {
    let columns = (0..4_096)
        .map(|index| FormalAttribute {
            name: format!("wide_ordered_signature_column_{index:04}_with_exact_position_metadata"),
            ty: FormalAttributeType::Int32,
        })
        .collect::<Vec<_>>();
    let query = FormalQueryExpr::Table {
        relation: "wide_signature_table".to_owned(),
        columns,
    };
    let source = LoweredProgram {
        status: LoweringStatus::Lowered,
        statements: vec![signature_test_lowered_query(query.clone())],
        diagnostics: Vec::new(),
    };
    let target = LoweredProgram {
        status: LoweringStatus::Lowered,
        statements: vec![signature_test_lowered_query(query)],
        diagnostics: Vec::new(),
    };

    let text = build_ordered_signatures(&source, &target).expect("build wide signature navigation");
    assert!(text.len() > 128 * 1024, "fixture must exceed the old limit");
    let artifact: serde_json::Value = serde_json::from_str(&text).expect("parse artifact");
    assert!(artifact.get("byteLimit").is_none());
    assert!(artifact.get("nodeLimit").is_none());
}

#[test]
fn scheduler_policy_labels_describe_deadline_bounded_wip_and_checkpoint_deduplication() {
    assert_eq!(
        super::PROOF_AGENT_DIAGNOSTIC_SCHEDULING_POLICY,
        "sequential_host_broker_invocation_deadline_bounded"
    );
    assert!(super::PROOF_AGENT_SCRATCH_PERSISTENCE_POLICY.contains("checked_promotion"));
    assert_eq!(
        super::PROOF_AGENT_WRITABLE_STORAGE_POLICY,
        "single_kernel_tmpfs_all_agent_writes_with_read_only_root_v1"
    );
    assert!(
        super::PROOF_AGENT_SCRATCH_PERSISTENCE_POLICY.contains("exact_digest_checked_promotion")
    );
    assert!(super::PROOF_AGENT_COMPILE_CHECKPOINT_POLICY.contains("digest_deduplicated"));
}

#[test]
#[ignore = "requires Unix socket creation, unavailable in restricted test sandboxes"]
fn diagnostic_broker_accepts_more_than_the_legacy_short_check_quota() {
    let diagnostic_count = 25usize;
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after Unix epoch")
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "logos-diagnostic-broker-test-{}-{nonce}",
        std::process::id()
    ));
    let stage = root.join("stage");
    let artifacts = root.join("artifacts");
    let proof = root.join("proof");
    let repo = root.join("repo");
    std::fs::create_dir_all(&stage).expect("create broker stage");
    std::fs::create_dir_all(&artifacts).expect("create artifact root");
    std::fs::create_dir_all(&proof).expect("create proof workspace");
    std::fs::create_dir_all(&repo).expect("create repository root");
    for name in ["Schema.v", "Queries.v", "Witness.v", "Goal.v"] {
        std::fs::write(proof.join(name), format!("(* {name} *)\n"))
            .expect("write trusted test input");
    }
    let checker = root.join("fake-trusted-checker.sh");
    complete_broker_witness_fixture(&proof);
    let passing_pattern = (diagnostic_count..=diagnostic_count)
        .map(|sequence| format!("checkpoint_{sequence}"))
        .collect::<Vec<_>>()
        .join("|");
    std::fs::write(
        &checker,
        format!(
            "#!/usr/bin/env bash\nif grep -Eq '{passing_pattern}' \"$LOGOS_PROOF_WORKDIR/Problem.v\"; then exit 0; fi\nexit 1\n"
        ),
    )
    .expect("write fake trusted checker");

    let broker = DiagnosticBroker::start(
        &artifacts,
        4,
        1,
        &checker,
        &proof,
        &repo,
        None,
        None,
        2 * 1024 * 1024 * 1024,
        Instant::now() + Duration::from_secs(30),
    )
    .expect("start diagnostic broker");
    let broker_nonce = broker.nonce().to_owned();
    let socket = broker.socket_path().to_owned();

    let rejected = send_diagnostic_broker_request(
        &socket,
        &stage,
        serde_json::json!({
            "schemaVersion": 2,
            "nonce": broker_nonce,
            "mode": "problem",
            "candidatePath": "Problem.v",
            "purpose": "assembly",
            "candidateSha256": "0".repeat(64),
            "requestedTimeoutSeconds": 5,
            "extra": true
        }),
    );
    assert_eq!(rejected["problemCompilePassed"], false);
    assert!(
        rejected["error"]
            .as_str()
            .unwrap()
            .contains("unknown field")
    );

    let mut latest_problem = Vec::new();
    let mut latest_sha256 = String::new();
    for sequence in 1..=diagnostic_count {
        latest_problem = format!("Definition checkpoint_{sequence} : True := I.\n").into_bytes();
        latest_sha256 = sha256_hex(&latest_problem);
        std::fs::write(stage.join("Problem.v"), &latest_problem).expect("write staged Problem.v");
        let response = send_diagnostic_broker_request(
            &socket,
            &stage,
            serde_json::json!({
                "schemaVersion": 2,
                "nonce": broker_nonce,
                "mode": "problem",
                "candidatePath": "Problem.v",
                "purpose": "assembly",
                "candidateSha256": latest_sha256,
                "requestedTimeoutSeconds": 5
            }),
        );
        assert_eq!(
            response["problemCompilePassed"],
            sequence == diagnostic_count,
            "unexpected broker response: {response:?}"
        );
        assert_eq!(
            response["sequence"], sequence,
            "unexpected broker response: {response:?}"
        );
    }

    let outcome = broker.finish().expect("finish diagnostic broker");
    assert_eq!(outcome.requests_seen, diagnostic_count + 1);
    assert_eq!(
        outcome.requested_timeout_seconds_reserved,
        diagnostic_count as u64 * 5
    );
    assert_eq!(outcome.accepted_count, diagnostic_count);
    assert_eq!(outcome.rejected_source_audit_count, 0);
    assert_eq!(outcome.other_rejected_request_count, 1);
    assert_eq!(outcome.invocations.len(), diagnostic_count);
    assert_eq!(outcome.accepted_source_audits.len(), diagnostic_count);
    assert!(outcome.rejected_source_audits.is_empty());
    assert_eq!(outcome.accepted_source_audits[0].request_ordinal, 2);
    assert_eq!(
        outcome.accepted_source_audits[diagnostic_count - 1].request_ordinal,
        diagnostic_count + 1
    );
    let checkpoint = outcome.latest_checkpoint.expect("latest checkpoint");
    assert_eq!(
        std::fs::read(&checkpoint.path).expect("read latest checkpoint"),
        latest_problem
    );
    assert_eq!(checkpoint.sha256, latest_sha256);
    assert_eq!(checkpoint.round, 4);
    assert_eq!(checkpoint.sequence, diagnostic_count);
    std::fs::remove_dir_all(root).expect("remove broker test tree");
}

#[test]
#[ignore = "requires Unix socket creation, unavailable in restricted test sandboxes"]
fn module_promotion_rolls_back_failure_and_replaces_only_unchecked_orphans() {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after Unix epoch")
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "logos-module-promotion-transaction-{}-{nonce}",
        std::process::id()
    ));
    let stage = root.join("stage");
    let artifacts = root.join("artifacts");
    let proof = root.join("proof");
    let repo = root.join("repo");
    let checker =
        artifacts.join("proof-stage/proof-agent/trusted-launcher/fake-trusted-checker.sh");
    let cache_modules =
        artifacts.join("proof-stage/proof-agent/trusted-diagnostic-cache/ProofModules");
    for directory in [
        stage.join("ProofModules"),
        proof.join("ProofModules"),
        repo.clone(),
        checker.parent().expect("checker parent").to_owned(),
        cache_modules.clone(),
    ] {
        std::fs::create_dir_all(directory).expect("create module transaction fixture");
    }
    for name in ["Schema.v", "Queries.v", "Witness.v", "Goal.v", "Problem.v"] {
        std::fs::write(proof.join(name), format!("(* {name} *)\n"))
            .expect("write trusted module transaction input");
    }
    std::fs::write(cache_modules.join("ORDER"), "").expect("write empty module order");
    complete_broker_witness_fixture(&proof);
    std::fs::write(
        cache_modules
            .parent()
            .expect("cache root")
            .join("SHA256SUMS"),
        format!("{}  ProofModules/ORDER\n", sha256_hex(b"")),
    )
    .expect("write empty cache manifest");
    std::fs::write(&checker, "#!/usr/bin/env bash\nexit 1\n")
        .expect("write failing module checker");
    let candidate = b"Lemma promoted_fact : True. Proof. exact I. Qed.\n";
    let candidate_path = stage.join("ProofModules/CoreFacts.v");
    std::fs::write(&candidate_path, candidate).expect("write module candidate");
    std::fs::write(
        proof.join("ProofModules/CoreFacts.v"),
        "Lemma never_checked_old_revision : True. Proof. exact I. Qed.\n",
    )
    .expect("write interrupted unchecked orphan");

    let broker = DiagnosticBroker::start(
        &artifacts,
        5,
        1,
        &checker,
        &proof,
        &repo,
        None,
        None,
        2 * 1024 * 1024 * 1024,
        Instant::now() + Duration::from_secs(30),
    )
    .expect("start module transaction broker");
    let request = serde_json::json!({
        "schemaVersion": 2,
        "nonce": broker.nonce(),
        "mode": "module",
        "candidatePath": "ProofModules/CoreFacts.v",
        "purpose": "static-obligation",
        "candidateSha256": sha256_hex(candidate),
        "requestedTimeoutSeconds": 5
    });
    let failed = send_diagnostic_broker_request(broker.socket_path(), &stage, request.clone());
    assert_eq!(failed["compilePassed"], false);
    assert!(
        !proof.join("ProofModules/CoreFacts.v").exists(),
        "failed promotion must remove both its pending source and an older unchecked orphan"
    );
    assert_eq!(
        std::fs::read_to_string(cache_modules.join("ORDER")).expect("read failed order"),
        ""
    );

    std::fs::write(
        &checker,
        "#!/usr/bin/env bash\nset -euo pipefail\nif [[ ${1:-} == --interactive-diagnostic ]]; then exit 64; fi\ncp \"$LOGOS_PROOF_WORKDIR/ProofModules/CoreFacts.v\" \"$LOGOS_TRUSTED_ROCQ_CACHE_DIR/ProofModules/CoreFacts.v\"\nprintf 'host compiler object\\n' >\"$LOGOS_TRUSTED_ROCQ_CACHE_DIR/ProofModules/CoreFacts.vo\"\nprintf 'CoreFacts.v\\n' >\"$LOGOS_TRUSTED_ROCQ_CACHE_DIR/ProofModules/ORDER\"\ncd \"$LOGOS_TRUSTED_ROCQ_CACHE_DIR\"\nsha256sum ProofModules/ORDER ProofModules/CoreFacts.v ProofModules/CoreFacts.vo >SHA256SUMS\n",
    )
    .expect("write successful module checker");
    let passed = send_diagnostic_broker_request(broker.socket_path(), &stage, request);
    assert_eq!(passed["compilePassed"], true);
    assert_eq!(passed["problemCompilePassed"], false);
    assert_eq!(
        std::fs::read(proof.join("ProofModules/CoreFacts.v"))
            .expect("read promoted workspace source"),
        candidate
    );
    assert_eq!(
        std::fs::read(cache_modules.join("CoreFacts.v")).expect("read promoted cache source"),
        candidate
    );

    let cache_root = cache_modules.parent().expect("cache root").to_owned();
    let gap_old = cache_root
        .parent()
        .expect("cache parent")
        .join(".logos-trusted-diagnostic-cache-old.current-gap");
    let gap_stage = cache_root
        .parent()
        .expect("cache parent")
        .join(".logos-trusted-diagnostic-cache.current-gap");
    let gap_candidate = b"Lemma gap_fact : True. Proof. exact I. Qed.\n";
    std::fs::write(stage.join("ProofModules/GapFacts.v"), gap_candidate)
        .expect("write current-gap candidate");
    std::fs::write(
        &checker,
        format!(
            "#!/usr/bin/env bash\nset -euo pipefail\nif [[ ${{1:-}} == --interactive-diagnostic ]]; then exit 64; fi\nmv -T \"$LOGOS_TRUSTED_ROCQ_CACHE_DIR\" \"{}\"\nmkdir \"{}\"\nexit 137\n",
            gap_old.display(),
            gap_stage.display()
        ),
    )
    .expect("write current-invocation gap checker");
    let gap = send_diagnostic_broker_request(
        broker.socket_path(),
        &stage,
        serde_json::json!({
            "schemaVersion": 2,
            "nonce": broker.nonce(),
            "mode": "module",
            "candidatePath": "ProofModules/GapFacts.v",
            "purpose": "static-obligation",
            "candidateSha256": sha256_hex(gap_candidate),
            "requestedTimeoutSeconds": 5
        }),
    );
    assert_eq!(gap["compilePassed"], false);
    assert!(!proof.join("ProofModules/GapFacts.v").exists());
    assert!(cache_root.is_dir());
    assert!(!gap_old.exists());
    assert!(!gap_stage.exists());

    let interrupted_old = cache_root
        .parent()
        .expect("cache parent")
        .join(".logos-trusted-diagnostic-cache-old.hard-exit");
    let interrupted_stage = cache_root
        .parent()
        .expect("cache parent")
        .join(".logos-trusted-diagnostic-cache.unpublished");
    std::fs::rename(&cache_root, &interrupted_old)
        .expect("simulate hard exit after moving live cache aside");
    std::fs::create_dir(&interrupted_stage).expect("simulate unpublished cache stage");

    let late_candidate = b"Lemma late_fact : True. Proof. exact I. Qed.\n";
    std::fs::write(stage.join("ProofModules/LateFacts.v"), late_candidate)
        .expect("write late-signal module candidate");
    std::fs::write(
        &checker,
        "#!/usr/bin/env bash\nset -euo pipefail\nif [[ ${1:-} == --interactive-diagnostic ]]; then exit 64; fi\ncp \"$LOGOS_PROOF_WORKDIR/ProofModules/LateFacts.v\" \"$LOGOS_TRUSTED_ROCQ_CACHE_DIR/ProofModules/LateFacts.v\"\nprintf 'host compiler object\\n' >\"$LOGOS_TRUSTED_ROCQ_CACHE_DIR/ProofModules/LateFacts.vo\"\nprintf 'LateFacts.v\\n' >>\"$LOGOS_TRUSTED_ROCQ_CACHE_DIR/ProofModules/ORDER\"\ncd \"$LOGOS_TRUSTED_ROCQ_CACHE_DIR\"\nsha256sum ProofModules/ORDER ProofModules/CoreFacts.v ProofModules/CoreFacts.vo ProofModules/LateFacts.v ProofModules/LateFacts.vo >SHA256SUMS\nexit 143\n",
    )
    .expect("write post-publication signal checker");
    let late = send_diagnostic_broker_request(
        broker.socket_path(),
        &stage,
        serde_json::json!({
            "schemaVersion": 2,
            "nonce": broker.nonce(),
            "mode": "module",
            "candidatePath": "ProofModules/LateFacts.v",
            "purpose": "static-obligation",
            "candidateSha256": sha256_hex(late_candidate),
            "requestedTimeoutSeconds": 5
        }),
    );
    assert_eq!(late["compilePassed"], true);
    assert_eq!(late["error"], serde_json::Value::Null);
    assert_eq!(
        std::fs::read(proof.join("ProofModules/LateFacts.v"))
            .expect("read source retained after late signal"),
        late_candidate
    );
    assert!(!interrupted_old.exists());
    assert!(!interrupted_stage.exists());

    let unpublished_candidate = b"Lemma unpublished_fact : True. Proof. exact I. Qed.\n";
    std::fs::write(
        stage.join("ProofModules/UnpublishedFacts.v"),
        unpublished_candidate,
    )
    .expect("write unpublished-success candidate");
    std::fs::write(&checker, "#!/usr/bin/env bash\nexit 0\n")
        .expect("write false-success module checker");
    let unpublished = send_diagnostic_broker_request(
        broker.socket_path(),
        &stage,
        serde_json::json!({
            "schemaVersion": 2,
            "nonce": broker.nonce(),
            "mode": "module",
            "candidatePath": "ProofModules/UnpublishedFacts.v",
            "purpose": "static-obligation",
            "candidateSha256": sha256_hex(unpublished_candidate),
            "requestedTimeoutSeconds": 5
        }),
    );
    assert_eq!(unpublished["compilePassed"], false);
    assert!(
        unpublished["error"]
            .as_str()
            .expect("false-success publication error")
            .contains("without publishing the exact manifest-bound source/object pair")
    );
    assert!(!proof.join("ProofModules/UnpublishedFacts.v").exists());
    assert!(!cache_modules.join("UnpublishedFacts.v").exists());

    let outcome = broker.finish().expect("finish module transaction broker");
    assert_eq!(outcome.invocations.len(), 5);
    assert_eq!(outcome.invocations[0].compile_passed, Some(false));
    assert_eq!(outcome.invocations[1].compile_passed, Some(true));
    assert_eq!(outcome.invocations[2].compile_passed, Some(false));
    assert_eq!(outcome.invocations[3].compile_passed, Some(true));
    assert_eq!(outcome.invocations[4].compile_passed, Some(false));
    assert!(
        outcome
            .trusted_environment_error
            .as_deref()
            .expect("false-success disables broker")
            .contains("without publishing the exact manifest-bound source/object pair")
    );
    assert_eq!(outcome.other_rejected_request_count, 0);
    std::fs::remove_dir_all(root).expect("remove module transaction fixture");
}

#[test]
fn active_problem_checkpoint_remains_compile_authority_without_a_duplicate_diagnostic() {
    let candidate = "a".repeat(64);
    let other = "b".repeat(64);

    assert!(super::candidate_problem_has_compile_authority(
        &candidate,
        &candidate,
        &[],
    ));
    assert!(!super::candidate_problem_has_compile_authority(
        &candidate,
        &other,
        &[],
    ));
}

#[test]
fn trusted_final_check_feedback_is_bounded_and_preserves_both_stream_tails() {
    assert!(super::trusted_final_check_repair_feedback(b"", b"").is_none());

    let mut stdout = vec![b'x'; super::TRUSTED_CHECK_REPAIR_FEEDBACK_STREAM_MAX_BYTES + 257];
    stdout.extend_from_slice(b"STDOUT-REPAIR-MARKER");
    let mut stderr = vec![b'y'; super::TRUSTED_CHECK_REPAIR_FEEDBACK_STREAM_MAX_BYTES + 513];
    stderr.extend_from_slice(b"STDERR-REPAIR-MARKER");
    let feedback = super::trusted_final_check_repair_feedback(&stdout, &stderr)
        .expect("nonempty trusted-check streams produce repair feedback");

    assert!(feedback.contains("trusted final Rocq check stdout tail"));
    assert!(feedback.contains("trusted final Rocq check stderr tail"));
    assert!(feedback.contains("STDOUT-REPAIR-MARKER"));
    assert!(feedback.contains("STDERR-REPAIR-MARKER"));
    assert!(!feedback.contains(&"x".repeat(super::TRUSTED_CHECK_REPAIR_FEEDBACK_STREAM_MAX_BYTES)));
    assert!(!feedback.contains(&"y".repeat(super::TRUSTED_CHECK_REPAIR_FEEDBACK_STREAM_MAX_BYTES)));
    assert!(feedback.len() < 2 * super::TRUSTED_CHECK_REPAIR_FEEDBACK_STREAM_MAX_BYTES + 512);
}

#[test]
#[ignore = "requires Unix socket creation, unavailable in restricted test sandboxes"]
fn diagnostic_broker_does_not_recompile_or_advance_unchanged_problem_checkpoints() {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after Unix epoch")
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "logos-diagnostic-checkpoint-dedup-test-{}-{nonce}",
        std::process::id()
    ));
    let stage = root.join("stage");
    let artifacts = root.join("artifacts");
    let proof = root.join("proof");
    let repo = root.join("repo");
    for directory in [&stage, &artifacts, &proof, &repo] {
        std::fs::create_dir_all(directory).expect("create checkpoint-dedup test directory");
    }
    for name in ["Schema.v", "Queries.v", "Witness.v", "Goal.v"] {
        std::fs::write(proof.join(name), format!("(* {name} *)\n"))
            .expect("write trusted test input");
    }
    let checker = root.join("counting-checker.sh");
    complete_broker_witness_fixture(&proof);
    let checker_marker = root.join("counting-checker.sh.invoked");
    std::fs::write(
        &checker,
        "#!/usr/bin/env bash\nprintf 'invoked\\n' >>\"$0.invoked\"\nexit 0\n",
    )
    .expect("write counting checker");
    let active = b"Definition active_checkpoint : True := I.\n";
    let active_sha256 = sha256_hex(active);
    let broker = DiagnosticBroker::start(
        &artifacts,
        8,
        1,
        &checker,
        &proof,
        &repo,
        None,
        Some(&active_sha256),
        2 * 1024 * 1024 * 1024,
        Instant::now() + Duration::from_secs(30),
    )
    .expect("start checkpoint-dedup broker");
    let socket = broker.socket_path().to_owned();

    std::fs::write(stage.join("Problem.v"), active).expect("write active Problem.v");
    let unchanged = send_diagnostic_broker_request(
        &socket,
        &stage,
        serde_json::json!({
            "schemaVersion": 2,
            "nonce": broker.nonce(),
            "mode": "problem",
            "candidatePath": "Problem.v",
            "purpose": "assembly",
            "candidateSha256": active_sha256,
            "requestedTimeoutSeconds": 5
        }),
    );
    assert_eq!(unchanged["sequence"], serde_json::Value::Null);
    assert!(
        unchanged["error"]
            .as_str()
            .unwrap()
            .contains("already the active compile-clean checkpoint")
    );
    assert!(!checker_marker.exists());

    let changed = b"Definition changed_checkpoint : True := I.\n";
    let changed_sha256 = sha256_hex(changed);
    std::fs::write(stage.join("Problem.v"), changed).expect("write changed Problem.v");
    let passed = send_diagnostic_broker_request(
        &socket,
        &stage,
        serde_json::json!({
            "schemaVersion": 2,
            "nonce": broker.nonce(),
            "mode": "problem",
            "candidatePath": "Problem.v",
            "purpose": "assembly",
            "candidateSha256": changed_sha256,
            "requestedTimeoutSeconds": 5
        }),
    );
    assert_eq!(passed["sequence"], 1);
    assert_eq!(passed["compilePassed"], true);
    assert_eq!(passed["compileCheckpointAdvanced"], true);

    let duplicate = send_diagnostic_broker_request(
        &socket,
        &stage,
        serde_json::json!({
            "schemaVersion": 2,
            "nonce": broker.nonce(),
            "mode": "problem",
            "candidatePath": "Problem.v",
            "purpose": "assembly",
            "candidateSha256": changed_sha256,
            "requestedTimeoutSeconds": 5
        }),
    );
    assert_eq!(duplicate["sequence"], serde_json::Value::Null);
    assert!(
        duplicate["error"]
            .as_str()
            .unwrap()
            .contains("already the active compile-clean checkpoint")
    );

    let invocations =
        std::fs::read_to_string(&checker_marker).expect("read counting-checker invocations");
    assert_eq!(invocations.lines().count(), 1);
    let outcome = broker.finish().expect("finish checkpoint-dedup broker");
    assert_eq!(outcome.requests_seen, 3);
    assert_eq!(outcome.accepted_count, 1);
    assert_eq!(outcome.other_rejected_request_count, 2);
    assert_eq!(outcome.requested_timeout_seconds_reserved, 5);
    assert_eq!(outcome.invocations.len(), 1);
    assert_eq!(
        outcome
            .latest_checkpoint
            .expect("changed checkpoint")
            .sha256,
        changed_sha256
    );
    std::fs::remove_dir_all(root).expect("remove checkpoint-dedup test tree");
}

#[test]
fn empty_scratch_hydration_materializes_launcher_and_persistence_directories() {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after Unix epoch")
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "logos-empty-scratch-test-{}-{nonce}",
        std::process::id()
    ));
    let stage = root.join("stage");
    let proof = root.join("proof");
    std::fs::create_dir_all(&stage).expect("create empty scratch stage");
    std::fs::create_dir_all(&proof).expect("create empty proof workspace");

    let hydrated = super::workspace::hydrate_round_scratch(&proof, &stage)
        .expect("hydrate an empty scratch workspace");
    assert_eq!(hydrated.file_count, 0);
    assert_eq!(hydrated.total_bytes, 0);
    let stage_metadata = std::fs::symlink_metadata(stage.join("scratch"))
        .expect("inspect materialized stage scratch directory");
    assert!(stage_metadata.file_type().is_dir());
    assert!(!stage_metadata.file_type().is_symlink());
    assert_eq!(stage_metadata.permissions().mode() & 0o777, 0o700);

    let persisted = super::workspace::persist_round_scratch(&stage, &proof)
        .expect("persist an empty scratch workspace");
    assert_eq!(persisted.file_count, 0);
    let proof_metadata = std::fs::symlink_metadata(proof.join("scratch"))
        .expect("inspect materialized persistent scratch directory");
    assert!(proof_metadata.file_type().is_dir());
    assert!(!proof_metadata.file_type().is_symlink());
    assert_eq!(proof_metadata.permissions().mode() & 0o777, 0o700);
    std::fs::remove_dir_all(root).expect("remove empty scratch test tree");
}

#[test]
fn unpublished_module_named_drafts_survive_rounds_without_becoming_dependencies() {
    let fixture = tempfile::tempdir().unwrap();
    let stage = fixture.path().join("stage");
    let proof = fixture.path().join("proof");
    let resumed = fixture.path().join("resumed");
    let draft = "scratch/ProofModules/CoreBridge.v";
    std::fs::create_dir_all(stage.join("scratch/ProofModules")).unwrap();
    std::fs::create_dir_all(&proof).unwrap();
    std::fs::create_dir_all(&resumed).unwrap();
    let unfinished = "Lemma bridge : True. Proof. exact 0.\n";
    std::fs::write(stage.join(draft), unfinished).unwrap();
    super::workspace::persist_round_scratch(&stage, &proof).unwrap();
    super::workspace::hydrate_round_scratch(&proof, &resumed).unwrap();
    assert_eq!(
        std::fs::read_to_string(resumed.join(draft)).unwrap(),
        unfinished
    );
    for workspace in [&proof, &resumed] {
        assert!(!workspace.join("ProofModules/CoreBridge.v").exists());
        assert!(
            !workspace
                .join("scratch/checked/ProofModules/CoreBridge.v")
                .exists()
        );
    }
}

#[test]
fn scratch_round_drops_unsupported_regular_files_without_failing() {
    let fixture = tempfile::tempdir().expect("create unsupported-scratch fixture");
    let stage = fixture.path().join("stage");
    let proof = fixture.path().join("proof");
    std::fs::create_dir_all(stage.join("scratch/nested"))
        .expect("create unsupported-scratch stage");
    std::fs::create_dir_all(&proof).expect("create unsupported-scratch proof root");
    std::fs::write(
        stage.join("scratch/keep.v"),
        b"Lemma keep : True. Proof. exact I. Qed.\n",
    )
    .expect("write retained scratch source");
    std::fs::write(stage.join("scratch/notes.json"), b"{\"temporary\":true}\n")
        .expect("write dropped JSON note");
    std::fs::write(
        stage.join("scratch/nested/check.log"),
        b"temporary output\n",
    )
    .expect("write dropped diagnostic log");
    std::fs::write(stage.join("scratch/compiler.vo"), [0_u8, 255, 1, 2])
        .expect("write dropped binary compiler artifact");

    let staged = super::workspace::validated_scratch_tree_with_policy(
        &stage.join("scratch"),
        super::workspace::UnsupportedScratchFilePolicy::Drop,
    )
    .expect("classify structurally safe staged scratch files");
    assert_eq!(staged.files.len(), 1);
    assert_eq!(
        staged.dropped_unsupported_files,
        vec![
            PathBuf::from("compiler.vo"),
            PathBuf::from("nested/check.log"),
            PathBuf::from("notes.json"),
        ]
    );

    let persisted = super::workspace::persist_round_scratch(&stage, &proof)
        .expect("drop unsupported scratch files without failing the round");
    assert_eq!(persisted.file_count, 1);
    assert!(proof.join("scratch/keep.v").is_file());
    assert!(!proof.join("scratch/notes.json").exists());
    assert!(!proof.join("scratch/nested/check.log").exists());
    assert!(!proof.join("scratch/compiler.vo").exists());
}

#[test]
fn scratch_round_still_rejects_symlinks() {
    let fixture = tempfile::tempdir().expect("create scratch-symlink fixture");
    let stage = fixture.path().join("stage");
    let proof = fixture.path().join("proof");
    std::fs::create_dir_all(stage.join("scratch")).expect("create scratch-symlink stage");
    std::fs::create_dir_all(&proof).expect("create scratch-symlink proof root");
    let outside = fixture.path().join("outside.txt");
    std::fs::write(&outside, b"outside\n").expect("write scratch-symlink target");
    symlink(&outside, stage.join("scratch/link.json"))
        .expect("create unsupported-extension scratch symlink");

    let error = super::workspace::persist_round_scratch(&stage, &proof)
        .expect_err("scratch symlinks must remain fatal");
    assert!(
        error
            .to_string()
            .contains("scratch tree contains a symlink")
    );
}

#[test]
fn agent_output_handoff_prefers_protected_stage_and_retains_legacy_fallback() {
    let fixture = tempfile::tempdir().expect("create agent-output fixture");
    let stage = fixture.path().join("stage");
    let artifacts = fixture.path().join("artifacts");
    std::fs::create_dir_all(&stage).expect("create agent-output stage");

    let staged_bytes = b"staged-jsonl\n";
    std::fs::write(stage.join("agent-stdout"), staged_bytes)
        .expect("write protected staged output");
    let staged_destination = artifacts.join("stdout.txt");
    super::materialize_agent_output_file(
        &stage,
        "agent-stdout",
        &staged_destination,
        b"launcher-fallback-must-not-be-appended\n",
    )
    .expect("materialize staged output");
    assert_eq!(
        std::fs::read(&staged_destination).expect("read staged output"),
        staged_bytes
    );
    assert_eq!(
        std::fs::metadata(&staged_destination)
            .expect("inspect staged output")
            .permissions()
            .mode()
            & 0o777,
        0o600
    );

    std::fs::remove_file(stage.join("agent-stdout"))
        .expect("remove staged output for legacy fallback");
    let legacy_bytes = b"legacy-launcher-jsonl\n";
    let legacy_destination = artifacts.join("legacy-stdout.txt");
    super::materialize_agent_output_file(&stage, "agent-stdout", &legacy_destination, legacy_bytes)
        .expect("materialize legacy launcher output");
    assert_eq!(
        std::fs::read(&legacy_destination).expect("read legacy output"),
        legacy_bytes
    );

    std::fs::write(stage.join("agent-stdout"), b"").expect("write empty protected staged output");
    let empty_stage_destination = artifacts.join("empty-stage-stdout.txt");
    super::materialize_agent_output_file(
        &stage,
        "agent-stdout",
        &empty_stage_destination,
        b"launcher-fallback-must-not-replace-an-empty-stage\n",
    )
    .expect("materialize empty staged output");
    assert_eq!(
        std::fs::read(&empty_stage_destination).expect("read empty staged output"),
        b""
    );
    std::fs::remove_file(stage.join("agent-stdout"))
        .expect("remove empty staged output before symlink check");

    let outside = fixture.path().join("outside-output");
    std::fs::write(&outside, b"outside\n").expect("write symlink target");
    symlink(&outside, stage.join("agent-stdout")).expect("create staged-output symlink");
    assert!(
        super::materialize_agent_output_file(
            &stage,
            "agent-stdout",
            &artifacts.join("rejected.txt"),
            legacy_bytes,
        )
        .is_err()
    );
    assert_eq!(
        std::fs::read(&outside).expect("read unchanged symlink target"),
        b"outside\n"
    );
}

#[test]
fn scratch_checked_promotion_avoids_round_merge_capacity_race() {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after Unix epoch")
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "logos-scratch-promotion-capacity-test-{}-{nonce}",
        std::process::id()
    ));
    let stage = root.join("stage");
    let proof = root.join("proof");
    let persistent_scratch = proof.join("scratch");
    std::fs::create_dir_all(&stage).expect("create scratch promotion stage");
    std::fs::create_dir_all(&persistent_scratch)
        .expect("create scratch promotion persistence root");
    for index in 0..62 {
        std::fs::write(persistent_scratch.join(format!("slot-{index}.txt")), b"x")
            .expect("write scratch capacity filler");
    }
    let core = b"Lemma core_checked : True. Proof. exact I. Qed.\n";
    let fresh = b"Lemma fresh_checked : True. Proof. exact I. Qed.\n";
    std::fs::write(persistent_scratch.join("core.v"), core)
        .expect("write persistent untrusted core");

    let hydrated = super::workspace::hydrate_round_scratch(&proof, &stage)
        .expect("hydrate the 63-file scratch state");
    assert_eq!(hydrated.file_count, 63);
    std::fs::write(stage.join("scratch/fresh.v"), fresh)
        .expect("write the round-local fresh candidate");

    let core_state = super::workspace::persist_successful_scratch_candidate(
        &proof,
        Path::new("scratch/core.v"),
        core,
    )
    .expect("promote the matching persistent core");
    assert_eq!(core_state.file_count, 63);
    assert!(!persistent_scratch.join("core.v").exists());
    assert_eq!(
        std::fs::read(persistent_scratch.join("checked/core.v"))
            .expect("read promoted checked core"),
        core
    );

    let fresh_state = super::workspace::persist_successful_scratch_candidate(
        &proof,
        Path::new("scratch/fresh.v"),
        fresh,
    )
    .expect("persist the newly checked round-local candidate");
    assert_eq!(fresh_state.file_count, 64);
    assert_eq!(
        std::fs::read(persistent_scratch.join("checked/fresh.v"))
            .expect("read checked fresh candidate"),
        fresh
    );

    let persisted = super::workspace::persist_round_scratch(&stage, &proof)
        .expect("suppress exact raw duplicates at the capacity boundary");
    assert_eq!(persisted.file_count, 64);
    assert!(!persistent_scratch.join("core.v").exists());
    assert!(!persistent_scratch.join("fresh.v").exists());
    assert_eq!(
        std::fs::read(persistent_scratch.join("checked/core.v"))
            .expect("read retained checked core"),
        core
    );
    assert_eq!(
        std::fs::read(persistent_scratch.join("checked/fresh.v"))
            .expect("read retained checked fresh candidate"),
        fresh
    );
    for index in 0..62 {
        assert!(
            persistent_scratch
                .join(format!("slot-{index}.txt"))
                .is_file()
        );
    }
    std::fs::remove_dir_all(root).expect("remove scratch promotion test tree");
}

#[test]
fn scratch_retains_divergent_wip_without_a_file_count_limit() {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after Unix epoch")
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "logos-scratch-file-pressure-test-{}-{nonce}",
        std::process::id()
    ));
    let stage = root.join("stage");
    let proof = root.join("proof");
    let persistent_scratch = proof.join("scratch");
    std::fs::create_dir_all(&stage).expect("create file-pressure stage");
    std::fs::create_dir_all(&persistent_scratch).expect("create file-pressure persistence root");
    for index in 0..61 {
        std::fs::write(persistent_scratch.join(format!("slot-{index}.txt")), b"x")
            .expect("write file-pressure filler");
    }
    let core = b"Lemma file_pressure_core : True. Proof. exact I. Qed.\n";
    let divergent = b"Lemma file_pressure_core : True. Proof. exact I. Qed. (* later WIP *)\n";
    let stale = b"Lemma file_pressure_stale : True. Proof. exact I. Qed.\n";
    let fresh = b"Lemma file_pressure_fresh : True. Proof. exact I. Qed.\n";
    std::fs::write(persistent_scratch.join("core.v"), core).expect("write file-pressure core");
    std::fs::write(persistent_scratch.join("stale.v"), stale)
        .expect("write file-pressure stale work");

    let hydrated = super::workspace::hydrate_round_scratch(&proof, &stage)
        .expect("hydrate the 63-file pressure state");
    assert_eq!(hydrated.file_count, 63);
    std::fs::write(stage.join("scratch/fresh.v"), fresh)
        .expect("write file-pressure fresh candidate");
    super::workspace::persist_successful_scratch_candidate(
        &proof,
        Path::new("scratch/core.v"),
        core,
    )
    .expect("promote the matching file-pressure core");
    let promoted = super::workspace::persist_successful_scratch_candidate(
        &proof,
        Path::new("scratch/fresh.v"),
        fresh,
    )
    .expect("persist the file-pressure fresh candidate");
    assert_eq!(promoted.file_count, 64);
    std::fs::write(stage.join("scratch/core.v"), divergent)
        .expect("write divergent file-pressure WIP");

    let persisted = super::workspace::persist_round_scratch(&stage, &proof)
        .expect("retain divergent WIP without a file-count limit");
    assert_eq!(persisted.file_count, 65);
    assert_eq!(
        std::fs::read(persistent_scratch.join("checked/core.v"))
            .expect("read checked file-pressure core"),
        core
    );
    assert_eq!(
        std::fs::read(persistent_scratch.join("checked/fresh.v"))
            .expect("read checked file-pressure fresh candidate"),
        fresh
    );
    assert_eq!(
        std::fs::read(persistent_scratch.join("core.v"))
            .expect("read retained divergent file-pressure work"),
        divergent
    );
    assert_eq!(
        std::fs::read(persistent_scratch.join("stale.v"))
            .expect("read unpaired file-pressure work"),
        stale
    );
    std::fs::remove_dir_all(root).expect("remove file-pressure test tree");
}

#[test]
fn scratch_retains_divergent_wip_without_a_byte_limit() {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after Unix epoch")
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "logos-scratch-byte-pressure-test-{}-{nonce}",
        std::process::id()
    ));
    let stage = root.join("stage");
    let proof = root.join("proof");
    let persistent_scratch = proof.join("scratch");
    std::fs::create_dir_all(&stage).expect("create byte-pressure stage");
    std::fs::create_dir_all(&persistent_scratch).expect("create byte-pressure persistence root");
    let filler = vec![b'f'; 400 * 1024];
    for index in 0..8 {
        std::fs::write(
            persistent_scratch.join(format!("slot-{index}.txt")),
            &filler,
        )
        .expect("write byte-pressure filler");
    }
    let core = vec![b'c'; 400 * 1024];
    let divergent = vec![b'd'; 400 * 1024];
    let fresh = vec![b'e'; 300 * 1024];
    std::fs::write(persistent_scratch.join("core.v"), &core).expect("write byte-pressure core");

    let hydrated = super::workspace::hydrate_round_scratch(&proof, &stage)
        .expect("hydrate byte-pressure state");
    assert_eq!(hydrated.total_bytes, 9 * 400 * 1024);
    std::fs::write(stage.join("scratch/fresh.v"), &fresh)
        .expect("write byte-pressure fresh candidate");
    super::workspace::persist_successful_scratch_candidate(
        &proof,
        Path::new("scratch/core.v"),
        &core,
    )
    .expect("promote the matching byte-pressure core");
    let promoted = super::workspace::persist_successful_scratch_candidate(
        &proof,
        Path::new("scratch/fresh.v"),
        &fresh,
    )
    .expect("persist the byte-pressure fresh candidate");
    assert_eq!(promoted.total_bytes, (9 * 400 + 300) * 1024);
    std::fs::write(stage.join("scratch/core.v"), &divergent)
        .expect("write divergent byte-pressure WIP");

    let persisted = super::workspace::persist_round_scratch(&stage, &proof)
        .expect("retain divergent WIP without a scratch byte limit");
    assert_eq!(persisted.total_bytes, (10 * 400 + 300) * 1024);
    assert_eq!(
        std::fs::read(persistent_scratch.join("checked/core.v"))
            .expect("read checked byte-pressure core"),
        core
    );
    assert_eq!(
        std::fs::read(persistent_scratch.join("checked/fresh.v"))
            .expect("read checked byte-pressure fresh candidate"),
        fresh
    );
    assert_eq!(
        std::fs::read(persistent_scratch.join("core.v"))
            .expect("read retained divergent byte-pressure work"),
        divergent
    );
    std::fs::remove_dir_all(root).expect("remove byte-pressure test tree");
}

#[test]
fn scratch_round_replacement_drops_deleted_wip_and_stale_directories() {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after Unix epoch")
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "logos-scratch-replacement-test-{}-{nonce}",
        std::process::id()
    ));
    let stage = root.join("stage");
    let proof = root.join("proof");
    let persistent_scratch = proof.join("scratch");
    std::fs::create_dir_all(&stage).expect("create replacement stage");
    std::fs::create_dir_all(persistent_scratch.join("obsolete/deep"))
        .expect("create obsolete persistence directories");
    for index in 0..62 {
        std::fs::write(persistent_scratch.join(format!("slot-{index}.txt")), b"x")
            .expect("write replacement filler");
    }
    let old = b"Lemma old_wip : True. Proof. exact I. Qed.\n";
    let keep = b"Lemma kept_wip : True. Proof. exact I. Qed.\n";
    let replacement = b"Lemma replacement_wip : True. Proof. exact I. Qed.\n";
    std::fs::write(persistent_scratch.join("obsolete/deep/old.v"), old)
        .expect("write obsolete WIP");
    std::fs::write(persistent_scratch.join("keep.v"), keep).expect("write retained WIP");

    let hydrated = super::workspace::hydrate_round_scratch(&proof, &stage)
        .expect("hydrate the full replacement state");
    assert_eq!(hydrated.file_count, 64);
    std::fs::remove_file(stage.join("scratch/obsolete/deep/old.v"))
        .expect("delete obsolete staged WIP");
    std::fs::create_dir_all(stage.join("scratch/replacement"))
        .expect("create replacement stage directory");
    std::fs::write(stage.join("scratch/replacement/current.v"), replacement)
        .expect("write current replacement WIP");

    let persisted = super::workspace::persist_round_scratch(&stage, &proof)
        .expect("replace the staged namespace without a 65-file union");
    assert_eq!(persisted.file_count, 64);
    assert!(!persistent_scratch.join("obsolete/deep/old.v").exists());
    assert!(!persistent_scratch.join("obsolete/deep").exists());
    assert!(!persistent_scratch.join("obsolete").exists());
    assert_eq!(
        std::fs::read(persistent_scratch.join("replacement/current.v"))
            .expect("read replacement WIP"),
        replacement
    );
    assert_eq!(
        std::fs::read(persistent_scratch.join("keep.v")).expect("read retained WIP"),
        keep
    );
    std::fs::remove_dir_all(root).expect("remove replacement test tree");
}

#[test]
fn scratch_transaction_failure_before_exchange_retains_complete_live_tree() {
    let fixture = tempfile::tempdir().expect("create scratch transaction fixture");
    let proof = fixture.path().join("proof");
    let scratch = proof.join("scratch");
    std::fs::create_dir_all(scratch.join("checked")).expect("create live checked scratch tree");
    let old_checked = b"Lemma checked_old : True. Proof. exact I. Qed.\n";
    let old_wip = b"Lemma wip_old : True. Proof. exact I. Qed.\n";
    std::fs::write(scratch.join("checked/core.v"), old_checked)
        .expect("write live checked snapshot");
    std::fs::write(scratch.join("old.v"), old_wip).expect("write live WIP");
    let existing =
        super::workspace::validated_scratch_tree(&scratch).expect("snapshot live scratch");
    let new_checked = b"Lemma checked_new : True. Proof. exact I. Qed.\n";
    let new_wip = b"Lemma wip_new : True. Proof. exact I. Qed.\n";
    let selected = BTreeMap::from([
        (
            PathBuf::from("checked/core.v"),
            super::workspace::ScratchFile {
                relative_path: PathBuf::from("checked/core.v"),
                bytes: new_checked.to_vec(),
            },
        ),
        (
            PathBuf::from("new.v"),
            super::workspace::ScratchFile {
                relative_path: PathBuf::from("new.v"),
                bytes: new_wip.to_vec(),
            },
        ),
    ]);

    let error = super::workspace::replace_scratch_snapshots_with_pre_exchange_hook(
        &scratch,
        existing,
        selected.clone(),
        |_| {
            Err(crate::error::Error::ProofAgentCommand(
                "injected scratch publication failure".to_owned(),
            ))
        },
    )
    .expect_err("injected pre-exchange failure must abort publication");
    assert!(
        error
            .to_string()
            .contains("injected scratch publication failure")
    );
    assert_eq!(
        std::fs::read(scratch.join("checked/core.v")).expect("read retained checked state"),
        old_checked
    );
    assert_eq!(
        std::fs::read(scratch.join("old.v")).expect("read retained WIP"),
        old_wip
    );
    assert!(!scratch.join("new.v").exists());
    assert!(
        std::fs::read_dir(&proof)
            .expect("inspect transaction parent")
            .all(|entry| !entry
                .expect("read transaction-parent entry")
                .file_name()
                .to_string_lossy()
                .starts_with(super::workspace::SCRATCH_TRANSACTION_PREFIX))
    );

    let existing = super::workspace::validated_scratch_tree(&scratch)
        .expect("snapshot retained scratch before retry");
    let published = super::workspace::replace_scratch_snapshots(&scratch, existing, selected)
        .expect("atomically publish complete replacement");
    assert_eq!(published.file_count, 2);
    assert_eq!(
        std::fs::read(scratch.join("checked/core.v")).expect("read new checked state"),
        new_checked
    );
    assert_eq!(
        std::fs::read(scratch.join("new.v")).expect("read new WIP"),
        new_wip
    );
    assert!(!scratch.join("old.v").exists());
}

#[test]
fn scratch_retains_current_wip_without_a_directory_count_limit() {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after Unix epoch")
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "logos-scratch-directory-pressure-test-{}-{nonce}",
        std::process::id()
    ));
    let stage = root.join("stage");
    let proof = root.join("proof");
    let persistent_scratch = proof.join("scratch");
    std::fs::create_dir_all(persistent_scratch.join("checked"))
        .expect("create checked directory-pressure root");
    std::fs::create_dir_all(&stage).expect("create directory-pressure stage");
    let checked = b"Lemma directory_pressure_checked : True. Proof. exact I. Qed.\n";
    std::fs::write(persistent_scratch.join("checked/core.v"), checked)
        .expect("write checked directory-pressure snapshot");

    super::workspace::hydrate_round_scratch(&proof, &stage)
        .expect("hydrate the checked directory-pressure state");
    std::fs::remove_file(stage.join("scratch/checked/core.v"))
        .expect("remove the staged checked snapshot");
    std::fs::remove_dir(stage.join("scratch/checked"))
        .expect("remove the empty staged checked directory");
    for index in 0..63 {
        let directory = stage.join(format!("scratch/wip-{index:02}"));
        std::fs::create_dir(&directory).expect("create staged WIP directory");
        std::fs::write(directory.join("work.v"), format!("(* WIP {index} *)\n"))
            .expect("write staged directory-pressure WIP");
    }
    let staged_tree = super::workspace::validated_scratch_tree(&stage.join("scratch"))
        .expect("validate the structurally sound staged directory tree");
    assert_eq!(staged_tree.directories.len(), 64);

    let persisted = super::workspace::persist_round_scratch(&stage, &proof)
        .expect("retain the checked-plus-staged directory union");
    assert_eq!(persisted.file_count, 64);
    assert_eq!(
        std::fs::read(persistent_scratch.join("checked/core.v"))
            .expect("read preserved checked directory-pressure snapshot"),
        checked
    );
    let persisted_tree = super::workspace::validated_scratch_tree(&persistent_scratch)
        .expect("validate compacted directory-pressure tree");
    assert_eq!(persisted_tree.directories.len(), 65);
    assert_eq!(
        persisted_tree
            .files
            .iter()
            .filter(|snapshot| !super::workspace::is_checked_scratch_snapshot(
                &snapshot.relative_path
            ))
            .count(),
        63
    );
    std::fs::remove_dir_all(root).expect("remove directory-pressure test tree");
}

#[test]
fn scratch_successful_promotion_retains_untrusted_work() {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after Unix epoch")
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "logos-scratch-promotion-pressure-test-{}-{nonce}",
        std::process::id()
    ));
    let proof = root.join("proof");
    let persistent_scratch = proof.join("scratch");
    std::fs::create_dir_all(persistent_scratch.join("checked"))
        .expect("create promotion-pressure checked directory");
    let checked_core = vec![b'c'; 300 * 1024];
    let divergent_core = vec![b'd'; 400 * 1024];
    let filler = vec![b'f'; 400 * 1024];
    let fresh = vec![b'e'; 300 * 1024];
    std::fs::write(persistent_scratch.join("checked/core.v"), &checked_core)
        .expect("write promotion-pressure checked core");
    std::fs::write(persistent_scratch.join("core.v"), &divergent_core)
        .expect("write promotion-pressure divergent core");
    for index in 0..8 {
        std::fs::write(
            persistent_scratch.join(format!("slot-{index}.txt")),
            &filler,
        )
        .expect("write promotion-pressure filler");
    }
    let before = super::workspace::scratch_workspace_state(&persistent_scratch)
        .expect("inspect promotion-pressure initial state");
    assert_eq!(before.total_bytes, (300 + 400 + 8 * 400) * 1024);

    let promoted = super::workspace::persist_successful_scratch_candidate(
        &proof,
        Path::new("scratch/fresh.v"),
        &fresh,
    )
    .expect("retain untrusted state while adding the new checked candidate");
    assert_eq!(promoted.file_count, 11);
    assert_eq!(promoted.total_bytes, (300 + 400 + 300 + 8 * 400) * 1024);
    assert_eq!(
        std::fs::read(persistent_scratch.join("checked/core.v"))
            .expect("read promotion-pressure checked core"),
        checked_core
    );
    assert_eq!(
        std::fs::read(persistent_scratch.join("checked/fresh.v"))
            .expect("read promotion-pressure fresh checked candidate"),
        fresh
    );
    assert_eq!(
        std::fs::read(persistent_scratch.join("core.v"))
            .expect("read retained divergent promotion work"),
        divergent_core
    );
    std::fs::remove_dir_all(root).expect("remove promotion-pressure test tree");
}

#[test]
fn scratch_checked_snapshots_have_no_smaller_byte_envelope() {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after Unix epoch")
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "logos-scratch-checked-saturation-test-{}-{nonce}",
        std::process::id()
    ));
    let proof = root.join("proof");
    let persistent_scratch = proof.join("scratch");
    std::fs::create_dir_all(persistent_scratch.join("checked"))
        .expect("create checked-saturation directory");
    let full_file = vec![b'x'; 512 * 1024];
    for index in 0..8 {
        std::fs::write(
            persistent_scratch.join(format!("checked/slot-{index}.v")),
            &full_file,
        )
        .expect("write checked-saturation snapshot");
    }
    let before = super::workspace::scratch_workspace_state(&persistent_scratch)
        .expect("inspect checked-only saturation");
    assert_eq!(before.total_bytes, 4 * 1024 * 1024);

    let retained = super::workspace::persist_successful_scratch_candidate(
        &proof,
        Path::new("scratch/new.v"),
        b"Lemma uncached_but_checked : True. Proof. exact I. Qed.\n",
    )
    .expect("treat checked-only cache saturation as nonfatal");
    assert_eq!(retained.file_count, before.file_count + 1);
    assert!(retained.total_bytes > before.total_bytes);
    assert!(persistent_scratch.join("checked/new.v").exists());
    for index in 0..8 {
        assert_eq!(
            std::fs::read(persistent_scratch.join(format!("checked/slot-{index}.v")))
                .expect("read retained checked-saturation snapshot"),
            full_file
        );
    }
    std::fs::remove_dir_all(root).expect("remove checked-saturation test tree");
}

#[test]
fn scratch_stage_file_count_has_no_smaller_envelope() {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after Unix epoch")
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "logos-scratch-stage-overflow-test-{}-{nonce}",
        std::process::id()
    ));
    let stage = root.join("stage");
    let proof = root.join("proof");
    let persistent_scratch = proof.join("scratch");
    std::fs::create_dir_all(persistent_scratch.join("checked"))
        .expect("create stage-overflow checked directory");
    std::fs::create_dir_all(&stage).expect("create stage-overflow stage");
    let checked = b"Lemma stage_overflow_checked : True. Proof. exact I. Qed.\n";
    std::fs::write(persistent_scratch.join("checked/core.v"), checked)
        .expect("write stage-overflow checked snapshot");
    super::workspace::hydrate_round_scratch(&proof, &stage)
        .expect("hydrate stage-overflow checked snapshot");
    for index in 0..64 {
        std::fs::write(stage.join(format!("scratch/overflow-{index}.txt")), b"x")
            .expect("write aggregate stage-overflow file");
    }
    assert_eq!(
        super::workspace::validated_scratch_tree(&stage.join("scratch"))
            .expect("validate all staged files")
            .files
            .len(),
        65
    );

    let persisted = super::workspace::persist_round_scratch(&stage, &proof)
        .expect("retain every structurally valid staged file");
    assert_eq!(persisted.file_count, 65);
    assert_eq!(
        std::fs::read(persistent_scratch.join("checked/core.v"))
            .expect("read preserved stage-overflow checked snapshot"),
        checked
    );
    assert!(persistent_scratch.join("overflow-63.txt").is_file());
    std::fs::remove_dir_all(root).expect("remove stage-overflow test tree");
}

#[test]
fn scratch_file_has_no_smaller_per_file_limit() {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after Unix epoch")
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "logos-scratch-per-file-overflow-test-{}-{nonce}",
        std::process::id()
    ));
    let stage = root.join("stage");
    let proof = root.join("proof");
    std::fs::create_dir_all(stage.join("scratch")).expect("create per-file-overflow stage");
    std::fs::create_dir_all(&proof).expect("create per-file-overflow proof root");
    std::fs::write(stage.join("scratch/oversized.txt"), vec![b'x'; 600 * 1024])
        .expect("write oversized scratch file");

    let persisted = super::workspace::persist_round_scratch(&stage, &proof)
        .expect("retain a file larger than the former per-file limit");
    assert_eq!(persisted.total_bytes, 600 * 1024);
    std::fs::remove_dir_all(root).expect("remove per-file-overflow test tree");
}

#[test]
fn scratch_large_tree_retains_every_regular_utf8_file() {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after Unix epoch")
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "logos-scratch-mixed-overflow-test-{}-{nonce}",
        std::process::id()
    ));
    let stage = root.join("stage");
    let proof = root.join("proof");
    std::fs::create_dir_all(stage.join("scratch/unsafe"))
        .expect("create mixed-overflow unsafe subtree");
    std::fs::create_dir_all(&proof).expect("create mixed-overflow proof root");
    for index in 0..65 {
        std::fs::write(stage.join(format!("scratch/overflow-{index}.txt")), b"x")
            .expect("write mixed aggregate-overflow file");
    }
    std::fs::write(
        stage.join("scratch/unsafe/oversized.txt"),
        vec![b'x'; 600 * 1024],
    )
    .expect("write masked oversized scratch file");

    let persisted = super::workspace::persist_round_scratch(&stage, &proof)
        .expect("retain the complete structurally valid tree");
    assert_eq!(persisted.file_count, 66);
    assert!(proof.join("scratch/unsafe/oversized.txt").is_file());
    std::fs::remove_dir_all(root).expect("remove mixed-overflow test tree");
}

#[test]
fn scratch_validation_has_no_smaller_file_scan_ceiling() {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after Unix epoch")
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "logos-scratch-scan-ceiling-test-{}-{nonce}",
        std::process::id()
    ));
    let stage = root.join("stage");
    let proof = root.join("proof");
    std::fs::create_dir_all(stage.join("scratch")).expect("create scan-ceiling scratch stage");
    std::fs::create_dir_all(&proof).expect("create scan-ceiling proof root");
    for index in 0..=128 {
        std::fs::write(stage.join(format!("scratch/scan-{index}.txt")), b"x")
            .expect("write scan-ceiling file");
    }

    let persisted = super::workspace::persist_round_scratch(&stage, &proof)
        .expect("retain files beyond the former validation scan ceiling");
    assert_eq!(persisted.file_count, 129);
    std::fs::remove_dir_all(root).expect("remove scan-ceiling test tree");
}

#[test]
#[ignore = "requires Unix socket creation, unavailable in restricted test sandboxes"]
fn scratch_round_retains_untrusted_v_wip_separately_from_checked_snapshot() {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after Unix epoch")
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "logos-scratch-retention-test-{}-{nonce}",
        std::process::id()
    ));
    let stage = root.join("stage");
    let artifacts = root.join("artifacts");
    let proof = root.join("proof");
    let repo = root.join("repo");
    for directory in [
        &stage,
        &stage.join("scratch"),
        &artifacts,
        &proof,
        &proof.join("scratch"),
        &repo,
    ] {
        std::fs::create_dir_all(directory).expect("create scratch broker directory");
    }
    for name in ["Schema.v", "Queries.v", "Witness.v", "Goal.v"] {
        std::fs::write(proof.join(name), format!("(* {name} *)\n"))
            .expect("write trusted test input");
    }
    let checker = root.join("fake-scratch-checker.sh");
    complete_broker_witness_fixture(&proof);
    std::fs::write(
        &checker,
        "#!/usr/bin/env bash\nif grep -q FAIL \"$LOGOS_PROOF_WORKDIR/Problem.v\"; then exit 1; fi\nexit 0\n",
    )
    .expect("write scratch checker");
    let broker = DiagnosticBroker::start(
        &artifacts,
        5,
        1,
        &checker,
        &proof,
        &repo,
        None,
        None,
        2 * 1024 * 1024 * 1024,
        Instant::now() + Duration::from_secs(30),
    )
    .expect("start scratch broker");
    let socket = broker.socket_path().to_owned();

    let successful = b"Lemma retained_subproof : True. Proof. exact I. Qed.\n";
    let successful_sha256 = sha256_hex(successful);
    std::fs::write(stage.join("scratch/core.v"), successful)
        .expect("write successful scratch candidate");
    let passed = send_diagnostic_broker_request(
        &socket,
        &stage,
        serde_json::json!({
            "schemaVersion": 2,
            "nonce": broker.nonce(),
            "mode": "scratch",
            "candidatePath": "scratch/core.v",
            "purpose": "semantic-equivalence",
            "candidateSha256": successful_sha256,
            "requestedTimeoutSeconds": 5
        }),
    );
    assert_eq!(passed["compilePassed"], true);
    assert_eq!(passed["problemCompilePassed"], false);
    assert_eq!(passed["compileCheckpointAdvanced"], false);
    assert_eq!(
        std::fs::read(proof.join("scratch/checked/core.v"))
            .expect("read retained checked snapshot"),
        successful
    );

    let failing = b"Lemma later_failing_edit : True. Proof. exact I. Qed. (* FAIL *)\n";
    std::fs::write(stage.join("scratch/core.v"), failing)
        .expect("overwrite staged scratch candidate");
    let failed = send_diagnostic_broker_request(
        &socket,
        &stage,
        serde_json::json!({
            "schemaVersion": 2,
            "nonce": broker.nonce(),
            "mode": "scratch",
            "candidatePath": "scratch/core.v",
            "purpose": "semantic-equivalence",
            "candidateSha256": sha256_hex(failing),
            "requestedTimeoutSeconds": 5
        }),
    );
    assert_eq!(failed["compilePassed"], false);
    std::fs::write(
        stage.join("scratch/proof-plan.md"),
        "static\ncore\nlift\nassembly\n",
    )
    .expect("write scratch proof plan");
    std::fs::create_dir_all(stage.join("scratch/checked"))
        .expect("create forged checked namespace");
    std::fs::write(
        stage.join("scratch/checked/agent-note.md"),
        "must not persist in the host-owned namespace\n",
    )
    .expect("write forged checked note");
    let never_submitted = b"Lemma unfinished_subproof : True. Proof. exact I. Qed.\n";
    std::fs::write(stage.join("scratch/never-submitted.v"), never_submitted)
        .expect("write never-submitted scratch WIP");
    let persisted = super::workspace::persist_round_scratch(&stage, &proof)
        .expect("persist planning files and untrusted Rocq work in progress");
    assert_eq!(persisted.file_count, 4);
    assert!(!proof.join("scratch/checked/agent-note.md").exists());
    assert_eq!(
        std::fs::read(proof.join("scratch/core.v")).expect("read retained untrusted WIP"),
        failing
    );
    assert_eq!(
        std::fs::read(proof.join("scratch/checked/core.v"))
            .expect("read retained checked snapshot"),
        successful
    );
    assert_eq!(
        std::fs::read(proof.join("scratch/never-submitted.v"))
            .expect("read never-submitted retained WIP"),
        never_submitted
    );

    let next_stage = root.join("next-stage");
    std::fs::create_dir(&next_stage).expect("create next stage");
    super::workspace::hydrate_round_scratch(&proof, &next_stage).expect("hydrate retained scratch");
    assert_eq!(
        std::fs::read(next_stage.join("scratch/core.v")).expect("read hydrated WIP"),
        failing
    );
    assert_eq!(
        std::fs::read(next_stage.join("scratch/checked/core.v"))
            .expect("read hydrated checked snapshot"),
        successful
    );
    assert_eq!(
        std::fs::read(next_stage.join("scratch/never-submitted.v"))
            .expect("read hydrated never-submitted WIP"),
        never_submitted
    );
    assert!(next_stage.join("scratch/proof-plan.md").is_file());

    let outcome = broker.finish().expect("finish scratch broker");
    assert!(outcome.latest_checkpoint.is_none());
    assert_eq!(outcome.invocations.len(), 2);
    assert_eq!(outcome.invocations[0].mode.as_deref(), Some("scratch"));
    assert_eq!(outcome.invocations[0].compile_passed, Some(true));
    assert_eq!(outcome.invocations[0].problem_compile_passed, Some(false));
    assert_eq!(
        outcome.invocations[0].compile_checkpoint_advanced,
        Some(false)
    );
    assert_eq!(outcome.invocations[1].compile_passed, Some(false));
    std::fs::remove_dir_all(root).expect("remove scratch retention test tree");
}

#[test]
#[ignore = "requires Unix socket creation, unavailable in restricted test sandboxes"]
fn scratch_request_rejects_stale_schema_mode_path_and_checked_namespace() {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after Unix epoch")
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "logos-scratch-request-test-{}-{nonce}",
        std::process::id()
    ));
    let stage = root.join("stage");
    let artifacts = root.join("artifacts");
    let proof = root.join("proof");
    let repo = root.join("repo");
    for directory in [&stage, &stage.join("scratch"), &artifacts, &proof, &repo] {
        std::fs::create_dir_all(directory).expect("create scratch request directory");
    }
    for name in ["Schema.v", "Queries.v", "Witness.v", "Goal.v"] {
        std::fs::write(proof.join(name), format!("(* {name} *)\n"))
            .expect("write trusted test input");
    }
    let checker = root.join("checker-must-not-run.sh");
    complete_broker_witness_fixture(&proof);
    std::fs::write(&checker, "#!/usr/bin/env bash\nexit 99\n").expect("write checker");
    let broker = DiagnosticBroker::start(
        &artifacts,
        6,
        1,
        &checker,
        &proof,
        &repo,
        None,
        None,
        64,
        Instant::now() + Duration::from_secs(30),
    )
    .expect("start scratch request broker");
    let socket = broker.socket_path().to_owned();
    let candidate = b"Lemma safe : True. Proof. exact I. Qed.\n";
    std::fs::write(stage.join("scratch/safe.v"), candidate).expect("write scratch candidate");
    std::fs::create_dir(stage.join("scratch/checked"))
        .expect("create reserved staged checked directory");
    std::fs::write(stage.join("scratch/checked/safe.v"), candidate)
        .expect("write reserved checked candidate");

    for request in [
        serde_json::json!({
            "schemaVersion": 1,
            "nonce": broker.nonce(),
            "mode": "scratch",
            "candidatePath": "scratch/safe.v",
            "purpose": "static-obligation",
            "candidateSha256": sha256_hex(candidate),
            "requestedTimeoutSeconds": 5
        }),
        serde_json::json!({
            "schemaVersion": 2,
            "nonce": broker.nonce(),
            "mode": "problem",
            "candidatePath": "scratch/safe.v",
            "purpose": "assembly",
            "candidateSha256": sha256_hex(candidate),
            "requestedTimeoutSeconds": 5
        }),
        serde_json::json!({
            "schemaVersion": 2,
            "nonce": broker.nonce(),
            "mode": "scratch",
            "candidatePath": "scratch/checked/safe.v",
            "purpose": "static-obligation",
            "candidateSha256": sha256_hex(candidate),
            "requestedTimeoutSeconds": 5
        }),
    ] {
        let response = send_diagnostic_broker_request(&socket, &stage, request);
        assert_eq!(response["compilePassed"], false);
        assert_eq!(response["sequence"], serde_json::Value::Null);
    }

    let oversized = send_diagnostic_broker_request(
        &socket,
        &stage,
        serde_json::json!({
            "schemaVersion": 2,
            "nonce": broker.nonce(),
            "mode": "scratch",
            "candidatePath": "scratch/safe.v",
            "purpose": "static-obligation",
            "candidateSha256": sha256_hex(candidate),
            "candidateBytes": 65,
            "requestedTimeoutSeconds": 5
        }),
    );
    assert_eq!(oversized["compilePassed"], false);
    assert!(
        oversized["error"]
            .as_str()
            .is_some_and(|error| error.contains("aggregate writable-storage quota"))
    );

    let outcome = broker.finish().expect("finish scratch request broker");
    assert!(outcome.invocations.is_empty());
    assert_eq!(outcome.requests_seen, 4);
    std::fs::remove_dir_all(root).expect("remove scratch request test tree");
}

#[test]
#[ignore = "requires Unix socket creation, unavailable in restricted test sandboxes"]
fn diagnostic_broker_audits_each_snapshot_before_starting_the_checker() {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after Unix epoch")
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "logos-diagnostic-audit-test-{}-{nonce}",
        std::process::id()
    ));
    let stage = root.join("stage");
    let artifacts = root.join("artifacts");
    let proof = root.join("proof");
    let repo = root.join("repo");
    std::fs::create_dir_all(&stage).expect("create broker stage");
    std::fs::create_dir_all(&artifacts).expect("create artifact root");
    std::fs::create_dir_all(&proof).expect("create proof workspace");
    std::fs::create_dir_all(&repo).expect("create repository root");
    for name in ["Schema.v", "Queries.v", "Witness.v", "Goal.v"] {
        std::fs::write(proof.join(name), format!("(* {name} *)\n"))
            .expect("write trusted test input");
    }
    let checker = root.join("fake-trusted-checker.sh");
    let checker_marker = root.join("fake-trusted-checker.sh.invoked");
    complete_broker_witness_fixture(&proof);
    std::fs::write(
        &checker,
        "#!/usr/bin/env bash\nprintf invoked >>\"$0.invoked\"\nexit 0\n",
    )
    .expect("write fake trusted checker");

    let broker = DiagnosticBroker::start(
        &artifacts,
        2,
        1,
        &checker,
        &proof,
        &repo,
        None,
        None,
        2 * 1024 * 1024 * 1024,
        Instant::now() + Duration::from_secs(30),
    )
    .expect("start diagnostic broker");
    let broker_nonce = broker.nonce().to_owned();
    let socket = broker.socket_path().to_owned();

    let forbidden_problem = b"Load \"/host-only/retained-proof.v\".\n";
    let forbidden_sha256 = sha256_hex(forbidden_problem);
    std::fs::write(stage.join("Problem.v"), forbidden_problem).expect("write forbidden Problem.v");
    let rejected = send_diagnostic_broker_request(
        &socket,
        &stage,
        serde_json::json!({
            "schemaVersion": 2,
            "nonce": broker_nonce,
            "mode": "problem",
            "candidatePath": "Problem.v",
            "purpose": "assembly",
            "candidateSha256": forbidden_sha256,
            "requestedTimeoutSeconds": 5
        }),
    );
    assert_eq!(rejected["problemCompilePassed"], false);
    assert_eq!(rejected["sequence"], serde_json::Value::Null);
    assert_eq!(rejected["exitCode"], serde_json::Value::Null);
    assert!(
        rejected["error"]
            .as_str()
            .unwrap()
            .contains("audit rejected diagnostic candidate before checker execution")
    );
    assert!(
        !checker_marker.exists(),
        "source-audit rejection must not execute the checker"
    );
    {
        let state = broker.state.lock().expect("lock broker state");
        assert_eq!(state.requests_seen, 1);
        assert!(state.invocations.is_empty());
        assert!(
            state
                .latest_feedback
                .as_deref()
                .is_some_and(|feedback| feedback.contains("checker was not executed"))
        );
    }
    let rejected_dir =
        artifacts.join("proof-stage/proof-agent/rounds/02/rejected-diagnostic-source-audits/01");
    assert_eq!(
        std::fs::read(rejected_dir.join("Problem.v")).expect("read rejected Problem.v"),
        forbidden_problem
    );
    let rejected_request: serde_json::Value = serde_json::from_slice(
        &std::fs::read(rejected_dir.join("request.json")).expect("read rejected request"),
    )
    .expect("parse rejected request");
    assert_eq!(rejected_request["candidateSha256"], forbidden_sha256);
    assert_eq!(rejected_request["requestedTimeoutSeconds"], 5);
    let rejected_audit: serde_json::Value = serde_json::from_slice(
        &std::fs::read(rejected_dir.join("audit.json")).expect("read rejected audit"),
    )
    .expect("parse rejected audit");
    assert_eq!(rejected_audit["passed"], false);
    assert_eq!(rejected_audit["findings"][0]["token"], "Load");
    assert!(
        std::fs::read_to_string(rejected_dir.join("feedback.txt"))
            .expect("read rejected feedback")
            .contains("checker was not executed")
    );
    assert!(
        !artifacts
            .join("proof-stage/proof-agent/rounds/02/interactive-diagnostics/01")
            .exists(),
        "audit-only rejection must not occupy a checker-invocation namespace"
    );

    let allowed_problem = b"Definition broker_audit_allowed : True := I.\n";
    let allowed_sha256 = sha256_hex(allowed_problem);
    std::fs::write(stage.join("Problem.v"), allowed_problem).expect("write allowed Problem.v");
    let accepted = send_diagnostic_broker_request(
        &socket,
        &stage,
        serde_json::json!({
            "schemaVersion": 2,
            "nonce": broker_nonce,
            "mode": "problem",
            "candidatePath": "Problem.v",
            "purpose": "assembly",
            "candidateSha256": allowed_sha256,
            "requestedTimeoutSeconds": 5
        }),
    );
    assert_eq!(accepted["problemCompilePassed"], true);
    assert_eq!(accepted["sequence"], 1);
    assert_eq!(
        std::fs::read_to_string(&checker_marker).expect("read checker marker"),
        "invoked"
    );
    let accepted_audit: serde_json::Value = serde_json::from_slice(
        &std::fs::read(
            artifacts
                .join("proof-stage/proof-agent/rounds/02/interactive-diagnostics/01/audit.json"),
        )
        .expect("read accepted audit"),
    )
    .expect("parse accepted audit");
    assert_eq!(accepted_audit["passed"], true);
    assert_eq!(accepted_audit["findings"], serde_json::json!([]));

    {
        let state = broker.state.lock().expect("lock broker state");
        assert_eq!(state.requests_seen, 2);
        assert_eq!(state.invocations.len(), 1);
    }
    let outcome = broker.finish().expect("finish diagnostic broker");
    assert_eq!(outcome.requests_seen, 2);
    assert_eq!(outcome.requested_timeout_seconds_reserved, 10);
    assert_eq!(outcome.accepted_count, 1);
    assert_eq!(outcome.rejected_source_audit_count, 1);
    assert_eq!(outcome.other_rejected_request_count, 0);
    assert_eq!(outcome.invocations.len(), 1);
    assert_eq!(outcome.invocations[0].problem_compile_passed, Some(true));
    let accepted_record = &outcome.accepted_source_audits[0];
    assert_eq!(accepted_record.request_ordinal, 2);
    assert_eq!(accepted_record.sequence, 1);
    assert_eq!(accepted_record.candidate_sha256, allowed_sha256);
    assert_eq!(accepted_record.requested_timeout_seconds, 5);
    assert!(accepted_record.audit.path.ends_with("/01/audit.json"));
    assert_eq!(
        accepted_record.audit.sha256,
        sha256_hex(
            &std::fs::read(artifacts.join(&accepted_record.audit.path))
                .expect("read accepted bound audit")
        )
    );
    let rejected_record = &outcome.rejected_source_audits[0];
    assert_eq!(rejected_record.request_ordinal, 1);
    assert_eq!(rejected_record.candidate_sha256, forbidden_sha256);
    assert_eq!(rejected_record.requested_timeout_seconds, 5);
    for binding in [
        &rejected_record.problem,
        &rejected_record.request,
        &rejected_record.audit,
        &rejected_record.feedback,
    ] {
        assert!(!Path::new(&binding.path).is_absolute());
        let bytes =
            std::fs::read(artifacts.join(&binding.path)).expect("read rejected bound artifact");
        assert_eq!(binding.bytes, bytes.len());
        assert_eq!(binding.sha256, sha256_hex(&bytes));
    }
    let accepted_json = serde_json::to_value(accepted_record).expect("serialize accepted audit");
    let rejected_json = serde_json::to_value(rejected_record).expect("serialize rejected audit");
    assert_eq!(accepted_json["requestOrdinal"], 2);
    assert_eq!(accepted_json["sequence"], 1);
    assert_eq!(rejected_json["requestOrdinal"], 1);
    assert!(
        rejected_json["problem"]["path"]
            .as_str()
            .is_some_and(|path| path.ends_with("/01/Problem.v"))
    );
    assert!(
        outcome
            .latest_feedback
            .as_deref()
            .is_some_and(|feedback| feedback.contains("exit Some(0)"))
    );
    std::fs::remove_dir_all(root).expect("remove diagnostic audit test tree");
}

#[test]
#[ignore = "requires Unix socket creation, unavailable in restricted test sandboxes"]
fn diagnostic_broker_finish_fails_closed_on_rejected_evidence_drift() {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after Unix epoch")
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "logos-diagnostic-evidence-drift-test-{}-{nonce}",
        std::process::id()
    ));
    let stage = root.join("stage");
    let artifacts = root.join("artifacts");
    let proof = root.join("proof");
    let repo = root.join("repo");
    for directory in [&stage, &artifacts, &proof, &repo] {
        std::fs::create_dir_all(directory).expect("create broker test directory");
    }
    for name in ["Schema.v", "Queries.v", "Witness.v", "Goal.v"] {
        std::fs::write(proof.join(name), format!("(* {name} *)\n"))
            .expect("write trusted test input");
    }
    let checker = root.join("checker-must-not-run.sh");
    complete_broker_witness_fixture(&proof);
    std::fs::write(&checker, "#!/usr/bin/env bash\nexit 99\n").expect("write checker sentinel");
    let broker = DiagnosticBroker::start(
        &artifacts,
        3,
        1,
        &checker,
        &proof,
        &repo,
        None,
        None,
        2 * 1024 * 1024 * 1024,
        Instant::now() + Duration::from_secs(30),
    )
    .expect("start diagnostic broker");
    let problem = b"Load \"/host-only/secret.v\".\n";
    let candidate_sha256 = sha256_hex(problem);
    std::fs::write(stage.join("Problem.v"), problem).expect("write rejected Problem.v");
    let response = send_diagnostic_broker_request(
        broker.socket_path(),
        &stage,
        serde_json::json!({
            "schemaVersion": 2,
            "nonce": broker.nonce(),
            "mode": "problem",
            "candidatePath": "Problem.v",
            "purpose": "assembly",
            "candidateSha256": candidate_sha256,
            "requestedTimeoutSeconds": 5
        }),
    );
    assert_eq!(response["sequence"], serde_json::Value::Null);
    assert_eq!(response["problemCompilePassed"], false);
    let feedback = artifacts.join(
        "proof-stage/proof-agent/rounds/03/rejected-diagnostic-source-audits/01/feedback.txt",
    );
    std::fs::write(&feedback, "tampered after host binding").expect("tamper rejected feedback");
    let error = broker
        .finish()
        .expect_err("bound diagnostic evidence drift must fail closed")
        .to_string();
    assert!(error.contains("diagnostic broker evidence integrity failure"));
    assert!(error.contains("feedback.txt"));
    std::fs::remove_dir_all(root).expect("remove evidence drift test tree");
}

#[test]
fn initial_problem_checkpoints_are_versioned_and_create_once() {
    let fixture = tempfile::tempdir().expect("create checkpoint fixture");
    let artifacts =
        ArtifactWriter::new(Some(fixture.path().join("case"))).expect("artifact writer");
    let problem_path = fixture.path().join("Problem.v");
    let first_problem = b"Definition generation_one : True := I.\n";
    std::fs::write(&problem_path, first_problem).expect("write first Problem.v");
    let invocation = DiagnosticCheckerInvocation {
        probe: None,
        sequence: Some(0),
        mode: Some("problem".to_owned()),
        candidate_sha256: Some(sha256_hex(first_problem)),
        candidate_path: Some("Problem.v".to_owned()),
        purpose: Some("assembly".to_owned()),
        compile_passed: Some(true),
        problem_compile_passed: Some(true),
        compile_checkpoint_advanced: Some(true),
        stdout_sha256: Some(sha256_hex(b"\xffstdout")),
        stderr_sha256: Some(sha256_hex(b"\xfestderr")),
        requested_timeout_seconds: 30,
        effective_timeout_seconds: 30,
        started_at_unix_ms: 1,
        elapsed_ms: 2,
        exit_code: Some(0),
        timed_out: false,
        error: None,
    };
    let first = persist_initial_problem_compile_checkpoint_evidence(
        &artifacts,
        1,
        &problem_path,
        b"\xffstdout",
        b"\xfestderr",
        &invocation,
    )
    .expect("persist generation-one checkpoint");
    assert_eq!(
        first,
        artifacts.root().join(
            "proof-stage/proof-agent/workspace-generations/0001/initial-problem-checkpoint/Problem.v"
        )
    );
    assert_eq!(std::fs::read(&first).unwrap(), first_problem);
    assert_eq!(
        std::fs::read(first.parent().unwrap().join("stdout.txt")).unwrap(),
        b"\xffstdout"
    );

    let second_problem = b"Definition generation_two : True := I.\n";
    std::fs::write(&problem_path, second_problem).expect("write second Problem.v");
    let error = persist_initial_problem_compile_checkpoint_evidence(
        &artifacts,
        1,
        &problem_path,
        b"replacement",
        b"replacement",
        &invocation,
    )
    .expect_err("generation-one evidence must be immutable")
    .to_string();
    assert!(error.contains("create-once initial checkpoint evidence"));
    assert_eq!(std::fs::read(&first).unwrap(), first_problem);

    let second = persist_initial_problem_compile_checkpoint_evidence(
        &artifacts,
        2,
        &problem_path,
        b"stdout two",
        b"stderr two",
        &invocation,
    )
    .expect("persist generation-two checkpoint");
    assert!(
        second
            .to_string_lossy()
            .contains("workspace-generations/0002")
    );
    assert_eq!(std::fs::read(second).unwrap(), second_problem);
}

#[test]
fn trusted_preflight_evidence_is_versioned_raw_and_create_once() {
    let fixture = tempfile::tempdir().expect("create preflight fixture");
    let artifacts =
        ArtifactWriter::new(Some(fixture.path().join("case"))).expect("artifact writer");
    let invocation = TrustedCheckInvocation {
        timeout_seconds: 420,
        elapsed_ms: 421_001,
        exit_code: Some(0),
        timed_out: false,
        error: None,
    };
    persist_trusted_environment_preflight_evidence(
        &artifacts,
        1,
        b"\xffpreflight stdout",
        b"\xfepreflight stderr",
        &invocation,
    )
    .expect("persist generation-one preflight");
    let root = artifacts
        .root()
        .join("proof-stage/proof-agent/workspace-generations/0001/trusted-environment-preflight");
    assert_eq!(
        std::fs::read(root.join("stdout.txt")).unwrap(),
        b"\xffpreflight stdout"
    );
    assert_eq!(
        serde_json::from_slice::<serde_json::Value>(
            &std::fs::read(root.join("invocation.json")).unwrap()
        )
        .unwrap()["elapsedMs"],
        421_001
    );
    let error = persist_trusted_environment_preflight_evidence(
        &artifacts,
        1,
        b"replacement",
        b"replacement",
        &invocation,
    )
    .expect_err("preflight evidence must be immutable")
    .to_string();
    assert!(error.contains("create-once trusted preflight evidence"));
    persist_trusted_environment_preflight_evidence(
        &artifacts,
        2,
        b"generation two",
        b"generation two",
        &invocation,
    )
    .expect("persist generation-two preflight");
    assert!(
        artifacts
            .root()
            .join("proof-stage/proof-agent/workspace-generations/0002/trusted-environment-preflight/invocation.json")
            .is_file()
    );
}

#[test]
fn handoff_digest_uses_cross_language_canonical_json() {
    let handoff = ProofCounterexampleHandoff {
        decision: ProofAgentDecision::CounterexampleCandidate,
        reason: "witness café".to_owned(),
        guidance: "use Ω".to_owned(),
    };
    assert_eq!(
        canonical_json_sha256(&handoff).expect("canonical handoff digest"),
        "80d6572a83f08a4be4f10e94c84305ed370b81ff692b45fe019d15e41a1b94a0"
    );
}

#[test]
fn workspace_transition_serializes_the_runner_contract() {
    let transition = ProofWorkspaceTransition {
        after_round: 3,
        from_workspace_generation: 1,
        to_workspace_generation: 2,
        reason: ProofWorkspaceTransitionReason::FixedWitnessReplacement,
        triggering_handoff_sha256: "a".repeat(64),
        from_context_manifest_sha256: "b".repeat(64),
        to_context_manifest_sha256: "c".repeat(64),
        from_trusted_diagnostic_cache: TrustedDiagnosticCacheEvidence {
            workspace_generation: 1,
            manifest_path: "proof-stage/proof-agent/workspace-generations/0001/trusted-diagnostic-cache/SHA256SUMS".to_owned(),
            manifest_sha256: "d".repeat(64),
        },
        new_trusted_environment_preflight: TrustedCheckInvocation {
            timeout_seconds: 420,
            elapsed_ms: 421_000,
            exit_code: Some(0),
            timed_out: false,
            error: None,
        },
        new_initial_problem_compile_checkpoint: ProblemCompileCheckpointEvidence {
            workspace_generation: 2,
            path: "proof-stage/proof-agent/workspace-generations/0002/initial-problem-checkpoint/Problem.v".to_owned(),
            sha256: "e".repeat(64),
            round: 0,
            sequence: 0,
        },
    };
    let serialized = serde_json::to_value(&transition).expect("serialize transition");
    assert_eq!(serialized["reason"], "fixedWitnessReplacement");
    assert_eq!(
        serialized["fromTrustedDiagnosticCache"]["workspaceGeneration"],
        1
    );
    assert_eq!(
        serialized["newTrustedEnvironmentPreflight"]["elapsedMs"],
        421_000
    );
    assert_eq!(
        serialized["newInitialProblemCompileCheckpoint"]["workspaceGeneration"],
        2
    );
    assert_eq!(
        serde_json::to_value(ProofCheckpointTransition::NewWorkspaceInitial).unwrap(),
        "newWorkspaceInitial"
    );
    assert_eq!(
        serde_json::to_value(ProofSessionRestartReason::FailedRoundLimit).unwrap(),
        "failedRoundLimit"
    );
}

#[test]
fn compile_checkpoint_restore_verifies_retained_bytes() {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after Unix epoch")
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "logos-checkpoint-restore-test-{}-{nonce}",
        std::process::id()
    ));
    std::fs::create_dir_all(&root).expect("create checkpoint test root");
    let path = root.join("Problem.v");
    std::fs::write(&path, b"rejected\n").expect("write rejected candidate");
    let problem = b"Definition compiled : True := I.\n".to_vec();
    let retained = root.join("retained.v");
    std::fs::write(&retained, &problem).expect("write retained checkpoint");
    let checkpoint = CompileCheckpoint {
        sha256: sha256_hex(&problem),
        path: retained,
        workspace_generation: 1,
        round: 2,
        sequence: 3,
    };
    restore_problem_compile_checkpoint(&path, &checkpoint, 1).expect("restore checkpoint");
    assert_eq!(std::fs::read(&path).unwrap(), problem);

    let mut corrupt = checkpoint.clone();
    corrupt.sha256 = "0".repeat(64);
    assert!(restore_problem_compile_checkpoint(&path, &corrupt, 1).is_err());
    assert_eq!(std::fs::read(&path).unwrap(), problem);
    assert!(restore_problem_compile_checkpoint(&path, &checkpoint, 2).is_err());
    std::fs::remove_dir_all(root).expect("remove checkpoint test tree");
}

#[test]
fn proof_session_homes_are_isolated_per_generation() {
    let fixture = tempfile::tempdir().expect("create proof temp fixture");
    let artifacts =
        ArtifactWriter::new(Some(fixture.path().join("case"))).expect("create artifact writer");
    let host_tmp = proof_agent_host_tmp_directory(&artifacts).expect("create host temp root");
    let home = ProofAgentSessionHome::create(&artifacts).expect("create session-home root");
    assert_eq!(home.path.parent(), Some(host_tmp.as_path()));
    assert!(home.path.starts_with(artifacts.root()));
    assert!(home.generation_path(0).is_err());

    let generation_one = home.generation_path(1).expect("create generation one");
    std::fs::write(generation_one.join("prior-session-marker"), "private")
        .expect("write generation-one marker");
    assert_eq!(
        home.generation_path(1).expect("reuse generation one"),
        generation_one
    );
    assert_eq!(
        std::fs::metadata(&generation_one)
            .expect("generation-one metadata")
            .permissions()
            .mode()
            & 0o777,
        0o700
    );

    let generation_two = home.generation_path(2).expect("create generation two");
    assert_ne!(generation_two, generation_one);
    assert!(!generation_two.join("prior-session-marker").exists());

    symlink(&generation_one, home.path.join("generation-0003"))
        .expect("create adversarial generation symlink");
    assert!(home.generation_path(3).is_err());

    let round = ProofAgentRoundStage::create(&artifacts).expect("create round stage");
    assert_eq!(round.path().parent(), Some(host_tmp.as_path()));
    assert!(round.path().starts_with(artifacts.root()));
    assert_eq!(
        std::fs::metadata(round.path())
            .expect("round-stage metadata")
            .permissions()
            .mode()
            & 0o777,
        0o700
    );
    let home_path = home.path.clone();
    let round_path = round.path().to_owned();
    drop(round);
    drop(home);
    assert!(!round_path.exists());
    assert!(!home_path.exists());
    assert!(host_tmp.is_dir());
}

#[test]
fn proof_agent_state_directory_publication_is_atomic_across_signals_and_failures() {
    let function_tail = FORMAL_SQL_DOCKER_AGENT_SCRIPT
        .split("atomic_exchange_directories() {")
        .nth(1)
        .expect("embedded launcher atomic-exchange function");
    let function_end = function_tail
        .find("\n}\n\npublish_authority_closure()")
        .expect("embedded launcher atomic-exchange terminator");
    let exchange_function = format!(
        "atomic_exchange_directories() {{{}\n}}",
        &function_tail[..function_end]
    );
    let fixture = tempfile::tempdir().expect("create atomic publication fixture");
    let live = fixture.path().join("live");
    let returned = fixture.path().join("returned");
    std::fs::create_dir(&live).expect("create live state");
    std::fs::create_dir(&returned).expect("create returned state");
    std::fs::write(live.join("OLD"), "old state\n").expect("write old marker");
    std::fs::write(returned.join("NEW"), "new state\n").expect("write new marker");

    let interrupted = Command::new("/usr/bin/bash")
        .arg("-c")
        .arg(format!(
            "set -euo pipefail\ntrap 'exit 143' TERM\n{exchange_function}\natomic_exchange_directories \"$RETURNED\" \"$LIVE\"\nkill -TERM $$\n"
        ))
        .env_clear()
        .env("PATH", "/usr/bin:/bin")
        .env("RETURNED", &returned)
        .env("LIVE", &live)
        .output()
        .expect("run signal-interrupted atomic state publication");
    assert_eq!(interrupted.status.code(), Some(143));
    assert_eq!(
        std::fs::read_to_string(live.join("NEW")).expect("read published state"),
        "new state\n"
    );
    assert_eq!(
        std::fs::read_to_string(returned.join("OLD")).expect("read displaced state"),
        "old state\n"
    );
    assert!(!live.join("OLD").exists());
    assert!(!returned.join("NEW").exists());

    let invalid = fixture.path().join("missing-returned");
    let rejected = Command::new("/usr/bin/bash")
        .arg("-c")
        .arg(format!(
            "set -euo pipefail\n{exchange_function}\natomic_exchange_directories \"$INVALID\" \"$LIVE\"\n"
        ))
        .env_clear()
        .env("PATH", "/usr/bin:/bin")
        .env("INVALID", &invalid)
        .env("LIVE", &live)
        .output()
        .expect("run rejected atomic state publication");
    assert!(!rejected.status.success());
    assert_eq!(
        std::fs::read_to_string(live.join("NEW")).expect("read retained live state"),
        "new state\n"
    );

    assert!(!FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("rm -rf \"$AGENT_STAGE/scratch\""));
    assert!(!FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("rm -rf \"$CODEX_HOME_STAGE\""));
    assert!(
        FORMAL_SQL_DOCKER_AGENT_SCRIPT
            .contains("atomic_exchange_directories \\\n  \"$EXPORT_STAGE/problem/scratch\"")
    );
    assert!(
        FORMAL_SQL_DOCKER_AGENT_SCRIPT
            .contains("atomic_exchange_directories \\\n  \"$EXPORT_STAGE/codex-home\"")
    );
    let home_publication = FORMAL_SQL_DOCKER_AGENT_SCRIPT
        .find(
            "atomic_exchange_directories \\\n  \"$EXPORT_STAGE/codex-home\" \\\n  \"$CODEX_HOME_STAGE\"",
        )
        .expect("Codex home publication");
    let authority_publication = FORMAL_SQL_DOCKER_AGENT_SCRIPT
        .rfind("publish_authority_closure || exit 2")
        .expect("final authority-closure publication");
    let problem_publication = FORMAL_SQL_DOCKER_AGENT_SCRIPT
        .find("publish_stage_file \"$AGENT_STAGE/Problem.v\" \"$WORKDIR/Problem.v\"")
        .expect("Problem workspace publication");
    let stdout_publication = FORMAL_SQL_DOCKER_AGENT_SCRIPT
        .find("publish_stage_file \"$EXPORT_STAGE/agent-stdout\"")
        .expect("agent stdout publication");
    assert!(home_publication < authority_publication);
    assert!(authority_publication < problem_publication);
    assert!(problem_publication < stdout_publication);
}

#[test]
fn case_process_supervisor_pid_parser_is_strict_and_canonical() {
    assert_eq!(
        super::diagnostics::parse_case_process_supervisor_pid(std::ffi::OsStr::new("1"))
            .expect("minimum positive pid"),
        1
    );
    assert_eq!(
        super::diagnostics::parse_case_process_supervisor_pid(std::ffi::OsStr::new("4294967295"))
            .expect("maximum u32 pid"),
        u32::MAX
    );
    for malformed in [
        b"".as_slice(),
        b"0",
        b"01",
        b"+1",
        b" 1",
        b"1\n",
        b"4294967296",
        b"\xff",
    ] {
        assert!(
            super::diagnostics::parse_case_process_supervisor_pid(std::ffi::OsStr::from_bytes(
                malformed
            ))
            .is_err(),
            "accepted malformed supervisor pid: {malformed:?}"
        );
    }
}

#[test]
fn diagnostic_socket_directory_is_short_private_sidecar_bound_and_raii_cleaned() {
    let fixture = tempfile::tempdir().expect("create diagnostic socket fixture");
    let artifacts =
        ArtifactWriter::new(Some(fixture.path().join("case"))).expect("create artifact writer");
    let host_tmp = proof_agent_host_tmp_directory(&artifacts).expect("create host temp root");
    let socket_directory = super::diagnostics::SocketDirectory::create(artifacts.root(), 97)
        .expect("create short diagnostic socket directory");
    let socket_path = socket_directory.socket_path();
    let directory_path = socket_path.parent().expect("socket directory").to_owned();
    let sidecar_path = socket_directory.sidecar_path.clone();
    assert_eq!(
        socket_path.file_name(),
        Some(std::ffi::OsStr::new("socket"))
    );
    assert!(socket_path.starts_with(super::DIAGNOSTIC_SOCKET_TEMP_ROOT));
    assert!(socket_path.to_string_lossy().len() < 100);
    assert_eq!(
        std::fs::metadata(&directory_path)
            .expect("socket directory metadata")
            .permissions()
            .mode()
            & 0o777,
        0o700
    );
    assert_eq!(sidecar_path.parent(), Some(host_tmp.as_path()));
    let sidecar: serde_json::Value = serde_json::from_slice(
        &std::fs::read(&sidecar_path).expect("read diagnostic socket sidecar"),
    )
    .expect("parse diagnostic socket sidecar");
    assert_eq!(sidecar["schemaVersion"], 1);
    assert_eq!(sidecar["solverPid"], std::process::id());
    assert_eq!(
        sidecar["directory"],
        directory_path.to_string_lossy().as_ref()
    );
    drop(socket_directory);
    assert!(!sidecar_path.exists());
    assert!(!directory_path.exists());
}

#[test]
fn proof_host_temp_root_rejects_symlink_redirection() {
    let fixture = tempfile::tempdir().expect("create proof temp fixture");
    let artifacts =
        ArtifactWriter::new(Some(fixture.path().join("case"))).expect("create artifact writer");
    let host_tmp = artifacts.root().join(PROOF_AGENT_HOST_TMP_DIRECTORY);
    std::fs::create_dir_all(host_tmp.parent().unwrap()).expect("create host temp parent");
    let redirected = fixture.path().join("redirected");
    std::fs::create_dir(&redirected).expect("create redirection target");
    symlink(&redirected, &host_tmp).expect("create host temp symlink");
    assert!(ProofAgentSessionHome::create(&artifacts).is_err());
    assert!(ProofAgentRoundStage::create(&artifacts).is_err());
}

#[test]
fn compact_tree_values_escape_every_notation_delimiter() {
    assert_eq!(
        encode_tree_value("schema.a b{c},(%)/é"),
        "schema.a%20b%7Bc%7D%2C%28%25%29%2F%C3%A9"
    );
    assert_eq!(encode_tree_value("safe_Name-1.2"), "safe_Name-1.2");
}

#[test]
fn compact_skeleton_dag_is_lossless_deterministic_and_structurally_interned() {
    let branch = "Branch{items=2;mode=exact}(Leaf,@scalar_select_list_0)";
    let tree = format!("Root({branch},{branch})");
    let trees = [tree.as_str(), tree.as_str()];

    let first = compact_skeleton_forest(&trees, "test").expect("compact skeleton");
    let second = compact_skeleton_forest(&trees, "test").expect("repeat compaction");

    assert_eq!(first, second);
    assert_eq!(first.roots[0], first.roots[1]);
    assert_eq!(first.nodes.len(), 4);
    for root in &first.roots {
        assert_eq!(
            expand_compact_skeleton_node(&first.nodes, *root).unwrap(),
            tree
        );
    }
    assert!(
        first
            .nodes
            .iter()
            .enumerate()
            .all(|(node_id, node)| node.1.iter().all(|child| *child < node_id))
    );
}

#[test]
fn compact_skeleton_parser_and_validator_fail_closed_on_drift() {
    for malformed in [
        "",
        "Node()",
        "Node(Leaf,)",
        "Node(Leaf))",
        "Node(Leaf",
        "Node{field=1",
        " Node",
        "Node ",
        "Node\tWithTab",
        "Nodé",
    ] {
        assert!(
            parse_skeleton_tree(malformed, "test").is_err(),
            "accepted malformed skeleton {malformed:?}"
        );
    }

    let error_constructor = "QExpr_Error{columns=1}(DataException InvalidTextRepresentation)";
    let compacted = compact_skeleton_forest(&[error_constructor], "test")
        .expect("multi-token Rocq constructor leaf is losslessly compacted");
    assert_eq!(
        expand_compact_skeleton_node(&compacted.nodes, compacted.roots[0]).unwrap(),
        error_constructor
    );

    let tree = "Root(Branch(Leaf),Branch(Leaf))";
    let trees = [tree];
    let pristine = compact_skeleton_forest(&trees, "test").unwrap();

    let mut non_postorder = pristine.clone();
    let root = non_postorder.roots[0];
    non_postorder.nodes[root].1.push(root);
    assert!(validate_compacted_skeleton_forest(&non_postorder, &trees, "test").is_err());

    let mut unreachable = pristine.clone();
    unreachable
        .nodes
        .push(super::navigation::CompactSkeletonNode(
            "Unused".to_owned(),
            Vec::new(),
        ));
    assert!(validate_compacted_skeleton_forest(&unreachable, &trees, "test").is_err());

    // Serialized provenance remains exact, but the in-memory round-trip
    // validator checks the tree itself, not a second hash of its input.
    assert_eq!(
        pristine.expanded_trees_sha256,
        super::navigation::compact_skeleton_digest(&trees).unwrap()
    );
    let mut changed_content = pristine;
    changed_content.nodes[0].0 = "DifferentLeaf".to_owned();
    assert!(validate_compacted_skeleton_forest(&changed_content, &trees, "test").is_err());
}

#[test]
fn compact_graph_keeps_provenance_digests_and_checks_contents_directly() {
    use crate::core::FormalQueryDefinitionGraph;
    let graph = FormalQueryDefinitionGraph {
        schema_version: 1,
        notation: "test graph".to_owned(),
        opaque_helper_symbols: vec![],
        definitions: vec![],
        source_statements: vec![],
        target_statements: vec![],
    };
    let compact = super::navigation::compact_definition_graph(&graph).unwrap();
    assert_eq!(
        compact.expanded_graph_sha256,
        sha256_hex(&serde_json::to_vec(&graph).unwrap())
    );
    assert_eq!(
        compact.expanded_trees_sha256,
        super::navigation::compact_skeleton_digest(&[]).unwrap()
    );
    let mut changed_metadata = compact.clone();
    changed_metadata
        .opaque_helper_symbols
        .push("other".to_owned());
    assert!(
        super::navigation::validate_compact_definition_graph(&changed_metadata, &graph).is_err()
    );
    let mut changed_tree = compact;
    changed_tree
        .skeleton_nodes
        .push(super::navigation::CompactSkeletonNode(
            "Unexpected".to_owned(),
            vec![],
        ));
    assert!(super::navigation::validate_compact_definition_graph(&changed_tree, &graph).is_err());
}

#[test]
fn compact_skeleton_regression_preserves_large_graph_without_a_context_cap() {
    let mut repeated = "SExpr_Pred{args=2}(PredicateEq)".to_owned();
    for _ in 0..9 {
        repeated = format!("SExpr_ConjList(And_F,{repeated},{repeated})");
    }
    let trees = vec![repeated.as_str(); 6];
    let expanded_bytes = serde_json::to_vec(&trees).unwrap().len();
    let compacted = compact_skeleton_forest(&trees, "size regression").unwrap();
    let compact_bytes = serde_json::to_vec(&(
        &compacted.expanded_trees_sha256,
        &compacted.nodes,
        &compacted.roots,
    ))
    .unwrap()
    .len();

    assert!(compact_bytes * 20 < expanded_bytes);
}

fn ordered_theory_paths(order: fn(&TrustedRocqImport) -> Option<usize>, ext: &str) -> Vec<String> {
    let mut entries = TRUSTED_ROCQ_IMPORTS
        .iter()
        .filter_map(|import| {
            let path = format!("theories/{}.{}", import.module.replace('.', "/"), ext);
            Some((order(import)?, path))
        })
        .collect::<Vec<_>>();
    entries.sort_unstable_by_key(|(rank, _)| *rank);
    entries.into_iter().map(|(_, path)| path).collect()
}

fn modules_from_import_line(source: &str, prefix: &str) -> Vec<String> {
    let lines = source
        .lines()
        .filter_map(|line| line.trim().strip_prefix(prefix))
        .collect::<Vec<_>>();
    assert_eq!(
        lines.len(),
        1,
        "expected exactly one {prefix:?} import line"
    );
    lines[0]
        .strip_suffix('.')
        .expect("Rocq import terminator")
        .split_whitespace()
        .map(str::to_owned)
        .collect()
}

fn shell_checked_theory_objects() -> Vec<String> {
    let mut in_object_list = false;
    let mut reached_list_end = false;
    let mut checked_objects = Vec::new();
    for line in FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT.lines() {
        let line = line.trim();
        if line == "for file in \\" {
            in_object_list = true;
            continue;
        }
        if !in_object_list {
            continue;
        }
        let rest = line
            .strip_prefix("\"$LOGOS_REPO_ROOT/")
            .expect("trusted object list entry rooted at LOGOS_REPO_ROOT");
        let quote = rest.find('"').expect("trusted object path terminator");
        checked_objects.push(rest[..quote].to_owned());
        if line.ends_with("; do") {
            reached_list_end = true;
            break;
        }
    }
    assert!(reached_list_end, "missing trusted object-list terminator");
    checked_objects
        .into_iter()
        .filter(|path| path.starts_with("theories/") && path.ends_with(".vo"))
        .collect()
}

fn makefile_compiled_theories() -> Vec<String> {
    let recipe = ROOT_MAKEFILE
        .lines()
        .skip_while(|line| *line != "logos-formal-sql-lemmas: formal-sql")
        .skip(1)
        .take_while(|line| line.starts_with('\t'))
        .collect::<Vec<_>>();
    assert!(!recipe.is_empty(), "missing logos-formal-sql-lemmas recipe");
    recipe
        .into_iter()
        .map(|line| {
            line.strip_prefix("\t$(LOGOS_ROCQ_COMPILE) ")
                .expect("every production theory recipe line uses LOGOS_ROCQ_COMPILE")
                .to_owned()
        })
        .collect()
}

fn assert_contiguous_ranks(mut ranks: Vec<usize>) {
    ranks.sort_unstable();
    assert_eq!(ranks, (0..ranks.len()).collect::<Vec<_>>());
}

fn write_placeholder_proof_context(artifacts: &ArtifactWriter) {
    for name in super::PROOF_CONTEXT_FILES {
        artifacts
            .write_text(format!("proof-stage/formal-sql/{name}"), "test context\n")
            .expect("write proof context");
    }
}

#[test]
fn goal_module_requires_the_generated_certificate() {
    assert!(FORMAL_SQL_GOAL_MODULE.contains("exact Problem.generated_queries_verified."));
    assert!(FORMAL_SQL_GOAL_MODULE.contains("Schema.generated_schema_conforms db ->"));
    assert!(!FORMAL_SQL_GOAL_MODULE.contains("Definition required_schema_conforms"));
    assert!(FORMAL_SQL_GOAL_MODULE.contains("NullValues.interp_scalar_operator_runtime_error"));
    assert!(FORMAL_SQL_GOAL_MODULE.contains("Definition required_query_program_equiv"));
    assert!(FORMAL_SQL_GOAL_MODULE.contains("Definition required_query_program_outcome_equiv"));
    assert!(FORMAL_SQL_GOAL_MODULE.contains("Definition required_query_program_admissible"));
    assert!(FORMAL_SQL_GOAL_MODULE.contains("Definition required_countermodel_statement"));
    assert!(FORMAL_SQL_GOAL_MODULE.contains(
        "Definition required_verification_statement\n    (claim : verification_claim_kind)"
    ));
    assert!(
        FORMAL_SQL_GOAL_MODULE
            .contains("Queries.source_program_output_signatures =\n      Queries.target_program_output_signatures /\\")
    );
    assert!(FORMAL_SQL_GOAL_MODULE.contains(
        "Queries.source_program_output_signatures =\n      map query_expr_outputs\n        Queries.source_query_program /\\"
    ));
    assert!(FORMAL_SQL_GOAL_MODULE.contains(
        "Queries.target_program_output_signatures =\n      map query_expr_outputs\n        Queries.target_query_program /\\"
    ));
    assert!(FORMAL_SQL_GOAL_MODULE.contains(
        "required_query_program_admissible\n        db Queries.source_query_program /\\"
    ));
    assert!(FORMAL_SQL_GOAL_MODULE.contains(
        "required_query_program_admissible\n        db Queries.target_query_program /\\"
    ));
    assert!(FORMAL_SQL_GOAL_MODULE.contains(
        "required_query_program_equiv db\n        Queries.source_query_program\n        Queries.target_query_program)."
    ));
    assert!(!FORMAL_SQL_GOAL_MODULE.contains("required_list_query_equiv"));
    let statement = FORMAL_SQL_GOAL_MODULE
        .find("Definition required_equivalence_statement")
        .expect("trusted statement definition");
    let countermodel = FORMAL_SQL_GOAL_MODULE
        .find("Definition required_countermodel_statement")
        .expect("trusted countermodel definition");
    let problem_import = FORMAL_SQL_GOAL_MODULE
        .find("From LogosGenerated Require Problem")
        .expect("problem import");
    assert!(statement < problem_import);
    assert!(countermodel < problem_import);
}

#[test]
fn goal_modules_enforce_the_selected_equivalence_strength() {
    let safe = formal_sql_goal_module(VerificationMode::SafeUnconditional);
    assert!(safe.contains("@query_program_possible_equiv TNull relname"));
    assert!(!safe.contains("@query_program_equiv TNull relname"));
    assert!(!safe.contains("verification_condition_holds db condition"));

    let outcome = formal_sql_goal_module(VerificationMode::OutcomeUnconditional);
    assert!(outcome.contains("@query_program_possible_outcome_equiv TNull relname"));
    assert!(!outcome.contains("@query_program_outcome_equiv TNull relname"));
    assert!(!outcome.contains("verification_condition_holds db condition"));

    let conditional = formal_sql_goal_module(VerificationMode::Conditional);
    assert!(conditional.contains("@query_program_possible_outcome_equiv TNull relname"));
    assert!(conditional.contains("verification_condition_holds db condition ->"));
    assert!(conditional.contains("Problem.generated_precondition_valid"));
    assert!(conditional.contains("Problem.generated_precondition_source"));
    assert!(conditional.contains("Problem.generated_precondition"));
    assert!(!conditional.contains("Definition required_countermodel_statement"));
    assert!(!conditional.contains("Problem.generated_verification_claim"));

    let bound_safe = formal_sql_bound_goal_module(VerificationMode::SafeUnconditional);
    assert!(bound_safe.contains("bound_query_program_possible_equiv"));
    assert!(!bound_safe.contains("bound_query_program_demand_safe_outcome_equiv"));

    let bound_outcome = formal_sql_bound_goal_module(VerificationMode::OutcomeUnconditional);
    assert!(bound_outcome.contains("bound_query_program_demand_safe_outcome_equiv"));
    assert!(bound_outcome.contains("Definition required_query_program_materialization_safe"));
    assert!(bound_outcome.contains(
        "required_query_program_materialization_safe\n        Witness.generated_witness_db\n        Queries.source_bound_query_program"
    ));
    assert!(bound_outcome.contains(
        "required_query_program_materialization_safe\n        Witness.generated_witness_db\n        Queries.target_bound_query_program"
    ));

    let bound_conditional = formal_sql_bound_goal_module(VerificationMode::Conditional);
    assert!(bound_conditional.contains("bound_query_program_demand_safe_outcome_equiv"));
    assert!(bound_conditional.contains("verification_condition_holds db condition ->"));
    assert!(!bound_conditional.contains("Definition required_countermodel_statement"));
}

#[test]
fn proof_backend_status_distinguishes_agent_completion_from_certification() {
    assert_eq!(
        proof_backend_status(false, false, false, None),
        BackendStatus::LoweringBlocked
    );
    assert_eq!(
        proof_backend_status(true, false, false, None),
        BackendStatus::WorkspaceGenerated
    );
    assert_eq!(
        proof_backend_status(true, false, false, Some((false, Some(0)))),
        BackendStatus::ProofAgentRunCompleted
    );
    assert_eq!(
        proof_backend_status(true, false, false, Some((false, Some(1)))),
        BackendStatus::ProofAgentFailed
    );
    assert_eq!(
        proof_backend_status(true, false, false, Some((true, Some(0)))),
        BackendStatus::ProofComplete
    );
    assert_eq!(
        proof_backend_status(true, true, false, Some((false, Some(0)))),
        BackendStatus::ProofSearchTimedOut
    );
    assert_eq!(
        proof_backend_status(true, false, true, Some((false, Some(0)))),
        BackendStatus::NeedsManualReview
    );
    assert_eq!(
        proof_backend_status(true, false, true, Some((true, Some(0)))),
        BackendStatus::ProofComplete,
        "a trusted certificate must take priority over a stale stop flag"
    );
}

#[test]
fn proof_round_records_missing_session_but_resolves_handoff_before_fatal_break() {
    // This is an intentional control-flow contract. A fixed-witness
    // replacement starts a fresh proof generation and must not be
    // discarded merely because the old Codex invocation failed before
    // emitting its session UUID.
    let source = include_str!("../../src/engine/proof_stage.rs");
    let round_logic = source
        .find("let round_success = round_result.log.success;")
        .expect("proof round result handling");
    let source = &source[round_logic..];
    let missing_session_evidence = source
        .find("if !round_success && !session_resumable {")
        .expect("missing-session evidence recording");
    let round_recorded = source
        .find("proof_agent_rounds.push(round_result.log);")
        .expect("round evidence publication");
    let successful_terminal = source
        .find("if round_success {")
        .expect("trusted successful round termination");
    let handoff_resolution = source
        .find("if let Some(handoff) = handoff {")
        .expect("host handoff resolution");
    let direct_manual_review_terminal = source[handoff_resolution..]
        .find("resolve_handoff(")
        .map(|offset| handoff_resolution + offset)
        .expect("direct proof-agent manual-review terminal disposition");
    let manual_review_terminal = source[handoff_resolution..]
        .find("ProofHandoffResolution::NeedsManualReview(request)")
        .map(|offset| handoff_resolution + offset)
        .expect("manual-review terminal disposition");
    let fatal_resume_break = source[handoff_resolution..]
        .find("if !session_resumable {")
        .map(|offset| handoff_resolution + offset)
        .expect("fatal unavailable-resume decision");
    assert!(missing_session_evidence < round_recorded);
    assert!(round_recorded < successful_terminal);
    assert!(successful_terminal < handoff_resolution);
    assert!(round_recorded < handoff_resolution);
    assert!(handoff_resolution < direct_manual_review_terminal);
    assert!(direct_manual_review_terminal < manual_review_terminal);
    assert!(manual_review_terminal < fatal_resume_break);
}

#[test]
fn codex_session_id_is_validated_and_bound_into_resume_command() {
    let session_id = "019f7ed2-b56c-77a0-8ab5-31d110b90e6b";
    assert!(is_codex_session_id(session_id));
    let command = render_proof_agent_resume_command(DEFAULT_PROOF_AGENT_RESUME_COMMAND, session_id)
        .expect("valid resume command");
    assert!(command.starts_with("codex exec resume "));
    assert!(command.contains("--json --model gpt-6.1-sol"));
    assert!(command.contains("--disable plugins"));
    assert!(command.contains("--disable goals"));
    assert!(DEFAULT_PROOF_AGENT_COMMAND.contains("--disable goals"));
    assert!(command.contains(session_id));
    assert!(!command.contains("{session_id}"));
}

#[test]
fn malformed_or_unbound_resume_sessions_are_rejected() {
    assert!(!is_codex_session_id("../../auth.json"));
    assert!(
        render_proof_agent_resume_command("codex exec resume {session_id}", "not-a-uuid").is_err()
    );
    assert!(
        render_proof_agent_resume_command(
            "codex exec resume --last",
            "019f7ed2-b56c-77a0-8ab5-31d110b90e6b",
        )
        .is_err()
    );
}

mod handoff;

fn proof_run_log_fixture() -> AgentRunLog {
    let binding = |path: &str| DiagnosticArtifactBinding {
        path: path.to_owned(),
        sha256: "a".repeat(64),
        bytes: 17,
    };
    let accepted_source_audit = AcceptedDiagnosticSourceAudit {
        request_ordinal: 2,
        sequence: 1,
        mode: "problem".to_owned(),
        candidate_path: "Problem.v".to_owned(),
        purpose: "assembly".to_owned(),
        candidate_sha256: "b".repeat(64),
        requested_timeout_seconds: 5,
        candidate: binding(
            "proof-stage/proof-agent/rounds/02/interactive-diagnostics/01/checked-workspace/Problem.v",
        ),
        audit: binding("proof-stage/proof-agent/rounds/02/interactive-diagnostics/01/audit.json"),
    };
    let rejected_source_audit = RejectedDiagnosticSourceAudit {
        request_ordinal: 3,
        mode: "scratch".to_owned(),
        candidate_path: "scratch/rejected.v".to_owned(),
        purpose: "semantic-equivalence".to_owned(),
        candidate_sha256: "c".repeat(64),
        requested_timeout_seconds: 5,
        problem: binding(
            "proof-stage/proof-agent/rounds/02/rejected-diagnostic-source-audits/03/Problem.v",
        ),
        request: binding(
            "proof-stage/proof-agent/rounds/02/rejected-diagnostic-source-audits/03/request.json",
        ),
        audit: binding(
            "proof-stage/proof-agent/rounds/02/rejected-diagnostic-source-audits/03/audit.json",
        ),
        feedback: binding(
            "proof-stage/proof-agent/rounds/02/rejected-diagnostic-source-audits/03/feedback.txt",
        ),
    };
    AgentRunLog {
        round: 2,
        workspace_generation: 1,
        session_generation: 1,
        session_restarted: false,
        session_restart_reason: None,
        checkpoint_transition: ProofCheckpointTransition::Continued,
        command: "codex exec resume".to_owned(),
        context_manifest_sha256: "abc123".to_owned(),
        remaining_proof_search_seconds: 900,
        round_budget_seconds: 480,
        session_id: Some("019f7ed2-b56c-77a0-8ab5-31d110b90e6b".to_owned()),
        docker_image: "logos-solver:test".to_owned(),
        started_ms_since_epoch: 1,
        elapsed_ms: 2,
        success: false,
        exit_code: Some(0),
        proof_check_exit_code: Some(1),
        proof_check_elapsed_ms: Some(3),
        proof_check_timeout_seconds: Some(420),
        proof_check_timed_out: false,
        authority_closure_path: None,
        authority_closure_sha256: None,
        authority_closure_bytes: None,
        candidate_problem_sha256: "candidate123".to_owned(),
        candidate_problem_compile_passed: true,
        candidate_has_final_theorem: true,
        candidate_claim: Some(VerificationClaimKind::Equivalence),
        active_problem_compile_checkpoint_sha256: "checkpoint123".to_owned(),
        updated_problem_compile_checkpoint_sha256: Some("candidate123".to_owned()),
        compile_checkpoint_restored: false,
        diagnostic_checker_telemetry_path: None,
        diagnostic_checker_invocations: Vec::new(),
        diagnostic_checker_telemetry_error: None,
        diagnostic_requests_seen: 4,
        diagnostic_requested_timeout_seconds_reserved: 10,
        diagnostic_accepted_count: 1,
        diagnostic_rejected_source_audit_count: 1,
        diagnostic_other_rejected_request_count: 2,
        diagnostic_accepted_source_audits: vec![accepted_source_audit],
        diagnostic_rejected_source_audits: vec![rejected_source_audit],
        scratch_file_count: 2,
        scratch_bytes: 34,
        stdout_path: "rounds/02/stdout.txt".to_owned(),
        stderr_path: "rounds/02/stderr.txt".to_owned(),
        stdout_bytes: 4,
        stderr_bytes: 5,
        events_path: "rounds/02/events.jsonl".to_owned(),
        usage: Some(LlmUsage::from_counts(120, 100, 30).unwrap()),
        usage_error: None,
        audit: AgentAudit {
            passed: true,
            scanned_files: Vec::new(),
            findings: Vec::new(),
        },
        precondition_source: None,
        precondition_definition: None,
        counterexample_handoff: None,
        error: Some("repair continues".to_owned()),
    }
}

#[test]
fn proof_run_artifact_preserves_cumulative_and_incremental_usage() {
    let log = proof_run_log_fixture();
    let incremental = log.usage.clone().unwrap();
    let cumulative = LlmUsage::from_counts(220, 180, 50).unwrap();

    let value = serde_json::to_value(AgentRunArtifact {
        log: &log,
        cumulative_usage: Some(&cumulative),
    })
    .expect("serialize proof run record");
    assert_eq!(value["sessionId"], serde_json::json!(log.session_id));
    assert_eq!(value["usage"], serde_json::to_value(incremental).unwrap());
    assert_eq!(value["diagnosticRequestsSeen"], 4);
    assert_eq!(value["diagnosticRequestedTimeoutSecondsReserved"], 10);
    assert_eq!(value["diagnosticAcceptedCount"], 1);
    assert_eq!(value["diagnosticRejectedSourceAuditCount"], 1);
    assert_eq!(value["diagnosticOtherRejectedRequestCount"], 2);
    assert_eq!(
        value["diagnosticAcceptedSourceAudits"][0]["requestOrdinal"],
        2
    );
    assert_eq!(value["diagnosticAcceptedSourceAudits"][0]["sequence"], 1);
    assert_eq!(
        value["diagnosticAcceptedSourceAudits"][0]["mode"],
        "problem"
    );
    assert_eq!(
        value["diagnosticAcceptedSourceAudits"][0]["candidatePath"],
        "Problem.v"
    );
    assert_eq!(
        value["diagnosticRejectedSourceAudits"][0]["requestOrdinal"],
        3
    );
    assert!(
        value["diagnosticRejectedSourceAudits"][0]["problem"]["path"]
            .as_str()
            .is_some_and(|path| path.ends_with("/03/Problem.v"))
    );
    assert_eq!(value["scratchFileCount"], 2);
    assert_eq!(value["scratchBytes"], 34);
    assert_eq!(
        value["cumulativeUsage"],
        serde_json::to_value(cumulative).unwrap()
    );
    let repair_feedback = super::proof_round_repair_feedback(
        &log,
        Some("[trusted final Rocq check stderr]\nFINAL-CHECK-REPAIR-MARKER"),
    );
    assert!(repair_feedback.contains("Bounded host final-check diagnostics"));
    assert!(repair_feedback.contains("FINAL-CHECK-REPAIR-MARKER"));
    assert!(repair_feedback.contains("prior round stdout/stderr artifacts"));
    let repair_feedback_without_final_tail = super::proof_round_repair_feedback(&log, None);
    assert!(repair_feedback_without_final_tail.contains("prior round stdout/stderr artifacts"));
    assert!(!repair_feedback_without_final_tail.contains("tails above"));

    let without_cumulative = serde_json::to_value(AgentRunArtifact {
        log: &log,
        cumulative_usage: None,
    })
    .expect("serialize failed proof run record");
    assert!(without_cumulative.get("cumulativeUsage").is_none());
}

#[test]
fn final_configuration_refreshes_the_dynamic_module_cache_manifest_binding() {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after Unix epoch")
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "logos-dynamic-module-manifest-{}-{nonce}",
        std::process::id()
    ));
    let artifacts = ArtifactWriter::new(Some(root.clone())).expect("artifact writer");
    let manifest_path = "proof-stage/proof-agent/trusted-diagnostic-cache/SHA256SUMS";
    let preflight_manifest = "generated-prefix-only\n";
    artifacts
        .write_text(manifest_path, preflight_manifest)
        .expect("write preflight cache manifest");
    let mut configuration = super::base_proof_agent_configuration(&proof_test_config(&root), None)
        .expect("base proof-agent configuration");
    super::bind_trusted_diagnostic_cache_manifest(&artifacts, &mut configuration)
        .expect("bind preflight manifest");
    let preflight_sha256 = configuration
        .diagnostic_cache_manifest_sha256
        .clone()
        .expect("preflight manifest binding");

    let final_manifest = "generated-prefix-only\nProofModules/CoreFacts.v\n";
    artifacts
        .write_text(manifest_path, final_manifest)
        .expect("write grown module cache manifest");
    super::bind_trusted_diagnostic_cache_manifest(&artifacts, &mut configuration)
        .expect("refresh final manifest");
    let final_sha256 = sha256_hex(final_manifest.as_bytes());
    assert_ne!(preflight_sha256, final_sha256);
    assert_eq!(
        configuration.diagnostic_cache_manifest_path.as_deref(),
        Some(manifest_path)
    );
    assert_eq!(
        configuration.diagnostic_cache_manifest_sha256.as_deref(),
        Some(final_sha256.as_str())
    );
    artifacts
        .write_json("proof-stage/proof-agent/config.json", &configuration)
        .expect("write final proof-agent configuration");
    let persisted: serde_json::Value = serde_json::from_slice(
        &std::fs::read(root.join("proof-stage/proof-agent/config.json"))
            .expect("read persisted proof-agent configuration"),
    )
    .expect("parse persisted proof-agent configuration");
    assert_eq!(
        persisted["diagnosticCacheManifestSha256"],
        serde_json::json!(final_sha256)
    );
    std::fs::remove_dir_all(root).expect("remove manifest test artifacts");
}

#[test]
fn proof_workspace_report_serializes_the_proof_modules_directory() {
    let workspace = ProofWorkspace {
        generated_module_dir: "proof-stage/formal-sql".to_owned(),
        problem_path: "proof-stage/formal-sql/Problem.v".to_owned(),
        proof_modules_dir: "proof-stage/formal-sql/ProofModules".to_owned(),
        scratch_dir: "proof-stage/formal-sql/scratch".to_owned(),
        goal_path: "proof-stage/formal-sql/Goal.v".to_owned(),
        witness_path: "proof-stage/formal-sql/Witness.v".to_owned(),
        source_sql_path: "source.sql".to_owned(),
        target_sql_path: "target.sql".to_owned(),
        query_shape_path: "query-shape.json".to_owned(),
        ordered_signatures_path: "ordered-signatures.json".to_owned(),
        observation_certificates_path: "observation-certificates.json".to_owned(),
        semantic_primer_path: "semantic-primer.md".to_owned(),
        declaration_search_path: "search-rocq-declarations.py".to_owned(),
        context_manifest_path: "context-manifest.json".to_owned(),
        proof_agent_prompt_path: "proof-agent-prompt.md".to_owned(),
        rocq_check_script_path: "run-rocq-check.sh".to_owned(),
        docker_agent_script_path: "run-proof-agent-docker.sh".to_owned(),
    };
    let serialized = serde_json::to_value(workspace).expect("serialize proof workspace");
    assert_eq!(
        serialized["proofModulesDir"],
        "proof-stage/formal-sql/ProofModules"
    );
    assert_eq!(
        serialized["declarationSearchPath"],
        "search-rocq-declarations.py"
    );
    assert!(serialized.get("proof_modules_dir").is_none());
}

#[test]
fn repair_prompt_carries_round_deadline_and_trusted_feedback() {
    let prompt = render_proof_agent_prompt(
        VerificationMode::OutcomeUnconditional,
        Some((
            17,
            Duration::from_secs(631),
            Duration::from_secs(211),
            2,
            true,
        )),
        Some("Problem.v:42: unresolved reference"),
    );

    assert!(prompt.contains("Proof continuation invocation: 17"));
    assert!(prompt.contains("Remaining overall proof-search time: 631 seconds"));
    assert!(prompt.contains("Invocation budget: 211 seconds"));
    assert!(prompt.contains("Proof-session generation: 2"));
    assert!(prompt.contains("fresh Codex session"));
    assert!(prompt.contains("after 16 unsuccessful turns"));
    assert!(prompt.contains("there is no completed-check or broker-request quota"));
    assert!(prompt.contains("byte-identity with the active host checkpoint"));
    assert!(prompt.contains("unchanged active checkpoint is deliberately not recompiled"));
    assert!(prompt.contains("one continuous proof search"));
    assert!(prompt.contains("Scratch is untrusted WIP"));
    assert!(prompt.contains("scratch/checked holds"));
    assert!(prompt.contains("immutable checked ProofModules"));
    assert!(prompt.contains("current host-selected Problem.v"));
    assert!(prompt.contains("do not assume material from an earlier witness generation"));
    assert!(prompt.contains("Problem.v:42: unresolved reference"));
}

#[test]
fn same_session_continuation_prompt_does_not_repeat_static_instructions() {
    let prompt = render_proof_agent_prompt(
        VerificationMode::OutcomeUnconditional,
        Some((
            2,
            Duration::from_secs(600),
            Duration::from_secs(300),
            1,
            false,
        )),
        Some("continue the compiled core lemma"),
    );

    assert!(prompt.contains("Proof continuation invocation: 2"));
    assert!(prompt.contains("Continue under the complete proof contract"));
    assert!(!prompt.contains("## Start from the query"));
    assert!(
        prompt.len() < 2_048,
        "continuation prompt grew to {} bytes",
        prompt.len()
    );
}

#[test]
fn proof_round_budget_uses_the_continuous_available_time_and_preserves_host_reserve() {
    assert_eq!(
        proof_agent_round_budget(Duration::from_secs(3_900), 420),
        Some(Duration::from_secs(3_470))
    );
    assert_eq!(
        proof_agent_round_budget(Duration::from_secs(951), 420),
        Some(Duration::from_secs(521))
    );
    assert_eq!(
        proof_agent_round_budget(Duration::from_secs(550), 420),
        Some(Duration::from_secs(120))
    );
    assert_eq!(
        proof_agent_round_budget(Duration::from_secs(431), 420),
        Some(Duration::from_secs(1))
    );
    assert_eq!(
        proof_agent_round_budget(Duration::from_secs(430), 420),
        None
    );
}

#[test]
fn trusted_environment_failures_are_non_repairable() {
    assert!(is_trusted_rocq_environment_failure(Some(86)));
    assert!(!is_trusted_rocq_environment_failure(Some(1)));
    assert!(!is_trusted_rocq_environment_failure(Some(124)));
    assert!(!is_trusted_rocq_environment_failure(None));

    assert!(FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT.contains("mode=preflight"));
    assert!(FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT.contains("[[ \"$mode\" == preflight ]]"));
    assert!(
        FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT.contains("unset LOGOS_TRUSTED_ENVIRONMENT_PREFLIGHT")
    );
    assert!(
        FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT
            .contains("# Every agent-controlled module is compiled in the same empty-root sandbox")
    );
    assert!(!FORMAL_SQL_ROCQ_CHECK_REQUEST_SCRIPT.contains("command -v rocq"));
    assert!(!FORMAL_SQL_ROCQ_CHECK_REQUEST_SCRIPT.contains("rocq compile"));
    assert!(!FORMAL_SQL_ROCQ_CHECK_REQUEST_SCRIPT.contains("opam"));
}

#[test]
fn host_bash_launch_environment_policies_are_explicit_and_separate() {
    let checker_policy = trusted_checker_environment_policy();
    assert!(checker_policy.inherited_environment_cleared);
    assert_eq!(checker_policy.schema_version, 1);
    assert_eq!(
        checker_policy.fixed_variables,
        [
            format!("PATH={TRUSTED_CHECKER_PATH}"),
            format!("HOME={TRUSTED_CHECKER_HOME}"),
            format!("LC_ALL={FIXED_HOST_LOCALE}"),
            format!("LANG={FIXED_HOST_LOCALE}"),
        ]
    );
    assert!(checker_policy.host_environment_allowlist.is_empty());
    assert_eq!(
        checker_policy.explicit_contract_variables,
        TRUSTED_CHECKER_EXPLICIT_ENVIRONMENT
    );

    let launcher_policy = proof_agent_launcher_environment_policy();
    assert!(launcher_policy.inherited_environment_cleared);
    assert_eq!(launcher_policy.schema_version, 1);
    assert_eq!(
        launcher_policy.fixed_variables,
        [
            format!("PATH={PROOF_AGENT_LAUNCHER_PATH}"),
            format!("LC_ALL={FIXED_HOST_LOCALE}"),
            format!("LANG={FIXED_HOST_LOCALE}"),
        ]
    );
    assert_eq!(
        launcher_policy.host_environment_allowlist,
        PROOF_AGENT_LAUNCHER_HOST_ENVIRONMENT_ALLOWLIST
    );
    assert_eq!(
        launcher_policy.explicit_contract_variables,
        PROOF_AGENT_LAUNCHER_EXPLICIT_ENVIRONMENT
    );
    for policy in [&checker_policy, &launcher_policy] {
        assert_eq!(
            policy.unlisted_environment_policy,
            "excluded_by_env_clear_before_process_start"
        );
        assert_eq!(
            policy.explicitly_excluded_variables,
            EXPLICITLY_EXCLUDED_HOST_ENVIRONMENT
        );
        assert_eq!(
            policy.explicitly_excluded_prefixes,
            EXPLICITLY_EXCLUDED_HOST_ENVIRONMENT_PREFIXES
        );
    }
}

#[test]
fn constructed_host_bash_commands_use_only_their_reported_allowlists() {
    let root = Path::new("/tmp/logos-launch-environment-construction");
    let checker = trusted_rocq_check_command(
        &root.join("proof-agent/trusted-launcher/checker.sh"),
        &root.join("workspace"),
        &root.join("repo"),
        Some(&root.join("rocq-switch")),
        Duration::from_secs(17),
        CheckMode::ProblemDiagnostic {
            timeout_seconds: 11,
        },
    );
    assert_eq!(checker.get_program(), "/usr/bin/timeout");
    let checker_environment = command_environment(&checker);
    let expected_checker_names = [
        "PATH",
        "HOME",
        "LC_ALL",
        "LANG",
        "LOGOS_REPO_ROOT",
        "LOGOS_PROOF_WORKDIR",
        "LOGOS_TRUSTED_ROCQ_CACHE_DIR",
        "LOGOS_ROCQ_OPAM_SWITCH",
    ]
    .into_iter()
    .map(str::to_owned)
    .collect::<BTreeSet<_>>();
    assert_eq!(
        checker_environment.keys().cloned().collect::<BTreeSet<_>>(),
        expected_checker_names
    );
    assert_eq!(checker_environment["PATH"], TRUSTED_CHECKER_PATH);
    assert_eq!(checker_environment["HOME"], TRUSTED_CHECKER_HOME);

    let launcher = proof_agent_launcher_command(
        &root.join("launcher.sh"),
        &root.join("repo"),
        &root.join("workspace"),
        &root.join("codex-home"),
        &root.join("round-stage"),
        &root.join("diagnostic/socket"),
        &"a".repeat(64),
        "logos-solver@sha256:test",
        "codex exec test",
        6_144,
        2 * 1024 * 1024 * 1024,
        Duration::from_secs(123),
    );
    assert_eq!(launcher.get_program(), "/usr/bin/bash");
    let launcher_environment = command_environment(&launcher);
    let mut allowed_launcher_names = ["PATH", "LC_ALL", "LANG"]
        .into_iter()
        .chain(
            PROOF_AGENT_LAUNCHER_HOST_ENVIRONMENT_ALLOWLIST
                .iter()
                .copied(),
        )
        .chain(PROOF_AGENT_LAUNCHER_EXPLICIT_ENVIRONMENT.iter().copied())
        .map(str::to_owned)
        .collect::<BTreeSet<_>>();
    assert!(
        launcher_environment
            .keys()
            .all(|name| allowed_launcher_names.remove(name))
    );
    for name in PROOF_AGENT_LAUNCHER_EXPLICIT_ENVIRONMENT {
        assert!(launcher_environment.contains_key(*name));
    }
    assert_eq!(launcher_environment["PATH"], PROOF_AGENT_LAUNCHER_PATH);
    assert!(!launcher_environment.contains_key("TMPDIR"));
    for name in EXPLICITLY_EXCLUDED_HOST_ENVIRONMENT {
        assert!(!launcher_environment.contains_key(*name));
        assert!(!checker_environment.contains_key(*name));
    }
    assert!(launcher_environment.keys().all(|name| {
        EXPLICITLY_EXCLUDED_HOST_ENVIRONMENT_PREFIXES
            .iter()
            .all(|prefix| !name.starts_with(prefix))
    }));
}

#[test]
fn ambient_bash_startup_state_cannot_reach_either_host_bash_entry_point() {
    const CHILD_MODE: &str = "LOGOS_LAUNCH_ENVIRONMENT_TEST_CHILD";
    if let Some(mode) = std::env::var_os(CHILD_MODE) {
        let bash_env = std::env::var_os("BASH_ENV").expect("child has BASH_ENV sentinel");
        let bash_env = std::path::PathBuf::from(bash_env);
        let root = bash_env.parent().expect("sentinel has parent");
        let marker = root.join("bash-env-executed");
        let script = root.join(format!("{mode:?}-entry.sh"));
        std::fs::write(&script, "#!/usr/bin/bash\n/usr/bin/env\n")
            .expect("write fake Bash entry script");
        let output = match mode.to_string_lossy().as_ref() {
            "checker" => {
                let checker = root.join("proof-agent/trusted-launcher/checker.sh");
                std::fs::create_dir_all(checker.parent().unwrap())
                    .expect("create fake checker directory");
                std::fs::copy(&script, &checker).expect("copy fake checker");
                trusted_rocq_check_command(
                    &checker,
                    &root.join("workspace"),
                    &root.join("repo"),
                    Some(&root.join("rocq-switch")),
                    Duration::from_secs(5),
                    CheckMode::Full,
                )
                .output()
                .expect("execute sanitized fake checker")
            }
            "launcher" => {
                let artifacts = ArtifactWriter::new(Some(root.join("artifacts")))
                    .expect("create child artifact writer");
                let host_tmp = proof_agent_host_tmp_directory(&artifacts)
                    .expect("create case-local host temp root");
                let session_home = ProofAgentSessionHome::create(&artifacts)
                    .expect("create case-local session home under hostile TMPDIR");
                assert_eq!(session_home.path.parent(), Some(host_tmp.as_path()));
                let generation_home = session_home
                    .generation_path(1)
                    .expect("create case-local generation home");
                let round_stage = ProofAgentRoundStage::create(&artifacts)
                    .expect("create case-local round stage under hostile TMPDIR");
                assert_eq!(round_stage.path().parent(), Some(host_tmp.as_path()));
                proof_agent_launcher_command(
                    &script,
                    &root.join("repo"),
                    &root.join("workspace"),
                    &generation_home,
                    round_stage.path(),
                    &root.join("diagnostic/socket"),
                    &"b".repeat(64),
                    "logos-solver@sha256:test",
                    "codex exec test",
                    6_144,
                    2 * 1024 * 1024 * 1024,
                    Duration::from_secs(5),
                )
                .output()
                .expect("execute sanitized fake agent launcher")
            }
            unexpected => panic!("unexpected child mode {unexpected}"),
        };
        assert!(
            output.status.success(),
            "fake {mode:?} entry failed: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(
            !marker.exists(),
            "ambient BASH_ENV executed before {mode:?}"
        );
        let environment = String::from_utf8(output.stdout).expect("UTF-8 environment");
        for name in EXPLICITLY_EXCLUDED_HOST_ENVIRONMENT {
            assert!(
                !environment
                    .lines()
                    .any(|line| line.starts_with(&format!("{name}="))),
                "{name} reached the sanitized {mode:?} process"
            );
        }
        assert!(environment.lines().all(|line| {
            EXPLICITLY_EXCLUDED_HOST_ENVIRONMENT_PREFIXES
                .iter()
                .all(|prefix| !line.starts_with(prefix))
        }));
        assert!(environment.contains(&format!("LC_ALL={FIXED_HOST_LOCALE}\n")));
        assert!(environment.contains(&format!("LANG={FIXED_HOST_LOCALE}\n")));
        if mode == "checker" {
            assert!(environment.contains(&format!("PATH={TRUSTED_CHECKER_PATH}\n")));
            assert!(environment.contains(&format!("HOME={TRUSTED_CHECKER_HOME}\n")));
            assert!(!environment.contains("DOCKER_HOST="));
            assert!(!environment.contains("OPENAI_API_KEY="));
            assert!(!environment.contains("TMPDIR="));
        } else {
            assert!(environment.contains(&format!("PATH={PROOF_AGENT_LAUNCHER_PATH}\n")));
            assert!(!environment.contains("TMPDIR="));
            assert!(environment.contains("HOME=/ambient-home\n"));
            assert!(environment.contains("DOCKER_HOST=unix:///ambient-test.sock\n"));
            assert!(environment.contains("OPENAI_API_KEY=harmless-test-key\n"));
        }
        return;
    }

    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after Unix epoch")
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "logos-host-bash-environment-{}-{nonce}",
        std::process::id()
    ));
    std::fs::create_dir_all(&root).expect("create launch environment fixture");
    let bash_env = root.join("ambient-bash-env.sh");
    let marker = root.join("bash-env-executed");
    std::fs::write(
        &bash_env,
        format!("printf executed >>'{}'\n", marker.display()),
    )
    .expect("write BASH_ENV sentinel");
    let current_thread = std::thread::current();
    let test_name = current_thread.name().expect("test thread has a name");
    for mode in ["checker", "launcher"] {
        let _ = std::fs::remove_file(&marker);
        let output = Command::new(std::env::current_exe().expect("current test executable"))
            .arg("--exact")
            .arg(test_name)
            .arg("--nocapture")
            .env(CHILD_MODE, mode)
            .env("BASH_ENV", &bash_env)
            .env("ENV", &bash_env)
            .env("BASH_FUNC_find%%", "() { :; }")
            .env("SHELLOPTS", "braceexpand:hashall:interactive-comments")
            .env("BASHOPTS", "checkwinsize:cmdhist:complete_fullquote")
            .env("LD_PRELOAD", "")
            .env("LD_LIBRARY_PATH", "/ambient/ld-library-path")
            .env("OCAMLPATH", "/ambient/ocamlpath")
            .env("CAML_LD_LIBRARY_PATH", "/ambient/caml-ld-library-path")
            .env("CDPATH", "/ambient/cdpath")
            .env("TMPDIR", "/ambient/hostile-tmpdir")
            .env("HOME", "/ambient-home")
            .env("DOCKER_HOST", "unix:///ambient-test.sock")
            .env("OPENAI_API_KEY", "harmless-test-key")
            .output()
            .expect("re-execute launch environment regression");
        assert!(
            output.status.success(),
            "{mode} launch environment child failed\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(!marker.exists(), "{mode} sourced the ambient BASH_ENV");
    }
    std::fs::remove_dir_all(root).expect("remove launch environment fixture");
}

#[test]
fn authority_closure_is_source_backed_paired_and_digest_bound() {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after Unix epoch")
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "logos-authority-closure-{}-{nonce}",
        std::process::id()
    ));
    let repo = root.join("repo");
    let workdir = root.join("workdir");
    let theory = repo.join("theories/FormalSQL/General.v");
    let object = repo.join("theories/FormalSQL/General.vo");
    std::fs::create_dir_all(theory.parent().unwrap()).expect("create theory directory");
    std::fs::create_dir_all(&workdir).expect("create workdir");
    std::fs::write(&theory, b"Definition general : True := I.\n").expect("write source");
    std::fs::write(&object, b"synthetic-object-bytes").expect("write object");
    let manifest = format!(
        concat!(
            "# Logos proof-agent authority closure\n",
            "# schemaVersion: 1\n",
            "# policy: logos-proof-agent-source-object-closure-v1\n",
            "# sourcePairs: 1\n",
            "# stagedFiles: 2\n",
            "# sha256  workspace-relative-path\n",
            "# Only source-backed non-Example .v/.vo pairs are present.\n",
            "{}  theories/FormalSQL/General.v\n",
            "{}  theories/FormalSQL/General.vo\n"
        ),
        sha256_hex(&std::fs::read(&theory).unwrap()),
        sha256_hex(&std::fs::read(&object).unwrap())
    );
    std::fs::write(workdir.join("authority-closure.txt"), &manifest)
        .expect("write closure manifest");
    let binding = validate_authority_closure(&workdir, &repo).expect("validate closure");
    assert_eq!(binding.bytes, manifest.len());
    assert_eq!(binding.sha256, sha256_hex(manifest.as_bytes()));

    std::fs::write(&object, b"drifted-object").expect("drift object");
    let error = validate_authority_closure(&workdir, &repo)
        .expect_err("object drift must fail closed")
        .to_string();
    assert!(error.contains("digest drifted"));
    std::fs::remove_dir_all(root).expect("remove closure fixture");
}

#[test]
fn counterexample_handoff_is_strict_and_requires_actionable_text() {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after Unix epoch")
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "logos-proof-handoff-{}-{nonce}",
        std::process::id()
    ));
    std::fs::create_dir_all(&root).expect("create handoff directory");
    let path = root.join("counterexample-handoff.json");
    std::fs::write(
        &path,
        r#"{
          "decision": "counterexample_candidate",
          "reason": "the right side drops one duplicate",
          "guidance": "insert two identical rows into t"
        }"#,
    )
    .expect("write handoff");

    let (handoff, error) = load_counterexample_handoff(&root);
    assert!(error.is_none());
    let handoff = handoff.expect("parsed handoff");
    assert_eq!(
        handoff.decision,
        ProofAgentDecision::CounterexampleCandidate
    );
    assert!(handoff.counterexample_feedback().is_some());
    std::fs::write(
        &path,
        r#"{
          "decision": "needs_manual_review",
          "reason": "the trusted goal requires a stronger demand semantics",
          "guidance": "inspect the CTE execution contract"
        }"#,
    )
    .expect("write direct manual-review handoff");
    let (handoff, error) = load_counterexample_handoff(&root);
    assert!(error.is_none());
    let handoff = handoff.expect("parsed manual-review handoff");
    assert_eq!(handoff.decision, ProofAgentDecision::NeedsManualReview);
    assert!(handoff.counterexample_feedback().is_none());
    assert!(handoff.reason.contains("stronger demand semantics"));
    assert!(handoff.guidance.contains("CTE execution contract"));

    std::fs::write(
        &path,
        r#"{
          "decision": "counterexample_candidate",
          "reason": "",
          "guidance": "insert a row",
          "untrustedExtra": true
        }"#,
    )
    .expect("write invalid handoff");
    let (handoff, error) = load_counterexample_handoff(&root);
    assert!(handoff.is_none());
    assert!(error.is_some());
    std::fs::remove_dir_all(root).expect("remove handoff directory");
}

#[test]
fn conditional_source_classifier_accepts_only_direct_constructors() {
    let derived = "(* generated_precondition_source in a comment *)\n\
Definition generated_precondition_source :\n\
  Logos.FormalSQL.VerificationConditions.precondition_source :=\n\
  Logos.FormalSQL.VerificationConditions.PreconditionDerived.\n\
Theorem generated_precondition_valid :\n\
  generated_precondition_obligation generated_precondition_source generated_precondition.\n\
Proof. unfold generated_precondition_source. exact I. Qed.";
    let (source, finding) = classify_precondition_source("Problem.v", derived);
    assert_eq!(source, Some(PreconditionSource::Derived));
    assert!(finding.is_none());

    let external = "Definition generated_precondition_source :\n\
  Logos.FormalSQL.VerificationConditions.precondition_source :=\n\
  Logos.FormalSQL.VerificationConditions.PreconditionExternal.";
    let (source, finding) = classify_precondition_source("Problem.v", external);
    assert_eq!(source, Some(PreconditionSource::External));
    assert!(finding.is_none());

    let indirect = "Definition source_alias := PreconditionDerived.\n\
Definition generated_precondition_source :\n\
  Logos.FormalSQL.VerificationConditions.precondition_source := source_alias.";
    let (source, finding) = classify_precondition_source("Problem.v", indirect);
    assert!(source.is_none());
    assert!(finding.is_some());

    let shadowable = "Definition generated_precondition_source : precondition_source :=\n\
  Logos.FormalSQL.VerificationConditions.PreconditionDerived.";
    let (source, finding) = classify_precondition_source("Problem.v", shadowable);
    assert!(source.is_none());
    assert!(finding.is_some());
}

#[test]
fn unconditional_claim_classifier_accepts_only_direct_trusted_constructors() {
    let equivalence = "Definition generated_verification_claim :\n\
  Logos.FormalSQL.VerificationConditions.verification_claim_kind :=\n\
  Logos.FormalSQL.VerificationConditions.VerificationEquivalence.";
    let (claim, finding) = classify_verification_claim("Problem.v", equivalence);
    assert_eq!(claim, Some(VerificationClaimKind::Equivalence));
    assert!(finding.is_none());

    let countermodel = "Definition generated_verification_claim :\n\
  Logos.FormalSQL.VerificationConditions.verification_claim_kind :=\n\
  Logos.FormalSQL.VerificationConditions.VerificationCountermodel.";
    let (claim, finding) = classify_verification_claim("Problem.v", countermodel);
    assert_eq!(claim, Some(VerificationClaimKind::FormalCountermodel));
    assert!(finding.is_none());

    let indirect = "Definition claim_alias := VerificationCountermodel.\n\
Definition generated_verification_claim :\n\
  Logos.FormalSQL.VerificationConditions.verification_claim_kind := claim_alias.";
    let (claim, finding) = classify_verification_claim("Problem.v", indirect);
    assert!(claim.is_none());
    assert!(finding.is_some());

    let shadowable = "Definition generated_verification_claim : verification_claim_kind :=\n\
  Logos.FormalSQL.VerificationConditions.VerificationCountermodel.";
    let (claim, finding) = classify_verification_claim("Problem.v", shadowable);
    assert!(claim.is_none());
    assert!(finding.is_some());
}

#[test]
fn proof_audit_rejects_coercion_based_selector_reinterpretation() {
    let source = "Inductive counterfeit_claim_kind := CounterfeitClaim.\n\
Definition claim_to_counterfeit\n\
(_ : Logos.FormalSQL.VerificationConditions.verification_claim_kind)\n\
: counterfeit_claim_kind := CounterfeitClaim.\n\
Coercion claim_to_counterfeit :\n\
  Logos.FormalSQL.VerificationConditions.verification_claim_kind >->\n\
  counterfeit_claim_kind.\n\
Definition counterfeit_to_claim (_ : counterfeit_claim_kind)\n\
: Logos.FormalSQL.VerificationConditions.verification_claim_kind :=\n\
  Logos.FormalSQL.VerificationConditions.VerificationEquivalence.\n\
Coercion counterfeit_to_claim : counterfeit_claim_kind >->\n\
  Logos.FormalSQL.VerificationConditions.verification_claim_kind.\n\
Definition verification_claim_kind := counterfeit_claim_kind.\n\
Definition generated_verification_claim : verification_claim_kind :=\n\
  Logos.FormalSQL.VerificationConditions.VerificationCountermodel.";

    let findings = audit_rocq_text("Problem.v", source);
    assert_eq!(
        findings
            .iter()
            .filter(|finding| finding.token == "Coercion")
            .count(),
        2
    );
    let (claim, finding) = classify_verification_claim("Problem.v", source);
    assert!(claim.is_none());
    assert!(finding.is_some());
}

#[test]
fn every_host_generated_problem_scaffold_passes_the_problem_source_audit() {
    for mode in [
        VerificationMode::SafeUnconditional,
        VerificationMode::OutcomeUnconditional,
        VerificationMode::Conditional,
    ] {
        let generated = emit_rocq_query_expr_proof_module_for_mode(mode);
        let findings = audit_rocq_text("Problem.v", &generated.rocq_module);
        assert!(
            findings.is_empty(),
            "host-generated {mode:?} Problem.v failed its own source audit: {findings:?}"
        );
    }
}

#[test]
fn conditional_mode_rejects_an_unconditional_claim_selector() {
    let selector = "Definition generated_verification_claim :\n\
  Logos.FormalSQL.VerificationConditions.verification_claim_kind :=\n\
  Logos.FormalSQL.VerificationConditions.VerificationCountermodel.";
    let finding = reject_conditional_verification_claim("Problem.v", selector)
        .expect("conditional selector must be rejected");
    assert_eq!(finding.token, "generated_verification_claim");
    assert!(finding.excerpt.contains("forbids"));
    assert!(reject_conditional_verification_claim("Problem.v", "Definition x := 1.").is_none());
}

#[test]
fn conditional_audit_records_one_direct_precondition_definition() {
    let text = "Definition generated_precondition :\n\
  Logos.FormalSQL.VerificationConditions.verification_condition :=\n\
  ConditionAnd ConditionTrue ConditionTrue.\n\
Theorem use_precondition : generated_equivalence_goal generated_precondition.\n\
Proof. exact generated_queries_equivalent. Qed.";
    let (definition, finding) = extract_precondition_definition("Problem.v", text);
    assert_eq!(
        definition.as_deref(),
        Some(
            "Definition generated_precondition :\nLogos.FormalSQL.VerificationConditions.verification_condition :=\nConditionAnd ConditionTrue ConditionTrue."
        )
    );
    assert!(finding.is_none());

    let duplicate = format!(
        "{text}\nDefinition generated_precondition : Logos.FormalSQL.VerificationConditions.verification_condition := ConditionTrue."
    );
    let (definition, finding) = extract_precondition_definition("Problem.v", &duplicate);
    assert!(definition.is_none());
    assert!(finding.is_some());

    let shadowable = "Definition generated_precondition : verification_condition := ConditionTrue.";
    let (definition, finding) = extract_precondition_definition("Problem.v", shadowable);
    assert!(definition.is_none());
    assert!(finding.is_some());
}

#[test]
fn rocq_comment_stripping_preserves_strings_and_nested_line_numbers() {
    let text = "Definition label := \"(* literal *)\".\n\
(* outer\n  (* nested *)\n*)\n\
Definition generated_precondition_source :\n\
  Logos.FormalSQL.VerificationConditions.precondition_source :=\n\
  Logos.FormalSQL.VerificationConditions.PreconditionDerived.";
    let stripped = strip_rocq_comments(text);
    assert!(stripped.contains("\"(* literal *)\""));
    assert_eq!(stripped.lines().count(), text.lines().count());
    let (source, finding) = classify_precondition_source("Problem.v", text);
    assert_eq!(source, Some(PreconditionSource::Derived));
    assert!(finding.is_none());
}

#[test]
fn final_theorem_detection_requires_a_direct_uncommented_declaration() {
    let placeholder = "(* LOGOS_PROOF_HOLE: add\n\
      Theorem generated_queries_verified : generated_verification_goal claim.\n\
    *)";
    assert!(!problem_declares_final_theorem(
        placeholder,
        VerificationMode::OutcomeUnconditional,
    ));
    assert!(!problem_declares_final_theorem(
        "Definition reminder := \"Theorem generated_queries_verified\".",
        VerificationMode::OutcomeUnconditional,
    ));
    assert!(!problem_declares_final_theorem(
        "Lemma generated_queries_verified : generated_verification_goal claim.",
        VerificationMode::OutcomeUnconditional,
    ));
    assert!(problem_declares_final_theorem(
        "Theorem generated_queries_verified : generated_verification_goal claim.\n\
         Proof. exact I. Qed.",
        VerificationMode::OutcomeUnconditional,
    ));
    assert!(problem_declares_final_theorem(
        "Theorem generated_queries_equivalent : generated_equivalence_goal condition.\n\
         Proof. exact I. Qed.",
        VerificationMode::Conditional,
    ));
}

#[test]
fn trusted_rocq_registry_metadata_is_complete() {
    for (index, import) in TRUSTED_ROCQ_IMPORTS.iter().enumerate() {
        assert!(
            !TRUSTED_ROCQ_IMPORTS[..index]
                .iter()
                .any(|prior| prior.root == import.root && prior.module == import.module),
            "duplicate trusted Rocq module {}",
            import.module,
        );
        assert!(import.proof_import_order.is_some());
        if import.root == TrustedRocqRoot::Logos {
            assert!(import.object_check_order.is_some());
            assert!(import.make_build_order.is_some());
        } else {
            assert!(import.object_check_order.is_none());
            assert!(import.make_build_order.is_none());
        }
    }
    for root in TRUSTED_ROCQ_IMPORT_ROOTS {
        assert_contiguous_ranks(
            TRUSTED_ROCQ_IMPORTS
                .iter()
                .filter(|import| import.root == root.root)
                .filter_map(|import| import.proof_import_order)
                .collect(),
        );
    }
    assert_contiguous_ranks(
        TRUSTED_ROCQ_IMPORTS
            .iter()
            .filter_map(|import| import.object_check_order)
            .collect(),
    );
    assert_contiguous_ranks(
        TRUSTED_ROCQ_IMPORTS
            .iter()
            .filter_map(|import| import.make_build_order)
            .collect(),
    );
}

#[test]
fn trusted_rocq_registry_matches_allowlist_shell_and_makefile() {
    let derived_allowlist = TRUSTED_PROBLEM_IMPORT_LINES.join("\n");
    for root in TRUSTED_ROCQ_IMPORT_ROOTS {
        let prefix = format!("From {} Require Import ", root.qualifier);
        let direct_imports = ordered_direct_trusted_rocq_imports(root.root)
            .into_iter()
            .map(str::to_owned)
            .collect::<Vec<_>>();
        assert_eq!(
            modules_from_import_line(&derived_allowlist, &prefix),
            direct_imports,
            "proof-stage allowlist drifted for {}",
            root.qualifier,
        );
    }
    assert_eq!(
        shell_checked_theory_objects(),
        ordered_theory_paths(|import| import.object_check_order, "vo"),
    );
    assert_eq!(
        makefile_compiled_theories(),
        ordered_theory_paths(|import| import.make_build_order, "v"),
    );
}

#[test]
fn proof_agent_container_does_not_run_the_final_trusted_check() {
    assert!(FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("LOGOS_PROOF_AGENT_COMMAND"));
    assert!(FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("LOGOS_PROOF_AGENT_CODEX_HOME"));
    assert!(FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("LOGOS_PROOF_WORKDIR"));
    assert!(FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("-v \"$WORKDIR\":/seed/context:ro"));
    assert!(FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("search-rocq-declarations.py"));
    assert!(!FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("/workspace/problem/lemma-catalog"));
    assert!(FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("-v \"$LOGOS_REPO_ROOT\":/workspace/logos:ro"));
    assert!(
        !FORMAL_SQL_DOCKER_AGENT_SCRIPT
            .contains("\"$LOGOS_REPO_ROOT/vendor/FormalSQL\":/workspace/logos/vendor/FormalSQL:ro")
    );
    assert!(
        !FORMAL_SQL_DOCKER_AGENT_SCRIPT
            .contains("\"$LOGOS_REPO_ROOT/theories\":/workspace/logos/theories:ro")
    );
    assert!(FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("AUTHORITY-CLOSURE.txt"));
    assert!(FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("authority-closure.txt"));
    let first_closure_publish = FORMAL_SQL_DOCKER_AGENT_SCRIPT
        .find("publish_authority_closure || exit 2")
        .expect("pre-agent authority closure publication");
    let docker_run = FORMAL_SQL_DOCKER_AGENT_SCRIPT
        .find("docker run \"${docker_args[@]}\"")
        .expect("untrusted Docker run");
    let final_closure_publish = FORMAL_SQL_DOCKER_AGENT_SCRIPT
        .rfind("publish_authority_closure || exit 2")
        .expect("post-agent authority closure publication");
    assert!(first_closure_publish < docker_run);
    assert!(docker_run < final_closure_publish);
    assert!(FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("LOGOS_PROOF_DIAGNOSTIC_SOCKET"));
    assert!(
        FORMAL_SQL_DOCKER_AGENT_SCRIPT
            .contains("-v \"$DIAGNOSTIC_SOCKET_DIR\":/seed/diagnostic:ro")
    );
    assert!(
        FORMAL_SQL_DOCKER_AGENT_SCRIPT
            .contains("LOGOS_PROOF_DIAGNOSTIC_SOCKET=/seed/diagnostic/socket")
    );
    assert!(
        !FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("LOGOS_PROOF_DIAGNOSTIC_SOCKET=/seed/problem")
    );
    assert!(FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("LOGOS_PROOF_DIAGNOSTIC_NONCE"));
    assert!(FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("$AGENT_STAGE/scratch"));
    assert!(FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("--read-only"));
    assert!(FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("--tmpfs \"/workspace:rw"));
    assert!(FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("--log-driver none"));
    assert!(FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("LOGOS_PROOF_AGENT_STORAGE_LIMIT_BYTES"));
    assert!(!FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("${TMPDIR:-/tmp}"));
    assert!(!FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("/tmp/logos-proof"));
    assert!(
        FORMAL_SQL_DOCKER_AGENT_SCRIPT
            .contains("HOST_STAGE_PREFIX=\"$AGENT_STAGE_PARENT/.${AGENT_STAGE_BASENAME}\"")
    );
    for allocation in [
        "CONTAINER_CID_FILE=\"${HOST_STAGE_PREFIX}.container.cid\"",
        "AUTHORITY_STAGE=\"$(mktemp -d \"${HOST_STAGE_PREFIX}.authority.XXXXXX\")\"",
        "EXPORT_STAGE=\"$(mktemp -d \"${HOST_STAGE_PREFIX}.export.XXXXXX\")\"",
        "HANDOFF_STAGE=\"$(mktemp -d \"${HOST_STAGE_PREFIX}.handoff.XXXXXX\")\"",
        "DOCKER_STDOUT=\"$(mktemp \"${HOST_STAGE_PREFIX}.docker-stdout.XXXXXX\")\"",
        "DOCKER_STDERR=\"$(mktemp \"${HOST_STAGE_PREFIX}.docker-stderr.XXXXXX\")\"",
    ] {
        assert!(
            FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains(allocation),
            "launcher host state is not case-local: {allocation}"
        );
    }
    assert!(
        FORMAL_SQL_DOCKER_AGENT_SCRIPT
            .contains("publish_stage_file \"$AGENT_STAGE/Problem.v\" \"$WORKDIR/Problem.v\"")
    );
    assert!(!FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("publish_stage_file \"$AGENT_STAGE/scratch"));
    assert!(!FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("LOGOS_TRUSTED_ROCQ_CACHE_DIR"));
    assert!(!FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("checker-invocations.jsonl"));
    assert!(!FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("$AGENT_STAGE\":/workspace/problem:rw"));
    assert!(!FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("$CODEX_HOME_STAGE\":/codex-home:rw"));
    assert!(FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("extract_agent_archive"));
    assert!(FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains(
        "HANDOFF_FILE_LIMIT_KIB=$(((LOGOS_PROOF_AGENT_STORAGE_LIMIT_BYTES + 1023) / 1024))"
    ));
    assert!(
        FORMAL_SQL_DOCKER_AGENT_SCRIPT
            .contains("HANDOFF_MEMBER_LIMIT=$((LOGOS_PROOF_AGENT_STORAGE_LIMIT_BYTES / 4096))")
    );
    assert!(
        FORMAL_SQL_DOCKER_AGENT_SCRIPT
            .contains("ulimit -f \"$LOGOS_PROOF_AGENT_HANDOFF_FILE_LIMIT_KIB\"")
    );
    assert!(
        FORMAL_SQL_DOCKER_AGENT_SCRIPT
            .contains("proof-agent export exceeds its aggregate filesystem-object quota")
    );
    assert!(FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("-v \"$HANDOFF_INCOMING\":/handoff-export:rw"));
    assert!(FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("chown 0:0 /handoff-export"));
    assert!(FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("trap release_handoff_on_exit EXIT"));
    assert!(FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("local saved_status=\"$?\""));
    let exit_trap = FORMAL_SQL_DOCKER_AGENT_SCRIPT
        .split("release_handoff_on_exit() {")
        .nth(1)
        .and_then(|tail| tail.split("}\ntrap release_handoff_on_exit EXIT").next())
        .expect("handoff ownership restoration trap body");
    let trap_kill = exit_trap
        .find("pkill -KILL -u \"$LOGOS_PROOF_AGENT_UID\"")
        .expect("untrusted uid termination in handoff exit trap");
    let trap_release = exit_trap
        .find("chown \"$LOGOS_PROOF_AGENT_UID:$LOGOS_PROOF_AGENT_GID\"")
        .expect("handoff ownership restoration in exit trap");
    assert!(trap_kill < trap_release);
    assert!(
        FORMAL_SQL_DOCKER_AGENT_SCRIPT
            .contains("chown \"$LOGOS_PROOF_AGENT_UID:$LOGOS_PROOF_AGENT_GID\"")
    );
    assert!(FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("! -s \"$HANDOFF_INCOMING\""));
    assert!(
        FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("\"$(stat -c '%s' \"$HANDOFF_INCOMING\")\" -gt")
    );
    assert!(
        FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("\"$(stat -c '%a' \"$HANDOFF_INCOMING\")\" != 600")
    );
    assert!(
        FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("mv -T \"$HANDOFF_INCOMING\" \"$HANDOFF_ARCHIVE\"")
    );
    assert!(
        FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("extract_agent_archive \\\n  \"$HANDOFF_ARCHIVE\"")
    );
    assert!(!FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("-cf -"));
    assert!(!FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("2>\"$DOCKER_STDERR\" |"));
    let protect_handoff = FORMAL_SQL_DOCKER_AGENT_SCRIPT
        .find("chown 0:0 /handoff-export")
        .expect("root protects handoff before the agent starts");
    let drop_privileges = FORMAL_SQL_DOCKER_AGENT_SCRIPT
        .find("setpriv \\")
        .expect("untrusted uid launch");
    let agent_completed = FORMAL_SQL_DOCKER_AGENT_SCRIPT
        .find("status=$?")
        .expect("untrusted agent completion boundary");
    let kill_untrusted = FORMAL_SQL_DOCKER_AGENT_SCRIPT[agent_completed..]
        .find("pkill -KILL -u \"$LOGOS_PROOF_AGENT_UID\"")
        .map(|offset| agent_completed + offset)
        .expect("post-agent untrusted uid termination");
    let discard_ephemeral_codex_helpers = FORMAL_SQL_DOCKER_AGENT_SCRIPT
        .find("rm -rf -- /workspace/codex-home/tmp")
        .expect("ephemeral Codex helper cleanup");
    let write_handoff = FORMAL_SQL_DOCKER_AGENT_SCRIPT
        .find("-C /workspace -cf /handoff-export")
        .expect("protected file handoff");
    let install_exit_trap = FORMAL_SQL_DOCKER_AGENT_SCRIPT
        .find("trap release_handoff_on_exit EXIT")
        .expect("handoff ownership restoration trap");
    assert!(protect_handoff < drop_privileges);
    assert!(protect_handoff < install_exit_trap);
    assert!(install_exit_trap < drop_privileges);
    assert!(drop_privileges < kill_untrusted);
    assert!(kill_untrusted < discard_ephemeral_codex_helpers);
    assert!(discard_ephemeral_codex_helpers < write_handoff);
    assert!(kill_untrusted < write_handoff);
    assert!(FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains(
        "publish_stage_file \"$EXPORT_STAGE/agent-stdout\" \"$AGENT_STAGE/agent-stdout\""
    ));
    assert!(FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains(
        "publish_stage_file \"$EXPORT_STAGE/agent-stderr\" \"$AGENT_STAGE/agent-stderr\""
    ));
    assert!(!FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("cat \"$EXPORT_STAGE/agent-stdout\""));
    assert!(!FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("cat \"$EXPORT_STAGE/agent-stderr\""));
    assert!(FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("-u LOGOS_UNTRUSTED_AGENT_CHECK"));
    assert!(
        FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("--memory \"$LOGOS_PROOF_AGENT_MEMORY_LIMIT\"")
    );
    assert!(FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("counterexample-handoff.json"));
    assert!(FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("forbidden proof-agent problem export path"));
    let handoff_members = FORMAL_SQL_DOCKER_AGENT_SCRIPT
        .split("-C /workspace -cf /handoff-export")
        .nth(1)
        .and_then(|tail| tail.split("\n)").next())
        .expect("agent handoff tar member list");
    assert!(handoff_members.contains("problem/Problem.v"));
    assert!(handoff_members.contains("problem/scratch"));
    assert!(!handoff_members.contains("ProofModules"));
    assert!(!handoff_members.contains(".vo"));
    assert!(
        FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("-v \"$CODEX_HOME_STAGE\":/seed/codex-home:ro")
    );
    assert!(FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("LOGOS_SOLVER_CODEX_CONFIG"));
    assert!(
        FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains(
            "rm -rf -- \"$dst/config.toml\" \"$dst/auth.json\" \"$dst/credentials.json\""
        )
    );
    assert!(
        FORMAL_SQL_DOCKER_AGENT_SCRIPT
            .contains("failed to stage the isolated proof-agent Codex home")
    );
    assert!(
        !FORMAL_SQL_DOCKER_AGENT_SCRIPT
            .contains("for env_name in OPENAI_API_KEY CODEX_API_KEY OPENAI_BASE_URL")
    );
    assert!(!FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("&& bash run-rocq-check.sh"));
    assert!(FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT.contains("LOGOS_TRUSTED_ROCQ_CACHE_DIR"));
    assert!(FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT.contains("diagnostic-cache-source"));
    assert!(
        FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT
            .contains("sha256sum Schema.v Schema.vo Queries.v Queries.vo")
    );
    assert!(FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT.contains("\"$ROCQ_BIN\" check -silent -o"));
    for generated in ["Schema", "Queries", "Witness", "Problem", "Goal"] {
        assert!(
            FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT
                .contains(&format!("-norec LogosGenerated.{generated}"))
        );
    }
    let final_mode_block = FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT
        .split("if [[ \"$mode\" == final ]]; then")
        .nth(1)
        .and_then(|tail| tail.split("\nfi\n").next())
        .expect("final trusted-check mode block");
    assert!(final_mode_block.contains("copy_trusted_cache_objects \"$PROBLEMOUTDIR\""));
    assert!(!final_mode_block.contains("sandbox_compile"));
    let final_kernel_check = FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT
        .rsplit_once("\"$ROCQ_BIN\" check -silent -o")
        .map(|(_, tail)| tail)
        .expect("final kernel check");
    for generated in ["Schema", "Queries", "Witness"] {
        assert!(!final_kernel_check.contains(&format!("-norec LogosGenerated.{generated}")));
    }
    assert!(final_kernel_check.contains("\"${module_check_arguments[@]}\""));
    assert!(final_kernel_check.contains("-norec LogosGenerated.Problem"));
    assert!(final_kernel_check.contains("-norec LogosGenerated.Goal"));
    assert!(
        !FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT
            .contains("From LogosGenerated Require Import Schema Queries Witness.")
    );
    assert!(FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT.contains("LogosGenerated\\."));
    assert!(FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT.contains("unsafe (co)fixpoints: <none>"));
    assert!(!FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT.contains("--ro-bind / /"));
    assert!(FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT.contains("--tmpfs /"));
    assert!(FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT.contains("--clearenv"));
    assert!(FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT.contains("/authority"));
    assert!(FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT.contains("$AUTHORITYDIR"));
    assert!(FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT.contains("$OSLIBDIR"));
    assert!(FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT.contains("--ro-bind \"$input_root\" /input"));
    assert!(FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT.contains("--bind \"$output_root\" /out"));
    assert!(FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT.contains("-noglob"));
    assert!(FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT.contains("-top \"$logical_name\""));
    assert!(FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT.contains("LogosGenerated.Problem Problem.vo"));
    assert!(FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT.contains("LogosGenerated.ProofModules.$stem"));
    assert!(FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT.contains("copy_trusted_cache_objects"));
    assert!(FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT.contains("$GOALDIR/Goal.v"));
    assert!(FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT.contains("--unshare-all"));
    assert!(FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT.contains("--unshare-user"));
    assert!(FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT.contains("--disable-userns"));
    assert!(FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT.contains("--assert-userns-disabled"));
    assert!(FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT.contains("$GOALDIR/Goal.v"));
    assert!(!FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT.contains("Examples.vo"));
    assert!(FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT.contains("[[ ! -s \"$file\" ]]"));
    assert!(!FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("run-trusted-rocq-check.sh"));
    assert!(!FORMAL_SQL_ROCQ_CHECK_REQUEST_SCRIPT.contains("rocq check"));
}

#[test]
fn module_cache_staging_requires_successful_compilation() {
    let preparation = FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT
        .split("elif [[ \"$mode\" == module-diagnostic ]]; then")
        .nth(1)
        .and_then(|tail| tail.split("\n  else\n").next())
        .expect("module diagnostic preparation");
    assert!(preparation.contains("copy_trusted_cache_objects \"$PROBLEMOUTDIR\""));
    assert!(!preparation.contains("CACHE_STAGE"));
    assert!(!preparation.contains("copy_trusted_cache \""));

    let publication = FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT
        .split_once("\nif [[ \"$mode\" == module-diagnostic ]]; then\n")
        .map(|(_, tail)| tail.split("\nfi\n").next().unwrap())
        .expect("module compile and publication block");
    // Execute the actual branch under errexit. Stop at the copy boundary on
    // success; the real sandbox regression covers the subsequent publication.
    let harness = format!(
        r#"set -euo pipefail
sandbox_compile() {{ printf 'compile\n'; return "$COMPILE_STATUS"; }}
copy_trusted_cache() {{ printf 'stage\n'; return 73; }}
if [[ "$mode" == module-diagnostic ]]; then
{publication}
fi
"#
    );
    for compile_status in [1, 124, 143, 0] {
        let root = tempfile::tempdir().expect("create module staging fixture");
        let output = Command::new("/usr/bin/bash")
            .arg("-c")
            .arg(&harness)
            .env_clear()
            .env("PATH", "/usr/bin:/bin")
            .env("mode", "module-diagnostic")
            .env("COMPILE_STATUS", compile_status.to_string())
            .env("CACHE_PARENT", root.path())
            .env("PROBLEMDIR", root.path().join("input"))
            .env("PROBLEMOUTDIR", root.path().join("output"))
            .env("module_candidate", "ProofModules/Facts.v")
            .env("candidate_stem", "Facts")
            .output()
            .expect("run module staging branch");
        assert_eq!(
            output.status.code(),
            Some(if compile_status == 0 {
                73
            } else {
                compile_status
            }),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(
            output.stdout,
            if compile_status == 0 {
                b"compile\nstage\n".as_slice()
            } else {
                b"compile\n".as_slice()
            }
        );
        assert_eq!(
            std::fs::read_dir(root.path()).unwrap().count(),
            usize::from(compile_status == 0),
            "unsuccessful compilation must not allocate a publication directory"
        );
    }
}

#[test]
fn interrupted_module_cache_swap_restores_the_last_valid_cache_first() {
    let function_tail = FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT
        .split("cleanup_trusted_checker() {")
        .nth(1)
        .expect("trusted checker cleanup function");
    let function_end = function_tail
        .find("\n}\ntrap cleanup_trusted_checker EXIT")
        .expect("trusted checker cleanup terminator");
    let cleanup_function = format!(
        "cleanup_trusted_checker() {{{}\n}}",
        &function_tail[..function_end]
    );
    assert!(cleanup_function.contains("set +e"));
    let restore = cleanup_function
        .find("mv -T \"$CACHE_OLD\" \"$TRUSTED_CACHE\"")
        .expect("cache restore command");
    let stage_cleanup = cleanup_function
        .find("rm -rf -- \"$CACHE_STAGE\"")
        .expect("cache-stage cleanup command");
    assert!(restore < stage_cleanup);

    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after Unix epoch")
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "logos-cache-swap-recovery-{}-{nonce}",
        std::process::id()
    ));
    let host_tmp = root.join("host-tmp");
    let check_dir = host_tmp.join("trusted-rocq-check.interrupted");
    let cache_stage = root.join(".logos-trusted-diagnostic-cache.pending");
    let cache_old = root.join(".logos-trusted-diagnostic-cache-old.valid");
    let trusted_cache = root.join("cache");
    for directory in [&check_dir, &cache_stage, &cache_old] {
        std::fs::create_dir_all(directory).expect("create recovery fixture directory");
    }
    std::fs::write(cache_old.join("VALID"), "last valid cache\n")
        .expect("write valid old-cache marker");
    let harness = format!(
        "set -euo pipefail\n{cleanup_function}\ntrap cleanup_trusted_checker EXIT\nexit 143\n"
    );
    let output = Command::new("/usr/bin/bash")
        .arg("-c")
        .arg(harness)
        .env_clear()
        .env("PATH", "/usr/bin:/bin")
        .env("HOST_TMP_ROOT", &host_tmp)
        .env("CHECKDIR", &check_dir)
        .env("CACHE_PARENT", &root)
        .env("CACHE_STAGE", &cache_stage)
        .env("CACHE_OLD", &cache_old)
        .env("CACHE_PUBLISHED", "false")
        .env("TRUSTED_CACHE", &trusted_cache)
        .output()
        .expect("run exact cache-recovery cleanup function");
    assert_eq!(output.status.code(), Some(143));
    assert_eq!(
        std::fs::read_to_string(trusted_cache.join("VALID")).expect("read restored cache marker"),
        "last valid cache\n"
    );
    assert!(!cache_old.exists());
    assert!(!cache_stage.exists());
    assert!(!check_dir.exists());

    let obstructed_check_dir = host_tmp.join("trusted-rocq-check.obstructed");
    let obstructed_stage = root.join(".logos-trusted-diagnostic-cache.obstructed");
    let obstructed_old = root.join(".logos-trusted-diagnostic-cache-old.retained");
    let obstruction = root.join("cache-obstructed");
    for directory in [
        &obstructed_check_dir,
        &obstructed_stage,
        &obstructed_old,
        &obstruction,
    ] {
        std::fs::create_dir_all(directory).expect("create obstructed recovery fixture");
    }
    std::fs::write(obstructed_old.join("VALID"), "only valid cache\n")
        .expect("write retained old-cache marker");
    std::fs::write(obstruction.join("UNPUBLISHED"), "not the replacement\n")
        .expect("write publication obstruction");
    let obstructed_output = Command::new("/usr/bin/bash")
        .arg("-c")
        .arg(format!(
            "set -euo pipefail\n{cleanup_function}\ntrap cleanup_trusted_checker EXIT\nexit 143\n"
        ))
        .env_clear()
        .env("PATH", "/usr/bin:/bin")
        .env("HOST_TMP_ROOT", &host_tmp)
        .env("CHECKDIR", &obstructed_check_dir)
        .env("CACHE_PARENT", &root)
        .env("CACHE_STAGE", &obstructed_stage)
        .env("CACHE_OLD", &obstructed_old)
        .env("CACHE_PUBLISHED", "false")
        .env("TRUSTED_CACHE", &obstruction)
        .output()
        .expect("run obstructed cache-recovery cleanup function");
    assert_eq!(obstructed_output.status.code(), Some(143));
    assert_eq!(
        std::fs::read_to_string(obstructed_old.join("VALID"))
            .expect("read retained valid old cache"),
        "only valid cache\n"
    );
    assert!(obstruction.join("UNPUBLISHED").is_file());
    assert!(!obstructed_stage.exists());
    assert!(!obstructed_check_dir.exists());

    let published_check_dir = host_tmp.join("trusted-rocq-check.post-publish-signal");
    let published_stage = root.join(".logos-trusted-diagnostic-cache.moved-away");
    let published_old = root.join(".logos-trusted-diagnostic-cache-old.superseded");
    let published_live = root.join("cache-published");
    for directory in [&published_check_dir, &published_old, &published_live] {
        std::fs::create_dir_all(directory).expect("create post-publication fixture");
    }
    std::fs::write(published_old.join("OLD"), "old cache\n")
        .expect("write superseded cache marker");
    std::fs::write(published_live.join("NEW"), "published cache\n")
        .expect("write published cache marker");
    assert!(!published_stage.exists());
    let published_output = Command::new("/usr/bin/bash")
        .arg("-c")
        .arg(format!(
            "set -euo pipefail\n{cleanup_function}\ntrap cleanup_trusted_checker EXIT\nexit 143\n"
        ))
        .env_clear()
        .env("PATH", "/usr/bin:/bin")
        .env("HOST_TMP_ROOT", &host_tmp)
        .env("CHECKDIR", &published_check_dir)
        .env("CACHE_PARENT", &root)
        .env("CACHE_STAGE", &published_stage)
        .env("CACHE_OLD", &published_old)
        .env("CACHE_PUBLISHED", "false")
        .env("TRUSTED_CACHE", &published_live)
        .output()
        .expect("run post-publication signal recovery");
    assert_eq!(published_output.status.code(), Some(0));
    assert_eq!(
        std::fs::read_to_string(published_live.join("NEW")).expect("read published cache marker"),
        "published cache\n"
    );
    assert!(!published_old.exists());
    assert!(!published_check_dir.exists());
    std::fs::remove_dir_all(root).expect("remove cache recovery fixture");
}

#[test]
fn next_checker_invocation_recovers_an_uncatchable_mid_swap_exit() {
    let function_tail = FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT
        .split("recover_interrupted_cache_swap() {")
        .nth(1)
        .expect("trusted checker startup recovery function");
    let function_end = function_tail
        .find("\n}\nrecover_interrupted_cache_swap")
        .expect("trusted checker startup recovery terminator");
    let recovery_function = format!(
        "recover_interrupted_cache_swap() {{{}\n}}",
        &function_tail[..function_end]
    );
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after Unix epoch")
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "logos-hard-exit-cache-recovery-{}-{nonce}",
        std::process::id()
    ));
    let old = root.join(".logos-trusted-diagnostic-cache-old.interrupted");
    let stage = root.join(".logos-trusted-diagnostic-cache.unpublished");
    let live = root.join("cache");
    std::fs::create_dir_all(&old).expect("create interrupted old cache");
    std::fs::create_dir_all(&stage).expect("create interrupted staged cache");
    std::fs::write(old.join("VALID"), "last valid cache\n")
        .expect("write interrupted old-cache marker");
    std::fs::write(stage.join("UNPUBLISHED"), "unpublished cache\n")
        .expect("write interrupted stage marker");
    let harness = format!(
        "set -euo pipefail\ntrusted_environment_failure() {{ exit 86; }}\n{recovery_function}\nrecover_interrupted_cache_swap\n"
    );
    let output = Command::new("/usr/bin/bash")
        .arg("-c")
        .arg(harness)
        .env_clear()
        .env("PATH", "/usr/bin:/bin")
        .env("CACHE_PARENT", &root)
        .env("TRUSTED_CACHE", &live)
        .output()
        .expect("run startup cache recovery");
    assert!(
        output.status.success(),
        "startup recovery failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        std::fs::read_to_string(live.join("VALID")).expect("read recovered live cache"),
        "last valid cache\n"
    );
    assert!(!old.exists());
    assert!(!stage.exists());

    let discard_tail = FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT
        .split("discard_superseded_cache_backups() {")
        .nth(1)
        .expect("trusted checker stale-backup cleanup function");
    let discard_end = discard_tail
        .find("\n}\n\nif [[ -L \"$TRUSTED_CACHE\"")
        .expect("trusted checker stale-backup cleanup terminator");
    let discard_function = format!(
        "discard_superseded_cache_backups() {{{}\n}}",
        &discard_tail[..discard_end]
    );
    let superseded = root.join(".logos-trusted-diagnostic-cache-old.superseded");
    std::fs::create_dir(&superseded).expect("create superseded cache backup");
    let discard_output = Command::new("/usr/bin/bash")
        .arg("-c")
        .arg(format!(
            "set -euo pipefail\ntrusted_environment_failure() {{ exit 86; }}\n{discard_function}\ndiscard_superseded_cache_backups\n"
        ))
        .env_clear()
        .env("PATH", "/usr/bin:/bin")
        .env("CACHE_PARENT", &root)
        .output()
        .expect("discard backup after validating live cache");
    assert!(discard_output.status.success());
    assert!(!superseded.exists());

    let second_old = root.join(".logos-trusted-diagnostic-cache-old.second-interruption");
    let second_stage = root.join(".logos-trusted-diagnostic-cache.second-unpublished");
    std::fs::rename(&live, &second_old).expect("simulate a second interrupted swap");
    std::fs::create_dir(&second_stage).expect("create second unpublished stage");
    let second_output = Command::new("/usr/bin/bash")
        .arg("-c")
        .arg(format!(
            "set -euo pipefail\ntrusted_environment_failure() {{ exit 86; }}\n{recovery_function}\nrecover_interrupted_cache_swap\n"
        ))
        .env_clear()
        .env("PATH", "/usr/bin:/bin")
        .env("CACHE_PARENT", &root)
        .env("TRUSTED_CACHE", &live)
        .output()
        .expect("run second startup cache recovery");
    assert!(second_output.status.success());
    assert!(live.join("VALID").is_file());
    assert!(!second_old.exists());
    assert!(!second_stage.exists());
    std::fs::remove_dir_all(root).expect("remove startup recovery fixture");
}

#[test]
fn proof_agent_diagnostic_wrapper_requires_strict_v2_mode_path_and_purpose() {
    for required in [
        "--mode <problem|module|scratch>",
        "--candidate <Problem.v|ProofModules/Name.v|scratch/*.v>",
        "--purpose <static-obligation|semantic-equivalence|assembly>",
        "\"schemaVersion\": 2",
        "\"candidatePath\": candidate_path",
        "\"purpose\": purpose",
        "result.get(\"compilePassed\") is True",
        "result.get(\"problemCompilePassed\") is True",
        "result.get(\"compileCheckpointAdvanced\") is True",
    ] {
        assert!(
            FORMAL_SQL_ROCQ_CHECK_REQUEST_SCRIPT.contains(required),
            "diagnostic wrapper is missing {required:?}"
        );
    }
    assert!(FORMAL_SQL_ROCQ_CHECK_REQUEST_SCRIPT.contains(
        "result.get(\"compilePassed\") is True or probe_passed or result.get(key) is not None"
    ));
    assert!(
        FORMAL_SQL_ROCQ_CHECK_REQUEST_SCRIPT
            .contains("f\"{mode} compile was incorrectly classified as a Problem.v checkpoint\"")
    );
    assert!(
        !FORMAL_SQL_ROCQ_CHECK_REQUEST_SCRIPT
            .contains("bash run-rocq-check.sh --timeout-seconds 30")
    );
    for required in [
        "State the SQL rewrite in one sentence",
        "scratch/proof-plan.md",
        "route-revision: 1",
        "current-residual: initial-top-level",
        "active-node: root",
        "## Root assembly",
        "## Obligation DAG",
        "## Active node",
        "compile-clean composition theorem",
        "--mode scratch",
        "--candidate scratch/ProofModules/CoreBridge.v",
        "--candidate scratch/probe.v",
        "no copy to",
        "second module check is needed",
        "--purpose semantic-equivalence",
        "--mode problem",
        "--candidate Problem.v",
        "operator-level",
        "rebuilding evaluator recursion",
        "instantiate it in `Problem.v`",
        "search-rocq-declarations.py",
        "Filters are mechanical and conjunctive",
        "Prove wide SELECT-list membership",
        "whose attribute or row is symbolic",
        "`vm_compute in H`",
        "`native_compute`/`native_decide`",
        "`ordered-signatures.json`",
        "explicit pages with a reported total",
        "necessary, not sufficient",
        "`create_goal`, `update_goal`",
        "ProofModules/<UppercaseRocqIdentifier>.v",
        "LogosGenerated.ProofModules.<Name>",
        "--mode module",
        "only modules that passed earlier",
        "fresh module name",
        "immutable dependency",
        "without recompiling their proofs",
        "container handoff never publishes that directory",
        "is not progress",
        "30--90 seconds",
        "120--180 seconds",
        "two or three minutes",
        "quota on local diagnostics",
        "Logos.FormalSQL.VerificationConditions.verification_claim_kind",
        "Logos.FormalSQL.VerificationConditions.verification_condition",
        "Logos.FormalSQL.VerificationConditions.precondition_source",
    ] {
        assert!(
            FORMAL_SQL_PROOF_AGENT_PROMPT.contains(required),
            "proof-agent prompt is missing {required:?}"
        );
    }
    assert!(!FORMAL_SQL_PROOF_AGENT_PROMPT.contains("bash run-rocq-check.sh --timeout-seconds 30"));
}

#[test]
#[ignore = "requires Unix socket creation, unavailable in restricted test sandboxes"]
fn proof_agent_diagnostic_wrapper_sends_and_checks_strict_v2_identity() {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after Unix epoch")
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "logos-diagnostic-wrapper-test-{}-{nonce}",
        std::process::id()
    ));
    std::fs::create_dir_all(root.join("scratch")).expect("create wrapper scratch tree");
    let script = root.join("run-rocq-check.sh");
    std::fs::write(&script, FORMAL_SQL_ROCQ_CHECK_REQUEST_SCRIPT)
        .expect("write diagnostic wrapper");
    let candidate = b"Lemma wrapper_subgoal : True. Proof. exact I. Qed.\n";
    std::fs::write(root.join("scratch/core.v"), candidate).expect("write wrapper candidate");
    let socket_path = root.join("broker.sock");
    let listener = UnixListener::bind(&socket_path).expect("bind fake wrapper broker");
    let broker = std::thread::spawn(move || {
        let (mut stream, _) = listener.accept().expect("accept wrapper request");
        let mut request_bytes = Vec::new();
        let mut block = [0u8; 512];
        while !request_bytes.contains(&b'\n') {
            let count = stream.read(&mut block).expect("read wrapper request");
            assert!(count > 0, "wrapper closed before its request newline");
            request_bytes.extend_from_slice(&block[..count]);
        }
        let newline = request_bytes
            .iter()
            .position(|byte| *byte == b'\n')
            .expect("wrapper request newline");
        let request: serde_json::Value =
            serde_json::from_slice(&request_bytes[..newline]).expect("parse wrapper request");
        let response = serde_json::json!({
            "schemaVersion": 2,
            "sequence": 1,
            "mode": request["mode"],
            "candidatePath": request["candidatePath"],
            "purpose": request["purpose"],
            "candidateSha256": request["candidateSha256"],
            "compilePassed": true,
            "problemCompilePassed": false,
            "compileCheckpointAdvanced": false,
            "exitCode": 0,
            "timedOut": false,
            "elapsedMs": 1,
            "stdout": "",
            "stderr": "",
            "error": null
        });
        let mut response_bytes = serde_json::to_vec(&response).expect("serialize response");
        response_bytes.push(b'\n');
        stream
            .write_all(&response_bytes)
            .expect("write wrapper response");
        request
    });
    let broker_nonce = "a".repeat(64);
    let output = Command::new("/usr/bin/bash")
        .arg(&script)
        .args([
            "--mode",
            "scratch",
            "--candidate",
            "scratch/core.v",
            "--purpose",
            "semantic-equivalence",
            "--timeout-seconds",
            "5",
        ])
        .env_clear()
        .env("PATH", "/usr/bin:/bin")
        .env("LOGOS_PROOF_DIAGNOSTIC_SOCKET", &socket_path)
        .env("LOGOS_PROOF_DIAGNOSTIC_NONCE", &broker_nonce)
        .output()
        .expect("run diagnostic wrapper");
    assert!(
        output.status.success(),
        "wrapper failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(String::from_utf8_lossy(&output.stdout).contains("Host scratch compile passed"));
    let request = broker.join().expect("join fake wrapper broker");
    assert_eq!(request["schemaVersion"], 2);
    assert_eq!(request["mode"], "scratch");
    assert_eq!(request["candidatePath"], "scratch/core.v");
    assert_eq!(request["purpose"], "semantic-equivalence");
    assert_eq!(request["candidateSha256"], sha256_hex(candidate));

    std::fs::create_dir(root.join("ProofModules")).expect("create wrapper module tree");
    let module_candidate = b"Lemma wrapper_module : True. Proof. exact I. Qed.\n";
    std::fs::write(root.join("ProofModules/CoreFacts.v"), module_candidate)
        .expect("write wrapper module candidate");
    let incomplete_socket_path = root.join("incomplete-broker.sock");
    let incomplete_listener =
        UnixListener::bind(&incomplete_socket_path).expect("bind incomplete fake broker");
    let incomplete_broker = std::thread::spawn(move || {
        let (mut stream, _) = incomplete_listener
            .accept()
            .expect("accept module wrapper request");
        let mut request_bytes = Vec::new();
        let mut block = [0u8; 512];
        while !request_bytes.contains(&b'\n') {
            let count = stream
                .read(&mut block)
                .expect("read module wrapper request");
            assert!(count > 0, "wrapper closed before module request newline");
            request_bytes.extend_from_slice(&block[..count]);
        }
        let newline = request_bytes
            .iter()
            .position(|byte| *byte == b'\n')
            .expect("module wrapper request newline");
        let request: serde_json::Value = serde_json::from_slice(&request_bytes[..newline])
            .expect("parse module wrapper request");
        let response = serde_json::json!({
            "schemaVersion": 2,
            "sequence": 2,
            "compilePassed": true,
            "problemCompilePassed": false,
            "compileCheckpointAdvanced": false,
            "exitCode": 0,
            "timedOut": false,
            "elapsedMs": 1,
            "stdout": "",
            "stderr": "",
            "error": null
        });
        let mut response_bytes = serde_json::to_vec(&response).expect("serialize response");
        response_bytes.push(b'\n');
        stream
            .write_all(&response_bytes)
            .expect("write incomplete module response");
        request
    });
    let incomplete = Command::new("/usr/bin/bash")
        .arg(&script)
        .args([
            "--mode",
            "module",
            "--candidate",
            "ProofModules/CoreFacts.v",
            "--purpose",
            "static-obligation",
            "--timeout-seconds",
            "5",
        ])
        .env_clear()
        .env("PATH", "/usr/bin:/bin")
        .env("LOGOS_PROOF_DIAGNOSTIC_SOCKET", &incomplete_socket_path)
        .env("LOGOS_PROOF_DIAGNOSTIC_NONCE", &broker_nonce)
        .output()
        .expect("run module diagnostic wrapper");
    assert!(!incomplete.status.success());
    assert!(
        String::from_utf8_lossy(&incomplete.stderr).contains("response identity mismatch for mode")
    );
    let module_request = incomplete_broker
        .join()
        .expect("join incomplete fake module broker");
    assert_eq!(module_request["mode"], "module");
    assert_eq!(module_request["candidatePath"], "ProofModules/CoreFacts.v");
    assert_eq!(
        module_request["candidateSha256"],
        sha256_hex(module_candidate)
    );

    let stale = Command::new("/usr/bin/bash")
        .arg(&script)
        .args(["--timeout-seconds", "5"])
        .env_clear()
        .env("PATH", "/usr/bin:/bin")
        .output()
        .expect("run stale wrapper invocation");
    assert_eq!(stale.status.code(), Some(64));
    std::fs::remove_dir_all(root).expect("remove wrapper test tree");
}

#[test]
fn proof_agent_searches_authoritative_sources_without_a_routed_catalog() {
    let body = proof_agent_instruction_body();
    assert!(body.contains("python3 search-rocq-declarations.py --help"));
    assert!(body.contains("--conclusion-symbol"));
    assert!(body.contains("Filters are mechanical and conjunctive"));
    assert!(body.contains("no relevance score"));
    assert!(!body.contains("lemma-catalog"));
    assert!(!body.contains("routed.json"));
    assert!(!body.contains("shortlist.jq"));
    assert!(!body.contains("normalizationFrontierHints"));
    assert!(!body.contains("[:16]"));
    assert!(!body.contains("--conclusion-head"));
    assert!(!body.contains("singleton-left RIGHT JOIN"));
    assert!(!body.contains("query_expr_join_has_success_of_acceptance_projection_exact"));
    for forbidden_answer_hint in [
        "query_expr_context_global_congr",
        "query_make_groups_group_terms_Permutation",
        "eval_groups_outcome_uniform_congr",
        "eval_group_bag_exact_rows_permut_equiv",
        "query_expr_group_possible_outcome_equiv_of_exact_group_bag_outcomes",
        "query_expr_project_has_outcome_safe",
        "query_expr_filter_bag_closed_exact",
    ] {
        assert!(
            !body.contains(forbidden_answer_hint),
            "proof prompt must not hard-code theorem route {forbidden_answer_hint}"
        );
    }
    assert_eq!(
        static_prompt_and_primer_bytes(),
        body.len() + FORMAL_SQL_SEMANTIC_PRIMER.len()
    );
    assert!(!body.is_empty());
}

#[test]
fn proof_agent_context_excludes_obsolete_routed_catalogs_and_detects_drift() {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after Unix epoch")
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "logos-self-search-context-{}-{nonce}",
        std::process::id()
    ));
    let artifacts = ArtifactWriter::new(Some(root.clone())).expect("artifact writer");
    let input_root = root.join("inputs");
    std::fs::create_dir_all(&input_root).expect("create input root");
    let schema_path = input_root.join("schema.sql");
    let source_path = input_root.join("source.sql");
    let target_path = input_root.join("target.sql");
    std::fs::write(&schema_path, "CREATE TABLE t (a INTEGER);\n").expect("write schema");
    std::fs::write(&source_path, "  SELECT a FROM t;\n").expect("write source");
    std::fs::write(&target_path, "SELECT a FROM t; -- target\n").expect("write target");
    let input = VerificationInput::read_with_environment(
        schema_path,
        source_path,
        target_path,
        SqlEnvironment::default(),
    )
    .expect("read verification input");
    let schema_module = "Definition schema_marker := I.\n";
    let queries_module = "Definition query_marker := I.\n";
    let witness_module = "Definition witness_marker := I.\n";
    for (name, text) in [
        ("Schema.v", schema_module),
        ("Queries.v", queries_module),
        ("Witness.v", witness_module),
        ("Goal.v", FORMAL_SQL_GOAL_MODULE.as_str()),
    ] {
        artifacts
            .write_text(format!("proof-stage/formal-sql/{name}"), text)
            .expect("write trusted context");
    }

    let context = write_proof_agent_context(
        &artifacts,
        &input,
        VerificationMode::OutcomeUnconditional,
        "{}\n",
        "{}\n",
        "{}\n",
        schema_module,
        queries_module,
        witness_module,
        "Definition problem_marker := I.\n",
        FORMAL_SQL_GOAL_MODULE.as_str(),
    )
    .expect("write self-search context");
    assert_eq!(context.manifest.schema_version, 8);
    assert!(!root.join("proof-stage/formal-sql/lemma-catalog").exists());
    assert_eq!(
        std::fs::read_to_string(root.join("proof-stage/formal-sql/search-rocq-declarations.py"))
            .expect("read declaration search helper"),
        FORMAL_SQL_DECLARATION_SEARCH_SCRIPT
    );
    assert_eq!(
        context.report.declaration_search_sha256,
        sha256_hex(FORMAL_SQL_DECLARATION_SEARCH_SCRIPT.as_bytes())
    );
    assert_eq!(
        std::fs::read_to_string(root.join("proof-stage/formal-sql/source.sql"))
            .expect("read exact source"),
        input.source_sql()
    );

    let replacement_witness = "Definition witness_marker := O.\n";
    artifacts
        .write_text("proof-stage/formal-sql/Witness.v", replacement_witness)
        .expect("replace fixed witness");
    let rebound_context = write_proof_agent_context(
        &artifacts,
        &input,
        VerificationMode::OutcomeUnconditional,
        "{}\n",
        "{}\n",
        "{}\n",
        schema_module,
        queries_module,
        replacement_witness,
        "Definition problem_marker := I.\n",
        FORMAL_SQL_GOAL_MODULE.as_str(),
    )
    .expect("rebind context to replacement witness");
    assert_ne!(
        context.report.witness_module_sha256,
        rebound_context.report.witness_module_sha256
    );
    assert_ne!(
        context.report.manifest_sha256,
        rebound_context.report.manifest_sha256
    );
    validate_proof_agent_context(&artifacts, &rebound_context)
        .expect("replacement-witness context is self-consistent");

    std::fs::write(
        root.join("proof-stage/formal-sql/source.sql"),
        "SELECT 1;\n",
    )
    .expect("mutate context");
    let error = validate_proof_agent_context(&artifacts, &rebound_context)
        .expect_err("context drift must fail closed")
        .to_string();
    assert!(error.contains("proof-agent context drift"));
    assert!(error.contains("source.sql"));
    std::fs::remove_dir_all(root).expect("remove context workspace");
}

#[test]
fn fixed_witness_restart_archives_checked_module_cache_by_generation() {
    let fixture = tempfile::tempdir().expect("create cache archive fixture");
    let artifacts =
        ArtifactWriter::new(Some(fixture.path().join("case"))).expect("artifact writer");
    let formal_root = artifacts.root().join("proof-stage/formal-sql");
    let cache_root = artifacts
        .root()
        .join("proof-stage/proof-agent/trusted-diagnostic-cache");
    std::fs::create_dir_all(formal_root.join("ProofModules")).expect("create formal module root");
    std::fs::create_dir_all(formal_root.join("WitnessModules"))
        .expect("create formal witness module root");
    std::fs::create_dir_all(cache_root.join("ProofModules")).expect("create trusted module cache");
    std::fs::create_dir_all(cache_root.join("WitnessModules"))
        .expect("create trusted witness module cache");
    for (name, bytes) in [
        ("Schema.v", b"Definition schema := True.\n".as_slice()),
        ("Queries.v", b"Definition queries := True.\n".as_slice()),
        (
            "WitnessData.v",
            b"Definition witness_data := True.\n".as_slice(),
        ),
        ("Witness.v", b"Definition witness := True.\n".as_slice()),
        (
            "RuntimeBridge.v",
            b"Definition runtime_bridge := True.\n".as_slice(),
        ),
    ] {
        std::fs::write(formal_root.join(name), bytes).expect("write live trusted source");
        std::fs::write(cache_root.join(name), bytes).expect("write cached trusted source");
    }
    for (name, bytes) in [
        ("Schema.vo", b"schema object".as_slice()),
        ("Queries.vo", b"queries object".as_slice()),
        ("WitnessData.vo", b"witness data object".as_slice()),
        ("Witness.vo", b"witness object".as_slice()),
        ("RuntimeBridge.vo", b"runtime bridge object".as_slice()),
    ] {
        std::fs::write(cache_root.join(name), bytes).expect("write cached object");
    }
    let module = b"Lemma checked_fact : True. Proof. exact I. Qed.\n";
    std::fs::write(formal_root.join("ProofModules/CheckedFacts.v"), module)
        .expect("write live checked module");
    std::fs::write(cache_root.join("ProofModules/CheckedFacts.v"), module)
        .expect("write cached module source");
    std::fs::write(
        cache_root.join("ProofModules/CheckedFacts.vo"),
        b"checked module object",
    )
    .expect("write cached module object");
    std::fs::write(cache_root.join("ProofModules/ORDER"), b"CheckedFacts.v\n")
        .expect("write module order");
    std::fs::write(formal_root.join("WitnessModules/ORDER"), b"")
        .expect("write live witness module order");
    std::fs::write(cache_root.join("WitnessModules/ORDER"), b"")
        .expect("write witness module order");
    let entries = [
        "Schema.v",
        "Schema.vo",
        "Queries.v",
        "Queries.vo",
        "WitnessData.v",
        "WitnessData.vo",
        "Witness.v",
        "Witness.vo",
        "RuntimeBridge.v",
        "RuntimeBridge.vo",
        "WitnessModules/ORDER",
        "ProofModules/ORDER",
        "ProofModules/CheckedFacts.v",
        "ProofModules/CheckedFacts.vo",
    ];
    let manifest = entries
        .iter()
        .map(|name| {
            let bytes = std::fs::read(cache_root.join(name)).expect("read cache entry");
            format!("{}  {name}\n", sha256_hex(&bytes))
        })
        .collect::<String>();
    std::fs::write(cache_root.join("SHA256SUMS"), &manifest).expect("write cache manifest");

    let evidence = archive_trusted_diagnostic_cache(&artifacts, 1)
        .expect("archive generation-one module cache");
    assert_eq!(evidence.workspace_generation, 1);
    assert_eq!(evidence.manifest_sha256, sha256_hex(manifest.as_bytes()));
    let archived_module = artifacts.root().join(
        "proof-stage/proof-agent/workspace-generations/0001/trusted-diagnostic-cache/ProofModules/CheckedFacts.vo",
    );
    assert_eq!(
        std::fs::read(&archived_module).unwrap(),
        b"checked module object"
    );
    let error = archive_trusted_diagnostic_cache(&artifacts, 1)
        .expect_err("cache archive must be create-once")
        .to_string();
    assert!(error.contains("create-once trusted cache archive"));

    remove_proof_workspace_for_formal_witness_restart(&artifacts)
        .expect("remove live fixed-witness state");
    assert!(cache_root.exists());
    assert_eq!(
        std::fs::read(cache_root.join("Queries.vo")).unwrap(),
        b"queries object"
    );
    assert_eq!(
        std::fs::read(archived_module).unwrap(),
        b"checked module object"
    );
}

#[test]
fn fixed_witness_restart_discards_mutable_state_but_keeps_checked_prefix() {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after Unix epoch")
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "logos-fixed-witness-restart-{}-{nonce}",
        std::process::id()
    ));
    let artifacts = ArtifactWriter::new(Some(root.clone())).expect("artifact writer");
    for (relative, contents) in [
        ("Problem.v", "Definition stale_problem := I.\n"),
        ("Witness.v", "Definition stale_witness := I.\n"),
        (
            "scratch/checked/stale.v",
            "Definition stale_scratch := I.\n",
        ),
        ("Problem.vo", "stale compiled bytes"),
        (
            "ProofModules/CheckedCore.v",
            "Lemma stale_checked_core : True. Proof. exact I. Qed.\n",
        ),
        ("counterexample-handoff.json", "{}\n"),
        ("authority-closure.txt", "stale\n"),
    ] {
        artifacts
            .write_text(format!("proof-stage/formal-sql/{relative}"), contents)
            .expect("write stale proof state");
    }
    for (relative, contents) in [
        (
            "trusted-diagnostic-cache/SHA256SUMS",
            "stale cache manifest\n",
        ),
        (
            "trusted-diagnostic-cache/ProofModules/ORDER",
            "CheckedCore.v\n",
        ),
        (
            "trusted-diagnostic-cache/ProofModules/CheckedCore.v",
            "Lemma stale_checked_core : True. Proof. exact I. Qed.\n",
        ),
        (
            "trusted-diagnostic-cache/ProofModules/CheckedCore.vo",
            "stale host object bytes\n",
        ),
        (
            "initial-problem-checkpoint/Problem.v",
            "Definition stale_checkpoint := I.\n",
        ),
        (
            "workspace-generations/0001/initial-problem-checkpoint/Problem.v",
            "Definition preserved_generation_one_checkpoint := I.\n",
        ),
        (
            "workspace-generations/0001/initial-problem-checkpoint/invocation.json",
            "{\"sequence\":0}\n",
        ),
        (
            "workspace-generations/0001/trusted-environment-preflight/invocation.json",
            "{\"exitCode\":0}\n",
        ),
        ("rounds/01/events.jsonl", "historical round\n"),
        (
            ".logos-trusted-diagnostic-cache-old.interrupted/SHA256SUMS",
            "retained old cache\n",
        ),
        (
            ".logos-trusted-diagnostic-cache.pending/SHA256SUMS",
            "unpublished staged cache\n",
        ),
        (
            "host-tmp/trusted-rocq-check.interrupted/problem/ProofModules/Old.v",
            "Lemma stale_checker_source : True. Proof. exact I. Qed.\n",
        ),
        (
            "host-tmp/trusted-rocq-check.interrupted/problem-output/ProofModules/Old.vo",
            "stale checker object bytes\n",
        ),
    ] {
        artifacts
            .write_text(format!("proof-stage/proof-agent/{relative}"), contents)
            .expect("write stale host proof state");
    }

    remove_proof_workspace_for_formal_witness_restart(&artifacts)
        .expect("remove stale fixed-witness workspace");
    assert!(!root.join("proof-stage/formal-sql").exists());
    assert!(
        root.join("proof-stage/proof-agent/trusted-diagnostic-cache")
            .exists()
    );
    assert!(
        !root
            .join("proof-stage/proof-agent/initial-problem-checkpoint")
            .exists()
    );
    assert_eq!(
        std::fs::read_to_string(root.join(
            "proof-stage/proof-agent/workspace-generations/0001/initial-problem-checkpoint/Problem.v"
        ))
        .expect("read preserved generation-one checkpoint"),
        "Definition preserved_generation_one_checkpoint := I.\n"
    );
    assert!(
        root.join(
            "proof-stage/proof-agent/workspace-generations/0001/trusted-environment-preflight/invocation.json"
        )
        .is_file()
    );
    assert!(
        !root
            .join("proof-stage/proof-agent/.logos-trusted-diagnostic-cache-old.interrupted")
            .exists()
    );
    assert!(
        !root
            .join("proof-stage/proof-agent/.logos-trusted-diagnostic-cache.pending")
            .exists()
    );
    assert!(
        !root
            .join("proof-stage/proof-agent/host-tmp/trusted-rocq-check.interrupted")
            .exists()
    );
    assert!(
        root.join("proof-stage/proof-agent/rounds/01/events.jsonl")
            .is_file()
    );
    assert!(root.join("proof-stage").is_dir());

    std::fs::remove_dir_all(root).expect("remove restart test artifacts");
}

#[test]
fn fixed_witness_restart_refuses_a_symlink_workspace() {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after Unix epoch")
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "logos-fixed-witness-symlink-{}-{nonce}",
        std::process::id()
    ));
    let artifacts = ArtifactWriter::new(Some(root.clone())).expect("artifact writer");
    let outside = root.join("outside");
    std::fs::create_dir_all(&outside).expect("create outside directory");
    let formal_sql = root.join("proof-stage/formal-sql");
    std::fs::create_dir_all(formal_sql.parent().expect("proof-stage parent"))
        .expect("create proof-stage");
    symlink(&outside, &formal_sql).expect("create adversarial workspace symlink");

    let error = remove_proof_workspace_for_formal_witness_restart(&artifacts)
        .expect_err("a symlink workspace must fail closed")
        .to_string();
    assert!(error.contains("refusing to replace non-directory proof workspace"));
    assert!(outside.is_dir());

    std::fs::remove_dir_all(root).expect("remove symlink restart artifacts");
}

#[test]
fn proof_agent_uses_a_launcher_outside_the_mutable_workspace() {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after Unix epoch")
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "logos-proof-launcher-{}-{nonce}",
        std::process::id()
    ));
    let artifacts = ArtifactWriter::new(Some(root.clone())).expect("artifact writer");
    let trusted = write_trusted_proof_agent_launcher(&artifacts).expect("write trusted launcher");
    let trusted_checker =
        write_trusted_rocq_checker(&artifacts).expect("write trusted Rocq checker");

    assert!(!trusted.starts_with(root.join("proof-stage/formal-sql")));
    assert!(!trusted_checker.starts_with(root.join("proof-stage/formal-sql")));
    assert_eq!(
        std::fs::read_to_string(trusted).expect("read trusted launcher"),
        FORMAL_SQL_DOCKER_AGENT_SCRIPT
    );
    assert_eq!(
        std::fs::read_to_string(trusted_checker).expect("read trusted Rocq checker"),
        FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT
    );
    assert!(
        !root
            .join("proof-stage/formal-sql/run-proof-agent-docker.sh")
            .exists()
    );
    std::fs::remove_dir_all(root).expect("remove test artifacts");
}

#[test]
fn proof_audit_reads_the_post_agent_snapshot() {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after Unix epoch")
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "logos-proof-snapshot-{}-{nonce}",
        std::process::id()
    ));
    let artifacts = ArtifactWriter::new(Some(root.clone())).expect("artifact writer");
    for name in PROOF_SOURCE_FILES {
        artifacts
            .write_text(
                format!("proof-stage/formal-sql/{name}"),
                "Definition clean := I.\n",
            )
            .expect("write proof source");
    }
    artifacts
        .write_text("proof-stage/formal-sql/WitnessModules/ORDER", "")
        .expect("write witness module order");
    write_placeholder_proof_context(&artifacts);
    artifacts
        .write_text(
            "proof-stage/formal-sql/Problem.v",
            "Axiom magic : forall P : Prop, P.\n",
        )
        .expect("write malicious problem");
    artifacts
        .write_text(
            "proof-stage/formal-sql/run-rocq-check.sh",
            "#!/usr/bin/env bash\nexit 0\n",
        )
        .expect("write checker");
    artifacts
        .write_text(
            "proof-stage/formal-sql/scratch/retained.v",
            "Axiom scratch_only : False.\n",
        )
        .expect("write scratch file excluded from final audit");

    let trusted_sources =
        capture_trusted_proof_sources(&artifacts).expect("capture trusted proof sources");
    let snapshot = snapshot_proof_workspace(&artifacts, 1).expect("snapshot proof sources");
    assert!(!snapshot.join("run-rocq-check.sh").exists());
    assert!(!snapshot.join("scratch").exists());
    artifacts
        .write_text(
            "proof-stage/formal-sql/Problem.v",
            "Definition clean := I.\n",
        )
        .expect("replace live problem");
    let audit =
        audit_proof_workspace(&artifacts, &snapshot, &trusted_sources).expect("audit snapshot");

    assert!(!audit.passed);
    assert!(
        audit
            .findings
            .iter()
            .any(|finding| finding.token == "Axiom")
    );
    std::fs::remove_dir_all(root).expect("remove test artifacts");
}

#[test]
fn proof_audit_rejects_changes_to_trusted_generated_sources() {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after Unix epoch")
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "logos-proof-integrity-{}-{nonce}",
        std::process::id()
    ));
    let artifacts = ArtifactWriter::new(Some(root.clone())).expect("artifact writer");
    for name in PROOF_SOURCE_FILES {
        artifacts
            .write_text(
                format!("proof-stage/formal-sql/{name}"),
                "Definition clean := I.\n",
            )
            .expect("write proof source");
    }
    artifacts
        .write_text("proof-stage/formal-sql/WitnessModules/ORDER", "")
        .expect("write witness module order");
    write_placeholder_proof_context(&artifacts);
    let trusted_sources =
        capture_trusted_proof_sources(&artifacts).expect("capture trusted proof sources");
    artifacts
        .write_text(
            "proof-stage/formal-sql/Goal.v",
            "Definition required_equivalence_statement : Prop := True.\n",
        )
        .expect("replace trusted goal");

    let snapshot = snapshot_proof_workspace(&artifacts, 1).expect("snapshot proof sources");
    let audit =
        audit_proof_workspace(&artifacts, &snapshot, &trusted_sources).expect("audit snapshot");

    assert!(!audit.passed);
    assert!(
        audit
            .findings
            .iter()
            .any(|finding| finding.token == "trusted source modified")
    );
    std::fs::remove_dir_all(root).expect("remove test artifacts");
}

#[test]
fn scratch_audit_allows_generalized_sections_but_not_assumptions_or_open_results() {
    let source = format!(
        "{}\nModule LocalIsolation.\nSection Generalized.\nVariable P : Prop.\nContext (HP : P).\nLemma generalized_identity : P. Proof. exact HP. Qed.\nEnd Generalized.\nEnd LocalIsolation.\n",
        TRUSTED_PROBLEM_IMPORT_LINES.join("\n")
    );
    assert!(super::audit::audit_scratch_rocq_text("scratch/general.v", &source).is_empty());
    let final_findings = audit_rocq_text("Problem.v", &source);
    assert!(
        final_findings
            .iter()
            .any(|finding| finding.token == "Module")
    );
    assert!(
        final_findings
            .iter()
            .any(|finding| finding.token == "Variable")
    );

    let assumption_findings = super::audit::audit_scratch_rocq_text(
        "scratch/assumption.v",
        "Parameter magic : forall P : Prop, P.\nLemma result : True. Proof. exact I. Qed.\n",
    );
    assert!(
        assumption_findings
            .iter()
            .any(|finding| finding.token == "Parameter")
    );
    let missing_qed = super::audit::audit_scratch_rocq_text(
        "scratch/no-result.v",
        "Definition only_a_definition : True := I.\n",
    );
    assert!(
        missing_qed
            .iter()
            .any(|finding| finding.token == "missing Qed")
    );
    let untrusted = super::audit::audit_scratch_rocq_text(
        "scratch/import.v",
        "Require Import HistoricalProof.\nLemma result : True. Proof. exact I. Qed.\n",
    );
    assert!(
        untrusted
            .iter()
            .any(|finding| finding.token == "untrusted import")
    );
}

#[test]
fn proof_module_paths_imports_and_immutability_are_fail_closed() {
    for accepted in ["ProofModules/Core.v", "ProofModules/Proof20_GroupLift.v"] {
        assert!(
            super::workspace::validate_proof_module_candidate_path(accepted).is_ok(),
            "expected valid module path {accepted}"
        );
    }
    for rejected in [
        "ProofModules/lowercase.v",
        "ProofModules/Nested/Core.v",
        "ProofModules/Core.vo",
        "scratch/Core.v",
        "ProofModules/../Core.v",
    ] {
        assert!(
            super::workspace::validate_proof_module_candidate_path(rejected).is_err(),
            "expected invalid module path {rejected}"
        );
    }

    let source = format!(
        "{}\nFrom LogosGenerated.ProofModules Require Import Core Proof20_GroupLift.\nLemma exported_fact : True. Proof. exact I. Qed.\n",
        TRUSTED_PROBLEM_IMPORT_LINES.join("\n")
    );
    assert!(
        super::audit::audit_proof_module_rocq_text("ProofModules/Consumer.v", &source).is_empty()
    );
    assert!(audit_rocq_text("Problem.v", &source).is_empty());
    let malformed = super::audit::audit_proof_module_rocq_text(
        "ProofModules/Bad.v",
        "From LogosGenerated.ProofModules Require Import ../Escape.\nLemma x : True. Proof. exact I. Qed.\n",
    );
    assert!(
        malformed
            .iter()
            .any(|finding| finding.token == "untrusted import")
    );
    for forbidden in [
        "Import Core.\nLemma x : True. Proof. exact I. Qed.\n",
        "Export Core.\nLemma x : True. Proof. exact I. Qed.\n",
        "Include Core.\nLemma x : True. Proof. exact I. Qed.\n",
        "From LogosGenerated.ProofModules\nRequire Import Core.\nLemma x : True. Proof. exact I. Qed.\n",
    ] {
        assert!(
            super::audit::audit_proof_module_rocq_text("ProofModules/BadImport.v", forbidden)
                .iter()
                .any(|finding| finding.token == "untrusted import"),
            "forbidden helper import form passed the source audit: {forbidden:?}"
        );
    }

    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after Unix epoch")
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "logos-proof-module-persistence-{}-{nonce}",
        std::process::id()
    ));
    std::fs::create_dir_all(&root).expect("create proof module test root");
    let first = b"Lemma first : True. Proof. exact I. Qed.\n";
    super::workspace::persist_successful_proof_module_candidate(
        &root,
        Path::new("ProofModules/Core.v"),
        first,
    )
    .expect("persist first checked module");
    super::workspace::persist_successful_proof_module_candidate(
        &root,
        Path::new("ProofModules/Core.v"),
        first,
    )
    .expect("accept byte-identical checked module");
    let replacement = super::workspace::persist_successful_proof_module_candidate(
        &root,
        Path::new("ProofModules/Core.v"),
        b"Lemma changed : True. Proof. exact I. Qed.\n",
    )
    .expect_err("checked module names must be immutable")
    .to_string();
    assert!(replacement.contains("immutable"));

    let pending = super::workspace::ModulePublication::prepare(
        &root,
        Path::new("ProofModules/Pending.v"),
        b"Lemma pending : True. Proof. exact I. Qed.\n",
        false,
    )
    .expect("prepare pending module source");
    assert!(root.join("ProofModules/Pending.v").is_file());
    pending
        .rollback()
        .expect("roll back a failed module diagnostic");
    assert!(!root.join("ProofModules/Pending.v").exists());

    let outside = root.join("outside.v");
    std::fs::write(&outside, first).expect("write symlink target");
    symlink(&outside, root.join("ProofModules/Symlinked.v"))
        .expect("create adversarial module symlink");
    assert!(
        super::validated_proof_module_sources(&root.join("ProofModules")).is_err(),
        "a symlinked module source must be rejected"
    );
    std::fs::remove_file(root.join("ProofModules/Symlinked.v")).expect("remove module symlink");
    std::fs::write(root.join("ProofModules/lowercase.v"), first)
        .expect("write malformed module name");
    assert!(
        super::validated_proof_module_sources(&root.join("ProofModules")).is_err(),
        "a malformed module source name must be rejected"
    );
    std::fs::remove_dir_all(root).expect("remove proof module test tree");
}

#[test]
fn proof_audit_rejects_untrusted_imports_and_escape_commands() {
    let source = "Require Import LocalAxiom.\n\
                  From Stdlib Require Import Compat.AdmitAxiom.\n\
                  Axioms magic : forall P : Prop, P.\n\
                  Unset Guard Checking.\n\
                  #[bypass_check(guard)] Fixpoint loop (u : unit) : False := loop u.\n\
                  Global Notation \"safe\" := False.\n\
                  Module Logos. End Logos.\n\
                  vm_cast_no_check (eq_refl true).\n\
                  Print Universes All \"Goal.v\".\n\
                  Load secret.\n\
                  Admit Obligations.\n";
    let findings = audit_rocq_text("proof-stage/formal-sql/Problem.v", source);
    assert!(
        findings
            .iter()
            .any(|finding| finding.token == "untrusted import")
    );
    assert_eq!(
        findings
            .iter()
            .filter(|finding| finding.token == "untrusted import")
            .count(),
        2
    );
    assert!(findings.iter().any(|finding| finding.token == "Load"));
    assert!(findings.iter().any(|finding| finding.token == "Print"));
    assert!(findings.iter().any(|finding| finding.token == "Admit"));
    assert!(findings.iter().any(|finding| finding.token == "Axioms"));
    assert!(findings.iter().any(|finding| finding.token == "Unset"));
    assert!(
        findings
            .iter()
            .any(|finding| finding.token == "bypass_check")
    );
    assert!(
        findings
            .iter()
            .any(|finding| finding.token == "vm_cast_no_check")
    );
    assert!(findings.iter().any(|finding| finding.token == "Notation"));
    assert!(findings.iter().any(|finding| finding.token == "Module"));
}

#[test]
fn proof_audit_accepts_generated_trusted_imports() {
    let mut source = TRUSTED_PROBLEM_IMPORT_LINES.join("\n");
    source.push_str(
        "\nCheck numeric_avg_attested_scale_finite_exact.\n\
         Check theta_join_list_functional_length_le.\n\
         Check int32_bit_and_fold_permutation.\n\
         Check int64_bit_or_fold_distinct_invariant.\n",
    );
    assert!(audit_rocq_text("proof-stage/formal-sql/Problem.v", &source).is_empty());
}
