//! Proof-stage orchestration: preparation, round scheduling, witness handoff,
//! and final result assembly. Domain logic lives in the private submodules below.

use std::collections::{BTreeMap, BTreeSet};
use std::fs::{File, OpenOptions};
use std::io::{Read, Write};
use std::os::unix::fs::{OpenOptionsExt, PermissionsExt};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::LazyLock;
use std::sync::atomic::AtomicU64;
use std::time::{Duration, Instant};

use logos_ir::ShellSqlIrFrontend;
use serde::Serialize;
use sha2::{Digest, Sha256};

use crate::artifacts::ArtifactWriter;
use crate::core::{
    FormalProofModule, LoweringConfig, ObservationCertificateReport, ProofInputBindings,
    ProofLoweringReport, VerificationInput, VerificationIr, VerificationMode,
    analyze_observation_certificates, lower_verification_input_with_mode,
};
use crate::engine::config::{Config, ExecutionMode};
use crate::engine::now_ms_since_epoch;
use crate::engine::report::{
    AgentRunLog, Backend, BackendStatus, CertificationLevel, DiagnosticCheckerInvocation,
    LaunchEnvironmentPolicy, PreconditionSource, ProofAgentConfiguration, ProofAgentContext,
    ProofAgentDecision, ProofCheckpointTransition, ProofCounterexampleHandoff, ProofReport,
    ProofSessionRestartReason, ProofWorkspace, ProofWorkspaceTransition,
    ProofWorkspaceTransitionReason, TrustedCheckInvocation, VerificationClaimKind,
};
use crate::error::{Error, Result};
use crate::usage::{CodexInvocationUsage, LlmUsage, parse_codex_jsonl, parse_codex_thread_id};
use crate::validation::FormalWitnessSnapshot;

mod ablation;
mod audit;
mod checker;
mod context;
mod diagnostic_inputs;
mod diagnostics;
mod goal;
mod handoff;
mod navigation;
mod witness;
mod workspace;

use audit::{
    AuditPurpose, WorkspaceAudit, audit_proof_workspace_for_mode, problem_declares_final_theorem,
};
use checker::{
    is_trusted_rocq_environment_failure, run_host_diagnostic_rocq_check, run_trusted_rocq_check,
    validate_trusted_rocq_environment,
};
use context::{
    FileBinding, PreparedContext, context_binding, validate_proof_agent_context,
    write_proof_agent_context,
};
use diagnostics::{CandidateKind, CompileCheckpoint, DiagnosticBroker, ReadOnlyMappedFile};
use goal::{formal_sql_bound_goal_module, formal_sql_goal_module};
pub(super) use handoff::{ManualReviewRequest, ProofHandoffResolution};
use handoff::{ProofHandoffHandler, ProofRoundDisposition, resolve_proof_round};
use navigation::build_query_shape;
pub(super) use witness::write_typed_witness_audit_workspace;
use witness::{WitnessModules, formal_sql_witness_modules, write_formal_sql_witness_modules};
use workspace::{
    archive_trusted_diagnostic_cache, hydrate_round_scratch, persist_round_scratch,
    validate_proof_module_candidate_path,
};

pub const DEFAULT_PROOF_AGENT_COMMAND: &str = "codex exec --disable plugins --disable remote_plugin --disable plugin_hooks --disable skill_mcp_dependency_install --disable goals --json --model gpt-6.1-sol -c model_reasoning_effort=medium --dangerously-bypass-approvals-and-sandbox --skip-git-repo-check --cd /workspace/problem - < proof-agent-prompt.md";
pub const DEFAULT_PROOF_AGENT_RESUME_COMMAND: &str = "codex exec resume --disable plugins --disable remote_plugin --disable plugin_hooks --disable skill_mcp_dependency_install --disable goals --json --model gpt-6.1-sol -c model_reasoning_effort=medium --dangerously-bypass-approvals-and-sandbox --skip-git-repo-check {session_id} - < proof-agent-prompt.md";

const PROOF_AGENT_HOST_KILL_MARGIN_SECONDS: u64 = 10;
const PROOF_AGENT_SESSION_RESTART_AFTER_FAILED_ROUNDS: usize = 16;
const PROOF_AGENT_SESSION_HOME_POLICY: &str = "isolated_per_generation";
const PROOF_AGENT_COMPILE_CHECKPOINT_POLICY: &str =
    "latest_host_problem_compile_pass_over_immutable_checked_module_cache_digest_deduplicated";
const PROOF_AGENT_DIAGNOSTIC_TRANSPORT: &str = "host_unix_broker";
const PROOF_AGENT_DIAGNOSTIC_CACHE_POLICY: &str = "preflight_built_source_digest_bound_host_only";
const PROOF_AGENT_DIAGNOSTIC_SCHEDULING_POLICY: &str =
    "sequential_host_broker_invocation_deadline_bounded";
const PROOF_AGENT_DIAGNOSTIC_PARALLELISM_MAX: usize = 1;
const PROOF_AGENT_SCRATCH_PERSISTENCE_POLICY: &str = "regular_nonsymlink_allowed_extension_round_replacement_drop_other_extensions_with_warning_exact_digest_checked_promotion";
const PROOF_AGENT_WRITABLE_STORAGE_POLICY: &str =
    "single_kernel_tmpfs_all_agent_writes_with_read_only_root_v1";
const SCRATCH_ALLOWED_EXTENSIONS: &[&str] = &["v", "md", "txt"];
const CHECKED_SCRATCH_DIRECTORY: &str = "checked";
const PROOF_MODULE_DIRECTORY: &str = "ProofModules";
const WITNESS_MODULE_DIRECTORY: &str = "WitnessModules";
const DIAGNOSTIC_SOCKET_FILE: &str = "socket";
const DIAGNOSTIC_SOCKET_TEMP_ROOT: &str = "/tmp";
// The request header contains only fixed protocol metadata. This protects the
// host parser; it is not a limit on Problem.v or any generated artifact.
const DIAGNOSTIC_BROKER_HEADER_MAX_BYTES: usize = 64 * 1024;
const TRUSTED_CHECK_REPAIR_FEEDBACK_STREAM_MAX_BYTES: usize = 16 * 1024;
const TRUSTED_ROCQ_ENVIRONMENT_FAILURE_EXIT_CODE: i32 = 86;
const TRUSTED_HOST_BASH: &str = "/usr/bin/bash";
const TRUSTED_HOST_TIMEOUT: &str = "/usr/bin/timeout";
const TRUSTED_CHECKER_PATH: &str = "/Anaconda/bin:/usr/bin:/bin";
const TRUSTED_CHECKER_HOME: &str = "/nonexistent";
const PROOF_AGENT_LAUNCHER_PATH: &str = "/usr/bin:/bin";
const PROOF_AGENT_HOST_TMP_DIRECTORY: &str = "proof-stage/proof-agent/host-tmp";
const CASE_PROCESS_SUPERVISOR_PID_ENVIRONMENT: &str = "LOGOS_CASE_SUPERVISOR_PID";
const FIXED_HOST_LOCALE: &str = "C";
const TRUSTED_CHECKER_EXPLICIT_ENVIRONMENT: &[&str] = &[
    "LOGOS_ROCQ_VALIDATION_SESSION",
    "LOGOS_REPO_ROOT",
    "LOGOS_PROOF_WORKDIR",
    "LOGOS_TRUSTED_ROCQ_CACHE_DIR",
    "LOGOS_ROCQ_OPAM_SWITCH",
    "LOGOS_SHARED_ROCQ_CHECKER_RUNTIME_CACHE_DIR",
];
const PROOF_AGENT_LAUNCHER_HOST_ENVIRONMENT_ALLOWLIST: &[&str] = &[
    "HOME",
    "CODEX_HOME",
    "LOGOS_SOLVER_CODEX_HOME",
    "LOGOS_SOLVER_CODEX_CONFIG",
    "OPENAI_API_KEY",
    "CODEX_API_KEY",
    "DOCKER_HOST",
    "DOCKER_CONTEXT",
    "DOCKER_CONFIG",
    "DOCKER_CERT_PATH",
    "DOCKER_TLS",
    "DOCKER_TLS_VERIFY",
    "DOCKER_API_VERSION",
];
const PROOF_AGENT_LAUNCHER_EXPLICIT_ENVIRONMENT: &[&str] = &[
    "LOGOS_REPO_ROOT",
    "LOGOS_PROOF_WORKDIR",
    "LOGOS_PROOF_AGENT_CODEX_HOME",
    "LOGOS_PROOF_AGENT_STAGE",
    "LOGOS_PROOF_DIAGNOSTIC_SOCKET",
    "LOGOS_PROOF_DIAGNOSTIC_NONCE",
    "LOGOS_SOLVER_IMAGE",
    "LOGOS_PROOF_AGENT_COMMAND",
    "LOGOS_PROOF_AGENT_MEMORY_LIMIT",
    "LOGOS_PROOF_AGENT_STORAGE_LIMIT_BYTES",
    "LOGOS_PROOF_AGENT_TIMEOUT",
];
const EXPLICITLY_EXCLUDED_HOST_ENVIRONMENT: &[&str] = &[
    "BASH_ENV",
    "ENV",
    "SHELLOPTS",
    "BASHOPTS",
    "LD_PRELOAD",
    "LD_LIBRARY_PATH",
    "OCAMLPATH",
    "CAML_LD_LIBRARY_PATH",
    "CDPATH",
];
const EXPLICITLY_EXCLUDED_HOST_ENVIRONMENT_PREFIXES: &[&str] = &["BASH_FUNC_"];
static PROOF_AGENT_SESSION_HOME_COUNTER: AtomicU64 = AtomicU64::new(0);

const FORMAL_SQL_PROOF_AGENT_PROMPT: &str = include_str!("../../prompts/proof-agent.md");
const FORMAL_SQL_SEMANTIC_PRIMER: &str = include_str!("../../prompts/semantic-primer.md");
const FORMAL_SQL_DECLARATION_SEARCH_SCRIPT: &str =
    include_str!("../../scripts/search-rocq-declarations.py");
const FORMAL_SQL_ROCQ_CHECK_REQUEST_SCRIPT: &str = include_str!("../../scripts/run-rocq-check.sh");
const FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT: &str =
    include_str!("../../scripts/run-trusted-rocq-check.sh");
const FORMAL_SQL_DOCKER_AGENT_SCRIPT: &str =
    include_str!("../../scripts/run-proof-agent-docker.sh");
const PROOF_SOURCE_FILES: &[&str] = &[
    "Schema.v",
    "Queries.v",
    "WitnessData.v",
    "Witness.v",
    "Problem.v",
    "Goal.v",
];
const TRUSTED_PROOF_SOURCE_FILES: &[&str] = &[
    "Schema.v",
    "Queries.v",
    "WitnessData.v",
    "Witness.v",
    "Goal.v",
];
const PROOF_CONTEXT_FILES: &[&str] = &[
    "source.sql",
    "target.sql",
    "query-shape.json",
    "ordered-signatures.json",
    "observation-certificates.json",
    "semantic-primer.md",
    "search-rocq-declarations.py",
    "context-manifest.json",
    "lemma-availability.json",
];
const COUNTEREXAMPLE_HANDOFF_FILE: &str = "counterexample-handoff.json";
const AUTHORITY_CLOSURE_FILE: &str = "authority-closure.txt";
type TrustedProofSources = BTreeMap<&'static str, String>;

/// Authoritative IR and lowering shared by witness synthesis and the Rocq proof
/// stage. Constructing it once prevents the two agents from silently reasoning
/// about different frontend snapshots.
pub(super) struct PreparedFormalInput {
    pub(super) ir_input: VerificationIr,
    pub(super) lowering_report: ProofLoweringReport,
    pub(super) observation_certificates: ObservationCertificateReport,
}

struct AgentRoundResult {
    log: AgentRunLog,
    repair_feedback: String,
    cumulative_usage: Option<CodexInvocationUsage>,
    session_resumable: bool,
    problem_compile_checkpoint: Option<CompileCheckpoint>,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct AgentRunArtifact<'a> {
    #[serde(flatten)]
    log: &'a AgentRunLog,
    #[serde(skip_serializing_if = "Option::is_none")]
    cumulative_usage: Option<&'a LlmUsage>,
}

struct ProofAgentSessionHome {
    path: PathBuf,
    _tempdir: tempfile::TempDir,
}

impl ProofAgentSessionHome {
    fn create(artifacts: &ArtifactWriter) -> Result<Self> {
        let host_tmp = proof_agent_host_tmp_directory(artifacts)?;
        let tempdir = tempfile::Builder::new()
            .prefix("session-")
            .tempdir_in(&host_tmp)
            .map_err(|source| {
                Error::ProofAgentCommand(format!(
                    "failed to create proof-agent session home in {}: {source}",
                    host_tmp.display()
                ))
            })?;
        let path = tempdir.path().to_owned();
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o700)).map_err(
            |source| {
                Error::ProofAgentCommand(format!(
                    "failed to secure proof-agent session home {}: {source}",
                    path.display()
                ))
            },
        )?;
        Ok(Self {
            path,
            _tempdir: tempdir,
        })
    }

    fn generation_path(&self, generation: usize) -> Result<PathBuf> {
        if generation == 0 {
            return Err(Error::ProofAgentCommand(
                "proof-agent session generation must be positive".to_owned(),
            ));
        }
        let path = self.path.join(format!("generation-{generation:04}"));
        match std::fs::symlink_metadata(&path) {
            Ok(metadata) => {
                if metadata.file_type().is_symlink() || !metadata.is_dir() {
                    return Err(Error::ProofAgentCommand(format!(
                        "proof-agent generation home {} is not a real directory",
                        path.display()
                    )));
                }
                if metadata.permissions().mode() & 0o077 != 0 {
                    return Err(Error::ProofAgentCommand(format!(
                        "proof-agent generation home {} has unsafe permissions {:o}",
                        path.display(),
                        metadata.permissions().mode() & 0o777
                    )));
                }
            }
            Err(source) if source.kind() == std::io::ErrorKind::NotFound => {
                std::fs::create_dir(&path).map_err(|source| {
                    Error::ProofAgentCommand(format!(
                        "failed to create proof-agent generation home {}: {source}",
                        path.display()
                    ))
                })?;
                if let Err(source) =
                    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o700))
                {
                    let _ = std::fs::remove_dir(&path);
                    return Err(Error::ProofAgentCommand(format!(
                        "failed to secure proof-agent generation home {}: {source}",
                        path.display()
                    )));
                }
            }
            Err(source) => {
                return Err(Error::ProofAgentCommand(format!(
                    "failed to inspect proof-agent generation home {}: {source}",
                    path.display()
                )));
            }
        }
        Ok(path)
    }
}

struct ProofAgentRoundStage {
    tempdir: tempfile::TempDir,
}

impl ProofAgentRoundStage {
    fn create(artifacts: &ArtifactWriter) -> Result<Self> {
        let host_tmp = proof_agent_host_tmp_directory(artifacts)?;
        let tempdir = tempfile::Builder::new()
            .prefix("round-")
            .tempdir_in(&host_tmp)
            .map_err(|source| {
                Error::ProofAgentCommand(format!(
                    "failed to create proof-agent round stage in {}: {source}",
                    host_tmp.display()
                ))
            })?;
        std::fs::set_permissions(tempdir.path(), std::fs::Permissions::from_mode(0o700)).map_err(
            |source| {
                Error::ProofAgentCommand(format!(
                    "failed to secure proof-agent round stage {}: {source}",
                    tempdir.path().display()
                ))
            },
        )?;
        Ok(Self { tempdir })
    }

    fn path(&self) -> &Path {
        self.tempdir.path()
    }
}

fn proof_agent_host_tmp_directory(artifacts: &ArtifactWriter) -> Result<PathBuf> {
    let path = artifacts.root().join(PROOF_AGENT_HOST_TMP_DIRECTORY);
    std::fs::create_dir_all(&path).map_err(|source| Error::CreateDir {
        path: path.clone(),
        source,
    })?;
    let metadata = std::fs::symlink_metadata(&path).map_err(|source| Error::Read {
        path: path.clone(),
        source,
    })?;
    if metadata.file_type().is_symlink() || !metadata.is_dir() {
        return Err(Error::ProofAgentCommand(format!(
            "proof-agent host temp root {} must be a real directory",
            path.display()
        )));
    }
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o700)).map_err(|source| {
        Error::ProofAgentCommand(format!(
            "failed to secure proof-agent host temp root {}: {source}",
            path.display()
        ))
    })?;
    Ok(path)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct TrustedRocqImportRoot {
    root: TrustedRocqRoot,
    qualifier: &'static str,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct TrustedRocqImport {
    root: TrustedRocqRoot,
    module: &'static str,
    proof_import_order: Option<usize>,
    object_check_order: Option<usize>,
    make_build_order: Option<usize>,
}

macro_rules! declare_proof_stage_trusted_rocq_imports {
    (
        roots: [$(($root:ident, $qualifier:literal)),* $(,)?],
        imports: [$(($import_root:ident, $module:literal, $proof_order:expr, $object_order:expr, $make_order:expr)),* $(,)?],
    ) => {
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        enum TrustedRocqRoot {
            $($root),*
        }

        const TRUSTED_ROCQ_IMPORT_ROOTS: &[TrustedRocqImportRoot] = &[
            $(TrustedRocqImportRoot {
                root: TrustedRocqRoot::$root,
                qualifier: $qualifier,
            }),*
        ];

        const TRUSTED_ROCQ_IMPORTS: &[TrustedRocqImport] = &[
            $(TrustedRocqImport {
                root: TrustedRocqRoot::$import_root,
                module: $module,
                proof_import_order: $proof_order,
                object_check_order: $object_order,
                make_build_order: $make_order,
            }),*
        ];
    };
}

crate::logos_trusted_rocq_import_registry!(declare_proof_stage_trusted_rocq_imports);

static TRUSTED_PROBLEM_IMPORT_LINES: LazyLock<Vec<String>> = LazyLock::new(|| {
    for root in TRUSTED_ROCQ_IMPORT_ROOTS {
        debug_assert!(trusted_registry_ranks_are_contiguous(
            TRUSTED_ROCQ_IMPORTS
                .iter()
                .filter(|import| import.root == root.root)
                .filter_map(|import| import.proof_import_order)
                .collect(),
        ));
    }
    debug_assert!(trusted_registry_ranks_are_contiguous(
        TRUSTED_ROCQ_IMPORTS
            .iter()
            .filter_map(|import| import.object_check_order)
            .collect(),
    ));
    debug_assert!(trusted_registry_ranks_are_contiguous(
        TRUSTED_ROCQ_IMPORTS
            .iter()
            .filter_map(|import| import.make_build_order)
            .collect(),
    ));
    TRUSTED_ROCQ_IMPORT_ROOTS
        .iter()
        .map(|root| {
            format!(
                "From {} Require Import {}.",
                root.qualifier,
                ordered_direct_trusted_rocq_imports(root.root).join(" ")
            )
        })
        .collect()
});

fn ordered_direct_trusted_rocq_imports(root: TrustedRocqRoot) -> Vec<&'static str> {
    let mut imports = TRUSTED_ROCQ_IMPORTS
        .iter()
        .filter(|import| import.root == root)
        .filter_map(|import| Some((import.proof_import_order?, import.module)))
        .collect::<Vec<_>>();
    imports.sort_unstable_by_key(|(order, _)| *order);
    imports.into_iter().map(|(_, module)| module).collect()
}

fn trusted_registry_ranks_are_contiguous(mut ranks: Vec<usize>) -> bool {
    ranks.sort_unstable();
    ranks.iter().copied().eq(0..ranks.len())
}

const FORMAL_SQL_GOAL_HEADER: &str = "\
From SQLFS Require Import SqlSyntax GenericInstance Values SqlOutcome SqlErrorSemantics SqlQuerySyntax SqlQuerySemantics SqlQueryWellFormed FiniteSet Bool3.
From Logos Require Import FormalSQL.QueryTNullSyntax FormalSQL.VerificationConditions.
From LogosGenerated Require Schema Queries Witness.
From Stdlib Require Import List.

Definition required_value_is_null (v : value) : bool :=
  NullValues.is_null_value v.
";

#[cfg(test)]
static FORMAL_SQL_GOAL_MODULE: LazyLock<String> =
    LazyLock::new(|| formal_sql_goal_module(VerificationMode::SafeUnconditional));

fn sha256_hex(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

/// Cross-language canonical JSON binding: recursively sort object keys,
/// preserve array order, serialize compact UTF-8 JSON, then hash those bytes.
fn canonical_json_sha256<T: Serialize>(value: &T) -> Result<String> {
    fn sorted(value: serde_json::Value) -> serde_json::Value {
        match value {
            serde_json::Value::Object(object) => {
                let mut entries = object.into_iter().collect::<Vec<_>>();
                entries.sort_unstable_by(|left, right| left.0.cmp(&right.0));
                let mut canonical = serde_json::Map::new();
                for (key, value) in entries {
                    canonical.insert(key, sorted(value));
                }
                serde_json::Value::Object(canonical)
            }
            serde_json::Value::Array(values) => {
                serde_json::Value::Array(values.into_iter().map(sorted).collect())
            }
            scalar => scalar,
        }
    }

    let canonical = sorted(serde_json::to_value(value)?);
    Ok(sha256_hex(&serde_json::to_vec(&canonical)?))
}

fn sha256_file_hex(path: &Path) -> Result<String> {
    let mut file = File::open(path).map_err(|source| Error::Read {
        path: path.to_owned(),
        source,
    })?;
    let mut digest = Sha256::new();
    let mut block = [0u8; 64 * 1024];
    loop {
        let count = file.read(&mut block).map_err(|source| Error::Read {
            path: path.to_owned(),
            source,
        })?;
        if count == 0 {
            break;
        }
        digest.update(&block[..count]);
    }
    Ok(format!("{:x}", digest.finalize()))
}

fn proof_agent_instruction_body() -> String {
    FORMAL_SQL_PROOF_AGENT_PROMPT.trim_end().to_owned() + "\n"
}

fn static_prompt_and_primer_bytes() -> usize {
    FORMAL_SQL_PROOF_AGENT_PROMPT.trim_end().len() + 1 + FORMAL_SQL_SEMANTIC_PRIMER.len()
}

fn launch_environment_policy(
    fixed_variables: &[String],
    host_environment_allowlist: &[&str],
    explicit_contract_variables: &[&str],
) -> LaunchEnvironmentPolicy {
    LaunchEnvironmentPolicy {
        schema_version: 1,
        inherited_environment_cleared: true,
        fixed_variables: fixed_variables.to_vec(),
        host_environment_allowlist: host_environment_allowlist
            .iter()
            .map(|name| (*name).to_owned())
            .collect(),
        explicit_contract_variables: explicit_contract_variables
            .iter()
            .map(|name| (*name).to_owned())
            .collect(),
        unlisted_environment_policy: "excluded_by_env_clear_before_process_start".to_owned(),
        explicitly_excluded_variables: EXPLICITLY_EXCLUDED_HOST_ENVIRONMENT
            .iter()
            .map(|name| (*name).to_owned())
            .collect(),
        explicitly_excluded_prefixes: EXPLICITLY_EXCLUDED_HOST_ENVIRONMENT_PREFIXES
            .iter()
            .map(|prefix| (*prefix).to_owned())
            .collect(),
    }
}

fn trusted_checker_environment_policy() -> LaunchEnvironmentPolicy {
    launch_environment_policy(
        &[
            format!("PATH={TRUSTED_CHECKER_PATH}"),
            format!("HOME={TRUSTED_CHECKER_HOME}"),
            format!("LC_ALL={FIXED_HOST_LOCALE}"),
            format!("LANG={FIXED_HOST_LOCALE}"),
        ],
        &[],
        TRUSTED_CHECKER_EXPLICIT_ENVIRONMENT,
    )
}

fn proof_agent_launcher_environment_policy() -> LaunchEnvironmentPolicy {
    launch_environment_policy(
        &[
            format!("PATH={PROOF_AGENT_LAUNCHER_PATH}"),
            format!("LC_ALL={FIXED_HOST_LOCALE}"),
            format!("LANG={FIXED_HOST_LOCALE}"),
        ],
        PROOF_AGENT_LAUNCHER_HOST_ENVIRONMENT_ALLOWLIST,
        PROOF_AGENT_LAUNCHER_EXPLICIT_ENVIRONMENT,
    )
}

fn proof_agent_storage_limit_bytes(options: &Config) -> Result<u64> {
    options
        .proof_agent_storage_limit_mib
        .checked_mul(1024 * 1024)
        .filter(|bytes| *bytes > 4096)
        .ok_or_else(|| {
            Error::ProofAgentCommand(
                "proof-agent storage limit must be a positive MiB value representable as bytes"
                    .to_owned(),
            )
        })
}

fn base_proof_agent_configuration(
    options: &Config,
    context: Option<ProofAgentContext>,
) -> Result<ProofAgentConfiguration> {
    let writable_storage_limit_bytes = proof_agent_storage_limit_bytes(options)?;
    Ok(ProofAgentConfiguration {
        lemma_availability: options.lemma_availability,
        rocq_session_pool_size: options.rocq_session_limits.max_sessions,
        rocq_session_pool_rss_mib: options.rocq_session_limits.retained_rss_mib,
        enabled: options.execution_mode == ExecutionMode::Verify,
        command: options.proof_agent_command.clone(),
        resume_command: options.proof_agent_resume_command.clone(),
        timeout_seconds: options.proof_agent_timeout_seconds,
        trusted_check_timeout_seconds: options.proof_check_timeout_seconds,
        memory_limit_mib: options.proof_agent_memory_limit_mib,
        diagnostic_timeout_policy: "positive_request_bounded_only_by_current_invocation_deadline"
            .to_owned(),
        diagnostic_transport: PROOF_AGENT_DIAGNOSTIC_TRANSPORT.to_owned(),
        diagnostic_cache_policy: PROOF_AGENT_DIAGNOSTIC_CACHE_POLICY.to_owned(),
        diagnostic_budget_policy: "bounded_by_invocation_deadline".to_owned(),
        diagnostic_checker_parallelism_max: PROOF_AGENT_DIAGNOSTIC_PARALLELISM_MAX,
        diagnostic_checker_scheduling_policy: PROOF_AGENT_DIAGNOSTIC_SCHEDULING_POLICY.to_owned(),
        compile_checkpoint_policy: PROOF_AGENT_COMPILE_CHECKPOINT_POLICY.to_owned(),
        scratch_persistence_policy: PROOF_AGENT_SCRATCH_PERSISTENCE_POLICY.to_owned(),
        scratch_allowed_extensions: SCRATCH_ALLOWED_EXTENSIONS
            .iter()
            .map(|extension| (*extension).to_owned())
            .collect(),
        writable_storage_limit_bytes,
        writable_storage_policy: PROOF_AGENT_WRITABLE_STORAGE_POLICY.to_owned(),
        diagnostic_cache_manifest_path: None,
        diagnostic_cache_manifest_sha256: None,
        session_restart_after_failed_rounds: PROOF_AGENT_SESSION_RESTART_AFTER_FAILED_ROUNDS,
        session_home_policy: PROOF_AGENT_SESSION_HOME_POLICY.to_owned(),
        trusted_checker_environment_policy: trusted_checker_environment_policy(),
        proof_agent_launcher_environment_policy: proof_agent_launcher_environment_policy(),
        docker_image: options.proof_docker_image.clone(),
        static_prompt_and_primer_bytes: ablation::static_bytes(options.lemma_availability),
        trusted_environment_preflight: None,
        context,
    })
}

fn bind_trusted_diagnostic_cache_manifest(
    artifacts: &ArtifactWriter,
    configuration: &mut ProofAgentConfiguration,
) -> Result<()> {
    let relative = "proof-stage/proof-agent/trusted-diagnostic-cache/SHA256SUMS";
    let path = artifacts.root().join(relative);
    let manifest = std::fs::read(&path).map_err(|source| Error::Read { path, source })?;
    configuration.diagnostic_cache_manifest_path = Some(relative.to_owned());
    configuration.diagnostic_cache_manifest_sha256 = Some(sha256_hex(&manifest));
    Ok(())
}

pub(super) fn prepare_formal_input(
    artifacts: &ArtifactWriter,
    input: &VerificationInput,
    options: &Config,
) -> Result<PreparedFormalInput> {
    let ir_frontend = ShellSqlIrFrontend::new(options.calcite_ir_command.clone())
        .with_environment(options.sql_environment);
    let ir_input = input.load_ir(&ir_frontend)?;
    let verification_input_path = artifacts.root().join("input/verification-input.json");
    let integrity_contract_path = artifacts.root().join("input/integrity-contract.json");
    artifacts.write_json("input/sql-environment.json", &ir_input.sql_environment())?;
    let schema_ir_sha256 =
        artifacts.write_json_with_sha256("input/schema-ir.json", ir_input.schema_ir())?;
    let source_ir_sha256 =
        artifacts.write_json_with_sha256("input/source-ir.json", &ir_input.source_program_ir())?;
    let target_ir_sha256 =
        artifacts.write_json_with_sha256("input/target-ir.json", &ir_input.target_program_ir())?;

    let lowering_config = LoweringConfig {
        sql_time_zone: options.sql_time_zone.clone(),
        sql_environment: options.sql_environment,
    };
    let mut lowering_report =
        lower_verification_input_with_mode(&ir_input, &lowering_config, options.verification_mode);
    lowering_report.input_bindings = Some(ProofInputBindings {
        schema_version: 1,
        case_id: input.integrity_contract().case_id.clone(),
        schema_sql_sha256: sha256_hex(input.schema_sql().as_bytes()),
        source_sql_sha256: sha256_hex(input.source_sql().as_bytes()),
        target_sql_sha256: sha256_hex(input.target_sql().as_bytes()),
        verification_input_sha256: sha256_file_hex(&verification_input_path)?,
        integrity_contract_sha256: sha256_file_hex(&integrity_contract_path)?,
        schema_ir_sha256,
        source_ir_sha256,
        target_ir_sha256,
    });
    if lowering_report.schema.schema.is_some()
        && lowering_report.query_module.is_some()
        && lowering_report.proof_module.is_some()
    {
        lowering_report.goal_module = Some(FormalProofModule {
            rocq_module: if lowering_programs_have_query_bindings(&lowering_report) {
                formal_sql_bound_goal_module(options.verification_mode)
            } else {
                formal_sql_goal_module(options.verification_mode)
            },
        });
    }
    artifacts.write_json("proof-stage/formal-sql-lowering.json", &lowering_report)?;
    let observation_certificates = analyze_observation_certificates(&lowering_report, input);
    Ok(PreparedFormalInput {
        ir_input,
        lowering_report,
        observation_certificates,
    })
}

fn lowering_programs_have_query_bindings(lowering: &ProofLoweringReport) -> bool {
    lowering
        .source
        .statements
        .iter()
        .chain(&lowering.target.statements)
        .any(|statement| !statement.bindings.is_empty())
}

fn remove_proof_workspace_for_formal_witness_restart(artifacts: &ArtifactWriter) -> Result<()> {
    let workspace = artifacts.root().join("proof-stage/formal-sql");
    match std::fs::symlink_metadata(&workspace) {
        Ok(metadata) => {
            if metadata.file_type().is_symlink() || !metadata.is_dir() {
                return Err(Error::ProofAgentCommand(format!(
                    "refusing to replace non-directory proof workspace {} for a fixed-witness restart",
                    workspace.display()
                )));
            }
            std::fs::remove_dir_all(&workspace).map_err(|source| Error::Write {
                path: workspace,
                source,
            })?;
        }
        Err(source) if source.kind() == std::io::ErrorKind::NotFound => {}
        Err(source) => {
            return Err(Error::Read {
                path: workspace,
                source,
            });
        }
    }
    // Keep the manifest-validated live compiled prefix so the witness-only
    // preflight can reuse its unchanged Schema/Queries objects. That preflight
    // atomically replaces the old Witness and drops every old proof module.
    // Problem checkpoints remain witness-bound and must not cross generations.
    for relative in ["proof-stage/proof-agent/initial-problem-checkpoint"] {
        let path = artifacts.root().join(relative);
        match std::fs::symlink_metadata(&path) {
            Ok(metadata) => {
                if metadata.file_type().is_symlink() || !metadata.is_dir() {
                    return Err(Error::ProofAgentCommand(format!(
                        "refusing to replace non-directory fixed-witness proof state {}",
                        path.display()
                    )));
                }
                std::fs::remove_dir_all(&path).map_err(|source| Error::Write {
                    path: path.clone(),
                    source,
                })?;
            }
            Err(source) if source.kind() == std::io::ErrorKind::NotFound => {}
            Err(source) => return Err(Error::Read { path, source }),
        }
    }
    let proof_agent_root = artifacts.root().join("proof-stage/proof-agent");
    match std::fs::symlink_metadata(&proof_agent_root) {
        Ok(metadata) if metadata.file_type().is_symlink() || !metadata.is_dir() => {
            return Err(Error::ProofAgentCommand(format!(
                "refusing to inspect unsafe fixed-witness proof state root {}",
                proof_agent_root.display()
            )));
        }
        Ok(_) => {
            for entry in std::fs::read_dir(&proof_agent_root).map_err(|source| Error::Read {
                path: proof_agent_root.clone(),
                source,
            })? {
                let entry = entry.map_err(|source| Error::Read {
                    path: proof_agent_root.clone(),
                    source,
                })?;
                let name = entry.file_name();
                let name = name.to_string_lossy();
                if !name.starts_with(".logos-trusted-diagnostic-cache-old.")
                    && !name.starts_with(".logos-trusted-diagnostic-cache.")
                {
                    continue;
                }
                let path = entry.path();
                let metadata = std::fs::symlink_metadata(&path).map_err(|source| Error::Read {
                    path: path.clone(),
                    source,
                })?;
                if metadata.file_type().is_symlink() || !metadata.is_dir() {
                    return Err(Error::ProofAgentCommand(format!(
                        "refusing to discard unsafe interrupted module-cache state {}",
                        path.display()
                    )));
                }
                std::fs::remove_dir_all(&path).map_err(|source| Error::Write { path, source })?;
            }
        }
        Err(source) if source.kind() == std::io::ErrorKind::NotFound => {}
        Err(source) => {
            return Err(Error::Read {
                path: proof_agent_root,
                source,
            });
        }
    }
    let checker_tmp_root = proof_agent_root.join("host-tmp");
    match std::fs::symlink_metadata(&checker_tmp_root) {
        Ok(metadata) if metadata.file_type().is_symlink() || !metadata.is_dir() => {
            return Err(Error::ProofAgentCommand(format!(
                "refusing to inspect unsafe trusted-checker scratch root {}",
                checker_tmp_root.display()
            )));
        }
        Ok(_) => {
            for entry in std::fs::read_dir(&checker_tmp_root).map_err(|source| Error::Read {
                path: checker_tmp_root.clone(),
                source,
            })? {
                let entry = entry.map_err(|source| Error::Read {
                    path: checker_tmp_root.clone(),
                    source,
                })?;
                if !entry
                    .file_name()
                    .to_string_lossy()
                    .starts_with("trusted-rocq-check.")
                {
                    continue;
                }
                let path = entry.path();
                let metadata = std::fs::symlink_metadata(&path).map_err(|source| Error::Read {
                    path: path.clone(),
                    source,
                })?;
                if metadata.file_type().is_symlink() || !metadata.is_dir() {
                    return Err(Error::ProofAgentCommand(format!(
                        "refusing to discard unsafe interrupted checker state {}",
                        path.display()
                    )));
                }
                std::fs::remove_dir_all(&path).map_err(|source| Error::Write { path, source })?;
            }
        }
        Err(source) if source.kind() == std::io::ErrorKind::NotFound => {}
        Err(source) => {
            return Err(Error::Read {
                path: checker_tmp_root,
                source,
            });
        }
    }
    Ok(())
}

fn restart_proof_workspace_with_formal_witness(
    artifacts: &ArtifactWriter,
    input: &VerificationInput,
    ir_input: &VerificationIr,
    lowering_report: &ProofLoweringReport,
    observation_certificates: &ObservationCertificateReport,
    snapshot: &FormalWitnessSnapshot,
    options: &Config,
    workspace_generation: usize,
) -> Result<(
    ProofWorkspace,
    PreparedContext,
    TrustedProofSources,
    TrustedCheckInvocation,
    CompileCheckpoint,
    ProofAgentSessionHome,
)> {
    let schema = lowering_report.schema.schema.as_ref().ok_or_else(|| {
        Error::ProofAgentCommand(
            "cannot restart a proof on a fixed witness without a lowered FormalSQL schema"
                .to_owned(),
        )
    })?;
    let query_module = lowering_report.query_module.as_ref().ok_or_else(|| {
        Error::ProofAgentCommand(
            "cannot restart a proof on a fixed witness without generated Queries.v".to_owned(),
        )
    })?;
    let proof_module = lowering_report.proof_module.as_ref().ok_or_else(|| {
        Error::ProofAgentCommand(
            "cannot restart a proof on a fixed witness without the generated Problem.v scaffold"
                .to_owned(),
        )
    })?;
    let goal_module = lowering_report.goal_module.as_ref().ok_or_else(|| {
        Error::ProofAgentCommand(
            "cannot restart a proof on a fixed witness without generated Goal.v".to_owned(),
        )
    })?;

    // Validate and render the typed snapshot before replacing any live proof
    // state.  Once that succeeds, replace the entire mutable workspace rather
    // than trying to patch Witness.v in place: Problem.v checkpoints, scratch
    // lemmas, handoff files, compiled debris, and context bindings all belong
    // to the old database and must not cross the witness boundary.
    let witness_modules = formal_sql_witness_modules(schema, Some(snapshot))?;
    remove_proof_workspace_for_formal_witness_restart(artifacts)?;
    let (workspace, context) = write_proof_workspace(
        artifacts,
        input,
        ir_input,
        lowering_report,
        observation_certificates,
        &schema.rocq_module,
        &query_module.rocq_module,
        &witness_modules,
        &proof_module.rocq_module,
        &goal_module.rocq_module,
        options,
    )?;
    let trusted_sources = capture_trusted_proof_sources(artifacts)?;
    // Reuse the independently checked Schema/Queries prefix, compile and check
    // only the replacement Witness, then atomically publish the new prefix
    // before compiling the fresh Problem.v checkpoint.
    let preflight =
        validate_trusted_rocq_environment(artifacts, options, workspace_generation, true)?;
    let checkpoint =
        establish_initial_problem_compile_checkpoint(artifacts, options, workspace_generation)?;
    let session_home = ProofAgentSessionHome::create(artifacts)?;
    Ok((
        workspace,
        context,
        trusted_sources,
        preflight,
        checkpoint,
        session_home,
    ))
}

pub(super) fn run_proof_stage(
    artifacts: &ArtifactWriter,
    input: &VerificationInput,
    options: &Config,
    prepared: Option<PreparedFormalInput>,
    formal_witness_snapshot: Option<crate::validation::FormalWitnessSnapshot>,
    initial_feedback: Option<String>,
    mut handoff_handler: Option<&mut ProofHandoffHandler<'_>>,
) -> Result<ProofReport> {
    let started = Instant::now();
    let mut proof_agent_configuration = base_proof_agent_configuration(options, None)?;
    artifacts.write_json(
        "proof-stage/proof-agent/config.json",
        &proof_agent_configuration,
    )?;
    let PreparedFormalInput {
        ir_input,
        lowering_report,
        observation_certificates,
    } = match prepared {
        Some(prepared) => prepared,
        None => prepare_formal_input(artifacts, input, options)?,
    };
    let (mut proof_workspace, mut proof_agent_context) =
        if let (Some(schema), Some(query_module), Some(proof_module), Some(goal_module)) = (
            lowering_report.schema.schema.as_ref(),
            lowering_report.query_module.as_ref(),
            lowering_report.proof_module.as_ref(),
            lowering_report.goal_module.as_ref(),
        ) {
            let witness_modules =
                formal_sql_witness_modules(schema, formal_witness_snapshot.as_ref())?;
            let (workspace, context) = write_proof_workspace(
                artifacts,
                input,
                &ir_input,
                &lowering_report,
                &observation_certificates,
                &schema.rocq_module,
                &query_module.rocq_module,
                &witness_modules,
                &proof_module.rocq_module,
                &goal_module.rocq_module,
                options,
            )?;
            (Some(workspace), Some(context))
        } else {
            (None, None)
        };
    if let Some(context) = proof_agent_context.as_ref() {
        proof_agent_configuration.context = Some(context.report.clone());
    }
    artifacts.write_json(
        "proof-stage/proof-agent/config.json",
        &proof_agent_configuration,
    )?;
    let mut trusted_sources =
        if options.execution_mode == ExecutionMode::Verify && proof_workspace.is_some() {
            Some(capture_trusted_proof_sources(artifacts)?)
        } else {
            None
        };
    let mut proof_workspace_generation = 1usize;
    let mut initial_problem_compile_checkpoint = None;
    if trusted_sources.is_some() {
        let preflight = validate_trusted_rocq_environment(
            artifacts,
            options,
            proof_workspace_generation,
            false,
        )?;
        bind_trusted_diagnostic_cache_manifest(artifacts, &mut proof_agent_configuration)?;
        initial_problem_compile_checkpoint = Some(establish_initial_problem_compile_checkpoint(
            artifacts,
            options,
            proof_workspace_generation,
        )?);
        proof_agent_configuration.trusted_environment_preflight = Some(preflight);
        artifacts.write_json(
            "proof-stage/proof-agent/config.json",
            &proof_agent_configuration,
        )?;
    }
    let mut proof_agent_session_home = trusted_sources
        .as_ref()
        .map(|_| ProofAgentSessionHome::create(artifacts))
        .transpose()?;
    let proof_deadline = Instant::now()
        .checked_add(Duration::from_secs(options.proof_agent_timeout_seconds))
        .unwrap_or_else(Instant::now);
    let mut proof_agent_rounds = Vec::new();
    let mut proof_workspace_transitions = Vec::new();
    // PostgreSQL feedback remains untrusted navigation.  When the host also
    // captured a typed snapshot, the workspace above binds it through the
    // read-only Witness.v; without that snapshot the countermodel branch stays
    // unavailable and only the independent equivalence branch can certify.
    let mut repair_feedback = initial_feedback;
    let mut proof_search_timed_out = false;
    let mut proof_resume_unavailable = false;
    let mut proof_manual_review_reason = None;
    let mut proof_agent_session_id = None;
    let mut proof_agent_cumulative_usage = None;
    let mut proof_agent_session_generation = 1usize;
    let mut next_session_restart_reason = None;
    let mut next_checkpoint_transition = ProofCheckpointTransition::NewWorkspaceInitial;
    let mut failed_rounds_in_session = 0usize;
    let mut problem_compile_checkpoint = initial_problem_compile_checkpoint;
    let mut proof_usage_complete = true;

    if trusted_sources.is_some()
        && proof_agent_session_home.is_some()
        && proof_agent_context.is_some()
    {
        let mut round = 1;
        loop {
            let remaining = proof_deadline.saturating_duration_since(Instant::now());
            let Some(round_budget) =
                proof_agent_round_budget(remaining, options.proof_check_timeout_seconds)
            else {
                proof_search_timed_out = true;
                break;
            };

            let session_restarted = round > 1 && proof_agent_session_id.is_none();
            let session_restart_reason = next_session_restart_reason;
            let checkpoint_transition = next_checkpoint_transition;
            let active_problem_compile_checkpoint = problem_compile_checkpoint
                .as_ref()
                .expect("proof-agent execution starts from a host-compiled Problem.v checkpoint");
            if active_problem_compile_checkpoint.workspace_generation != proof_workspace_generation
            {
                return Err(Error::ProofAgentCommand(format!(
                    "refusing to reuse workspace generation {} Problem.v checkpoint in generation {}",
                    active_problem_compile_checkpoint.workspace_generation,
                    proof_workspace_generation
                )));
            }
            let active_problem_compile_checkpoint_sha256 =
                active_problem_compile_checkpoint.sha256.clone();
            let session_generation_home = proof_agent_session_home
                .as_ref()
                .expect("an enabled proof agent has an isolated session home")
                .generation_path(proof_agent_session_generation)?;
            write_proof_agent_round_prompt(
                artifacts,
                options.lemma_availability,
                options.verification_mode,
                round,
                remaining,
                round_budget,
                repair_feedback.as_deref(),
                proof_agent_session_generation,
                session_restarted,
            )?;
            let mut round_result = execute_proof_agent_round(
                artifacts,
                options,
                trusted_sources
                    .as_ref()
                    .expect("an enabled proof agent has captured trusted sources"),
                proof_agent_context
                    .as_ref()
                    .expect("an enabled proof agent has a validated context"),
                &session_generation_home,
                proof_agent_session_id.as_deref(),
                proof_agent_cumulative_usage.as_ref(),
                round,
                proof_workspace_generation,
                proof_agent_session_generation,
                session_restarted,
                session_restart_reason,
                checkpoint_transition,
                &active_problem_compile_checkpoint_sha256,
                remaining,
                round_budget,
            )?;
            next_session_restart_reason = None;
            next_checkpoint_transition = ProofCheckpointTransition::Continued;
            let round_success = round_result.log.success;
            let handoff = round_result.log.counterexample_handoff.clone();
            let observed_session_id = round_result.log.session_id.clone();
            let session_resumable = round_result.session_resumable;
            proof_usage_complete &= round_result.cumulative_usage.is_some();
            let observed_cumulative_usage = round_result.cumulative_usage.take();
            if let Some(checkpoint) = round_result.problem_compile_checkpoint.take() {
                problem_compile_checkpoint = Some(checkpoint);
            }
            repair_feedback = Some(round_result.repair_feedback);

            if proof_agent_session_id.is_none() && session_resumable {
                proof_agent_session_id = observed_session_id;
            }
            if let Some(cumulative_usage) = observed_cumulative_usage {
                proof_agent_cumulative_usage = Some(cumulative_usage);
            }
            if !round_success && !session_resumable {
                // Preserve the exact missing-session fact in the round
                // evidence before any handoff resolution. It is fatal only
                // if the workflow still needs this old session; a terminal
                // result or fixed-witness generation replacement does not.
                round_result.log.error = Some(match round_result.log.error.take() {
                    Some(error) => format!(
                        "{error}; proof repair cannot continue because Codex did not report the expected valid session UUID"
                    ),
                    None => "proof repair cannot continue because Codex did not report the expected valid session UUID".to_owned(),
                });
            }
            proof_agent_rounds.push(round_result.log);

            match resolve_proof_round(
                proof_agent_rounds.last().expect("the round was recorded"),
                session_resumable,
                handoff_handler.as_deref_mut(),
            )? {
                ProofRoundDisposition::Complete => break,
                ProofRoundDisposition::NeedsManualReview(reason) => {
                    proof_manual_review_reason = Some(reason);
                    break;
                }
                ProofRoundDisposition::Continue(feedback) => {
                    if feedback.is_some() {
                        repair_feedback = feedback;
                    }
                }
                ProofRoundDisposition::ResumeUnavailable(feedback) => {
                    if feedback.is_some() {
                        repair_feedback = feedback;
                    }
                    proof_resume_unavailable = true;
                    break;
                }
                ProofRoundDisposition::RestartWithFormalWitness { feedback, snapshot } => {
                    let from_workspace_generation = proof_workspace_generation;
                    let to_workspace_generation =
                        from_workspace_generation.checked_add(1).ok_or_else(|| {
                            Error::ProofAgentCommand(
                                "proof workspace generation overflowed".to_owned(),
                            )
                        })?;
                    let from_context_manifest_sha256 = proof_agent_context
                        .as_ref()
                        .expect("an enabled proof agent has a validated context")
                        .report
                        .manifest_sha256
                        .clone();
                    let triggering_handoff_sha256 = canonical_json_sha256(
                        handoff
                            .as_ref()
                            .expect("witness restart requires a handoff"),
                    )?;
                    let from_trusted_diagnostic_cache =
                        archive_trusted_diagnostic_cache(artifacts, from_workspace_generation)?;
                    let (
                        restarted_workspace,
                        restarted_context,
                        restarted_trusted_sources,
                        restarted_preflight,
                        restarted_checkpoint,
                        restarted_session_home,
                    ) = restart_proof_workspace_with_formal_witness(
                        artifacts,
                        input,
                        &ir_input,
                        &lowering_report,
                        &observation_certificates,
                        &snapshot,
                        options,
                        to_workspace_generation,
                    )?;
                    let to_context_manifest_sha256 =
                        restarted_context.report.manifest_sha256.clone();
                    let checkpoint_evidence = restarted_checkpoint.report_evidence(artifacts)?;
                    proof_workspace_transitions.push(ProofWorkspaceTransition {
                        after_round: round,
                        from_workspace_generation,
                        to_workspace_generation,
                        reason: ProofWorkspaceTransitionReason::FixedWitnessReplacement,
                        triggering_handoff_sha256,
                        from_context_manifest_sha256,
                        to_context_manifest_sha256,
                        from_trusted_diagnostic_cache,
                        new_trusted_environment_preflight: restarted_preflight,
                        new_initial_problem_compile_checkpoint: checkpoint_evidence,
                    });
                    proof_workspace = Some(restarted_workspace);
                    proof_agent_configuration.context = Some(restarted_context.report.clone());
                    proof_agent_context = Some(restarted_context);
                    trusted_sources = Some(restarted_trusted_sources);
                    bind_trusted_diagnostic_cache_manifest(
                        artifacts,
                        &mut proof_agent_configuration,
                    )?;
                    problem_compile_checkpoint = Some(restarted_checkpoint);
                    proof_workspace_generation = to_workspace_generation;
                    proof_agent_session_home = Some(restarted_session_home);
                    proof_agent_session_id = None;
                    proof_agent_cumulative_usage = None;
                    proof_agent_session_generation =
                        proof_agent_session_generation.saturating_add(1);
                    next_session_restart_reason =
                        Some(ProofSessionRestartReason::FixedWitnessReplacement);
                    next_checkpoint_transition = ProofCheckpointTransition::NewWorkspaceInitial;
                    failed_rounds_in_session = 0;
                    proof_resume_unavailable = false;
                    repair_feedback = Some(format!(
                        "The counterexample stage type-checked the candidate DML and losslessly froze a new typed database after proof round {round}. PostgreSQL did not execute the query pair or certify divergence. The host replaced the live FormalSQL proof workspace, regenerated Witness.v and its context manifest, created a fresh generated Problem.v checkpoint while preserving prior generation evidence, discarded witness-bound scratch, and started a fresh proof session. Use the unified trusted Rocq selector to prove either equivalence or complete outcome separation on exactly this fixed witness. Counterexample-stage feedback:\n{feedback}"
                    ));
                    artifacts.write_json(
                        "proof-stage/proof-agent/config.json",
                        &proof_agent_configuration,
                    )?;
                    round = round.saturating_add(1);
                    continue;
                }
            }

            if proof_deadline
                .saturating_duration_since(Instant::now())
                .is_zero()
            {
                proof_search_timed_out = true;
                break;
            }
            failed_rounds_in_session = failed_rounds_in_session.saturating_add(1);
            if failed_rounds_in_session >= PROOF_AGENT_SESSION_RESTART_AFTER_FAILED_ROUNDS {
                let checkpoint = problem_compile_checkpoint
                    .as_ref()
                    .expect("proof-agent session restart retains a host-compiled checkpoint");
                let rejected_problem_path =
                    artifacts.root().join("proof-stage/formal-sql/Problem.v");
                let rejected_problem =
                    std::fs::read(&rejected_problem_path).map_err(|source| Error::Read {
                        path: rejected_problem_path.clone(),
                        source,
                    })?;
                let rejected_sha256 = sha256_hex(&rejected_problem);
                restore_problem_compile_checkpoint(
                    &rejected_problem_path,
                    checkpoint,
                    proof_workspace_generation,
                )?;
                let checkpoint_feedback = format!(
                    "The prior session reached the unsuccessful-turn limit. The host restored the latest Problem.v checkpoint that independently passed problem-only compilation (sha256 {}, captured at round {}, diagnostic {}). The rejected candidate (sha256 {}) remains preserved in its round snapshot. Continue from the restored compile-clean file and the bounded diagnostics below.",
                    checkpoint.sha256, checkpoint.round, checkpoint.sequence, rejected_sha256
                );
                repair_feedback = Some(match repair_feedback.take() {
                    Some(feedback) => format!("{checkpoint_feedback}\n\n{feedback}"),
                    None => checkpoint_feedback,
                });
                proof_agent_session_id = None;
                proof_agent_cumulative_usage = None;
                proof_agent_session_generation = proof_agent_session_generation.saturating_add(1);
                next_session_restart_reason = Some(ProofSessionRestartReason::FailedRoundLimit);
                next_checkpoint_transition = ProofCheckpointTransition::RestoredExisting;
                failed_rounds_in_session = 0;
            }
            round = round.saturating_add(1);
        }
    }

    let proof_agent = proof_agent_rounds.last().cloned();
    let backend_status = if proof_resume_unavailable {
        BackendStatus::ProofAgentFailed
    } else {
        proof_backend_status(
            proof_workspace.is_some(),
            proof_search_timed_out,
            proof_manual_review_reason.is_some(),
            proof_agent.as_ref().map(|run| (run.success, run.exit_code)),
        )
    };
    let certification = match backend_status {
        BackendStatus::ProofComplete => match proof_agent
            .as_ref()
            .and_then(|run| run.candidate_claim)
        {
            Some(VerificationClaimKind::FormalCountermodel) => {
                Some(CertificationLevel::FormalCountermodel)
            }
            Some(VerificationClaimKind::Equivalence) => match options.verification_mode {
                VerificationMode::SafeUnconditional => Some(CertificationLevel::SafeUnconditional),
                VerificationMode::OutcomeUnconditional => {
                    Some(CertificationLevel::OutcomeUnconditional)
                }
                VerificationMode::Conditional => proof_agent
                    .as_ref()
                    .and_then(|run| run.precondition_source)
                    .map(|source| match source {
                        PreconditionSource::Derived => CertificationLevel::ConditionalDerived,
                        PreconditionSource::External => CertificationLevel::ConditionalExternal,
                    }),
            },
            None => None,
        },
        _ => None,
    };
    let status_reason = match backend_status {
        BackendStatus::LoweringBlocked => {
            "FormalSQL/Rocq lowering did not produce a complete schema, query pair, and proof module; no proof agent or checker was run"
                .to_owned()
        }
        BackendStatus::ProofComplete => {
            format!(
                "FormalSQL/Rocq produced an audited {} certificate accepted by Rocq",
                certification
                    .map(CertificationLevel::label)
                    .unwrap_or_else(|| options.verification_mode.label())
            )
        }
        BackendStatus::ProofAgentRunCompleted => {
            proof_agent_completion_reason()
        }
        BackendStatus::ProofSearchTimedOut => {
            format!(
                "FormalSQL/Rocq proof repair timed out after {} seconds and {} round(s)",
                options.proof_agent_timeout_seconds,
                proof_agent_rounds.len()
            )
        }
        BackendStatus::NeedsManualReview => format!(
            "FormalSQL/Rocq proof search stopped without accepting an EQ or NEQ certificate after the proof agent or proof-directed counterexample synthesis requested manual review: {}",
            proof_manual_review_reason
                .as_deref()
                .expect("manual-review backend status carries its host-authored reason")
        ),
        BackendStatus::ProofAgentFailed => {
            "FormalSQL/Rocq proof agent failed; see proof-stage/proof-agent logs".to_owned()
        }
        BackendStatus::WorkspaceGenerated => {
            "FormalSQL/Rocq proof backend generated a proof workspace; automated proof search is not enabled"
                .to_owned()
        }
    };
    let llm_usage = LlmUsage::checked_sum(
        proof_agent_rounds
            .iter()
            .filter_map(|round| round.usage.as_ref()),
    )?;
    if trusted_sources.is_some() {
        // Module diagnostics append immutable source/object pairs to the same
        // host-only cache. Refresh the report binding so config.json describes
        // the exact final dependency cache rather than only its empty preflight
        // prefix.
        bind_trusted_diagnostic_cache_manifest(artifacts, &mut proof_agent_configuration)?;
        artifacts.write_json(
            "proof-stage/proof-agent/config.json",
            &proof_agent_configuration,
        )?;
    }
    let report = ProofReport {
        backend: Backend::FormalSqlRocq,
        sql_environment: options.sql_environment,
        verification_mode: options.verification_mode,
        backend_status,
        certification,
        status_reason,
        proof_workspace,
        proof_agent_configuration,
        proof_agent,
        proof_agent_rounds,
        proof_workspace_transitions,
        proof_search_timed_out,
        usage_complete: proof_usage_complete,
        elapsed_ms: started.elapsed().as_millis(),
        llm_usage,
    };
    artifacts.write_json("proof-stage/report.json", &report)?;
    Ok(report)
}

fn proof_agent_completion_reason() -> String {
    "FormalSQL/Rocq proof repair rounds completed, but no generated workspace passed every deterministic audit and trusted Rocq check"
        .to_owned()
}

fn proof_backend_status(
    workspace_generated: bool,
    proof_search_timed_out: bool,
    needs_manual_review: bool,
    agent_run: Option<(bool, Option<i32>)>,
) -> BackendStatus {
    match (workspace_generated, agent_run) {
        (false, _) => BackendStatus::LoweringBlocked,
        (true, Some((true, _))) => BackendStatus::ProofComplete,
        (true, _) if needs_manual_review => BackendStatus::NeedsManualReview,
        (true, _) if proof_search_timed_out => BackendStatus::ProofSearchTimedOut,
        (true, Some((false, Some(0)))) => BackendStatus::ProofAgentRunCompleted,
        (true, Some((false, _))) => BackendStatus::ProofAgentFailed,
        (true, None) => BackendStatus::WorkspaceGenerated,
    }
}

fn proof_agent_host_reserve_seconds(trusted_check_timeout_seconds: u64) -> u64 {
    trusted_check_timeout_seconds.saturating_add(PROOF_AGENT_HOST_KILL_MARGIN_SECONDS)
}

fn proof_agent_round_budget(
    remaining: Duration,
    trusted_check_timeout_seconds: u64,
) -> Option<Duration> {
    let available = remaining.checked_sub(Duration::from_secs(
        proof_agent_host_reserve_seconds(trusted_check_timeout_seconds),
    ))?;
    (!available.is_zero()).then_some(available)
}

fn is_codex_session_id(value: &str) -> bool {
    value.len() == 36
        && value.bytes().enumerate().all(|(index, byte)| {
            if matches!(index, 8 | 13 | 18 | 23) {
                byte == b'-'
            } else {
                byte.is_ascii_hexdigit()
            }
        })
}

fn render_proof_agent_resume_command(template: &str, session_id: &str) -> Result<String> {
    if !is_codex_session_id(session_id) {
        return Err(Error::ProofAgentCommand(format!(
            "refusing to resume malformed Codex session ID {session_id:?}"
        )));
    }
    if !template.contains("{session_id}") {
        return Err(Error::ProofAgentCommand(
            "proof-agent resume command must contain the {session_id} placeholder".to_owned(),
        ));
    }
    Ok(template.replace("{session_id}", session_id))
}

fn configure_proof_agent_launcher_environment(process: &mut Command) {
    process
        .env_clear()
        .env("PATH", PROOF_AGENT_LAUNCHER_PATH)
        .env("LC_ALL", FIXED_HOST_LOCALE)
        .env("LANG", FIXED_HOST_LOCALE);
    for name in PROOF_AGENT_LAUNCHER_HOST_ENVIRONMENT_ALLOWLIST {
        if let Some(value) = std::env::var_os(name) {
            process.env(name, value);
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn proof_agent_launcher_command(
    script_path: &Path,
    logos_repo_root: &Path,
    proof_workdir: &Path,
    session_home: &Path,
    round_stage: &Path,
    diagnostic_socket: &Path,
    diagnostic_nonce: &str,
    docker_image: &str,
    agent_command: &str,
    memory_limit_mib: u64,
    storage_limit_bytes: u64,
    round_budget: Duration,
) -> Command {
    let mut process = Command::new(TRUSTED_HOST_BASH);
    configure_proof_agent_launcher_environment(&mut process);
    process
        .arg(script_path)
        .env("LOGOS_REPO_ROOT", logos_repo_root)
        .env("LOGOS_PROOF_WORKDIR", proof_workdir)
        .env("LOGOS_PROOF_AGENT_CODEX_HOME", session_home)
        .env("LOGOS_PROOF_AGENT_STAGE", round_stage)
        .env("LOGOS_PROOF_DIAGNOSTIC_SOCKET", diagnostic_socket)
        .env("LOGOS_PROOF_DIAGNOSTIC_NONCE", diagnostic_nonce)
        .env("LOGOS_SOLVER_IMAGE", docker_image)
        .env("LOGOS_PROOF_AGENT_COMMAND", agent_command)
        .env(
            "LOGOS_PROOF_AGENT_MEMORY_LIMIT",
            format!("{memory_limit_mib}m"),
        )
        .env(
            "LOGOS_PROOF_AGENT_STORAGE_LIMIT_BYTES",
            storage_limit_bytes.to_string(),
        )
        .env(
            "LOGOS_PROOF_AGENT_TIMEOUT",
            round_budget.as_secs().max(1).to_string(),
        );
    process
}

fn materialize_agent_output_file(
    stage: &Path,
    stage_name: &str,
    destination: &Path,
    launcher_bytes: &[u8],
) -> Result<()> {
    if let Some(parent) = destination.parent() {
        std::fs::create_dir_all(parent).map_err(|source| Error::CreateDir {
            path: parent.to_owned(),
            source,
        })?;
    }
    let staged = stage.join(stage_name);
    let mut staged_input = match std::fs::symlink_metadata(&staged) {
        Ok(metadata) if metadata.file_type().is_file() && !metadata.file_type().is_symlink() => {
            Some(File::open(&staged).map_err(|source| Error::Read {
                path: staged.clone(),
                source,
            })?)
        }
        Ok(_) => {
            return Err(Error::ProofAgentCommand(format!(
                "proof-agent launcher output is not a regular file: {}",
                staged.display()
            )));
        }
        Err(source) if source.kind() == std::io::ErrorKind::NotFound => None,
        Err(source) => {
            return Err(Error::Read {
                path: staged,
                source,
            });
        }
    };
    if let Ok(metadata) = std::fs::symlink_metadata(destination)
        && !metadata.file_type().is_file()
    {
        return Err(Error::ProofAgentCommand(format!(
            "proof-agent output destination is not a regular file: {}",
            destination.display()
        )));
    }
    let mut output = OpenOptions::new()
        .write(true)
        .create(true)
        .truncate(true)
        .mode(0o600)
        .open(destination)
        .map_err(|source| Error::Write {
            path: destination.to_owned(),
            source,
        })?;
    std::fs::set_permissions(destination, std::fs::Permissions::from_mode(0o600)).map_err(
        |source| Error::Write {
            path: destination.to_owned(),
            source,
        },
    )?;
    if let Some(input) = staged_input.as_mut() {
        std::io::copy(input, &mut output).map_err(|source| Error::Write {
            path: destination.to_owned(),
            source,
        })?;
    } else {
        // Older launchers emitted Codex JSONL directly on stdout/stderr. Keep
        // that deterministic compatibility path only when no staged output
        // file exists; new file-backed launchers must never concatenate two
        // independent streams into one events artifact.
        output
            .write_all(launcher_bytes)
            .map_err(|source| Error::Write {
                path: destination.to_owned(),
                source,
            })?;
    }
    output.flush().map_err(|source| Error::Write {
        path: destination.to_owned(),
        source,
    })
}

fn append_output_file(path: &Path, label: &str, bytes: &[u8]) -> Result<()> {
    if bytes.is_empty() {
        return Ok(());
    }
    let mut output = OpenOptions::new()
        .append(true)
        .open(path)
        .map_err(|source| Error::Write {
            path: path.to_owned(),
            source,
        })?;
    output
        .write_all(format!("\n[{label}]\n").as_bytes())
        .and_then(|()| output.write_all(bytes))
        .and_then(|()| output.flush())
        .map_err(|source| Error::Write {
            path: path.to_owned(),
            source,
        })
}

fn candidate_problem_has_compile_authority(
    candidate_sha256: &str,
    active_checkpoint_sha256: &str,
    invocations: &[DiagnosticCheckerInvocation],
) -> bool {
    candidate_sha256 == active_checkpoint_sha256
        || invocations.iter().any(|invocation| {
            invocation.compile_passed == Some(true)
                && invocation.problem_compile_passed == Some(true)
                && invocation.mode.as_deref() == Some("problem")
                && invocation.candidate_path.as_deref() == Some("Problem.v")
                && invocation.compile_checkpoint_advanced == Some(true)
                && invocation.candidate_sha256.as_deref() == Some(candidate_sha256)
        })
}

fn bounded_trusted_check_stream_feedback(label: &str, bytes: &[u8]) -> Option<String> {
    if bytes.is_empty() {
        return None;
    }
    let omitted = bytes
        .len()
        .saturating_sub(TRUSTED_CHECK_REPAIR_FEEDBACK_STREAM_MAX_BYTES);
    let mut feedback = if omitted == 0 {
        format!("[trusted final Rocq check {label}]")
    } else {
        format!("[trusted final Rocq check {label} tail; {omitted} earlier bytes omitted]")
    };
    feedback.push('\n');
    feedback.push_str(&String::from_utf8_lossy(&bytes[omitted..]));
    Some(feedback)
}

fn trusted_final_check_repair_feedback(stdout: &[u8], stderr: &[u8]) -> Option<String> {
    let feedback = [
        bounded_trusted_check_stream_feedback("stdout", stdout),
        bounded_trusted_check_stream_feedback("stderr", stderr),
    ]
    .into_iter()
    .flatten()
    .collect::<Vec<_>>()
    .join("\n");
    (!feedback.is_empty()).then_some(feedback)
}

fn execute_proof_agent_round(
    artifacts: &ArtifactWriter,
    options: &Config,
    trusted_sources: &TrustedProofSources,
    proof_agent_context: &PreparedContext,
    session_home: &Path,
    session_id: Option<&str>,
    previous_cumulative_usage: Option<&CodexInvocationUsage>,
    round: usize,
    workspace_generation: usize,
    session_generation: usize,
    session_restarted: bool,
    session_restart_reason: Option<ProofSessionRestartReason>,
    checkpoint_transition: ProofCheckpointTransition,
    active_problem_compile_checkpoint_sha256: &str,
    remaining: Duration,
    round_budget: Duration,
) -> Result<AgentRoundResult> {
    let command = match session_id {
        Some(session_id) => {
            render_proof_agent_resume_command(&options.proof_agent_resume_command, session_id)?
        }
        None => options.proof_agent_command.clone(),
    };
    let docker_image = options.proof_docker_image.clone();
    let started_ms_since_epoch = now_ms_since_epoch();
    let started = Instant::now();
    let round_dir = format!("proof-stage/proof-agent/rounds/{round:02}");
    let stdout_path = format!("{round_dir}/stdout.txt");
    let stderr_path = format!("{round_dir}/stderr.txt");
    let events_path = format!("{round_dir}/events.jsonl");
    let proof_workdir = artifacts.root().join("proof-stage/formal-sql");
    validate_proof_agent_context(artifacts, proof_agent_context)?;
    clear_stale_proof_artifact(
        &proof_workdir,
        COUNTEREXAMPLE_HANDOFF_FILE,
        "counterexample handoff",
    )?;
    clear_stale_proof_artifact(
        &proof_workdir,
        AUTHORITY_CLOSURE_FILE,
        "proof-agent authority closure",
    )?;
    // Never execute the copy mounted read-write into the agent container. An
    // agent could append host-side shell commands to a running script and have
    // bash execute them after `docker run` returns. Materialize the embedded,
    // trusted launcher in a sibling directory that is not writable by Docker.
    let script_path = write_trusted_proof_agent_launcher(artifacts)?;
    let logos_repo_root = options
        .logos_repo_root
        .clone()
        .map(Ok)
        .unwrap_or_else(std::env::current_dir)
        .map_err(|source| Error::ProofAgentCommand(source.to_string()))?;
    let trusted_checker_path = write_trusted_rocq_checker(artifacts)?;
    let round_stage = ProofAgentRoundStage::create(artifacts)?;
    hydrate_round_scratch(&proof_workdir, round_stage.path())?;
    let diagnostic_broker = DiagnosticBroker::start(
        artifacts.root(),
        round,
        workspace_generation,
        &trusted_checker_path,
        &proof_workdir,
        &logos_repo_root,
        options.proof_rocq_opam_switch.as_deref(),
        Some(active_problem_compile_checkpoint_sha256),
        proof_agent_storage_limit_bytes(options)?,
        Instant::now()
            .checked_add(round_budget)
            .unwrap_or_else(Instant::now),
    )?
    .with_session_limits(options.rocq_session_limits)?;
    let mut process = proof_agent_launcher_command(
        &script_path,
        &logos_repo_root,
        &proof_workdir,
        session_home,
        round_stage.path(),
        diagnostic_broker.socket_path(),
        diagnostic_broker.nonce(),
        &docker_image,
        &command,
        options.proof_agent_memory_limit_mib,
        proof_agent_storage_limit_bytes(options)?,
        round_budget,
    );

    let process_output = process.output();
    let broker_outcome = diagnostic_broker.finish()?;
    let scratch_state = persist_round_scratch(round_stage.path(), &proof_workdir)?;
    let output = match process_output {
        Ok(output) => output,
        Err(source) => {
            let checked_workspace = snapshot_proof_workspace(artifacts, round)?;
            let candidate_problem =
                std::fs::read(checked_workspace.join("Problem.v")).map_err(|source| {
                    Error::Read {
                        path: checked_workspace.join("Problem.v"),
                        source,
                    }
                })?;
            let candidate_problem_sha256 = sha256_hex(&candidate_problem);
            let candidate_problem_compile_passed = candidate_problem_has_compile_authority(
                &candidate_problem_sha256,
                active_problem_compile_checkpoint_sha256,
                &broker_outcome.invocations,
            );
            let candidate_has_final_theorem = problem_declares_final_theorem(
                &String::from_utf8_lossy(&candidate_problem),
                options.verification_mode,
            );
            let updated_problem_compile_checkpoint_sha256 = broker_outcome
                .latest_checkpoint
                .as_ref()
                .map(|checkpoint| checkpoint.sha256.clone());
            let WorkspaceAudit {
                audit,
                candidate_claim,
                precondition_source,
                precondition_definition,
            } = audit_proof_workspace_for_mode(
                artifacts,
                &checked_workspace,
                trusted_sources,
                options.verification_mode,
                AuditPurpose::Certificate,
            )?;
            let log = AgentRunLog {
                round,
                workspace_generation,
                session_generation,
                session_restarted,
                session_restart_reason,
                checkpoint_transition,
                command,
                context_manifest_sha256: proof_agent_context.report.manifest_sha256.clone(),
                remaining_proof_search_seconds: remaining.as_secs(),
                round_budget_seconds: round_budget.as_secs(),
                session_id: None,
                docker_image,
                started_ms_since_epoch,
                elapsed_ms: started.elapsed().as_millis(),
                success: false,
                exit_code: None,
                proof_check_exit_code: None,
                proof_check_elapsed_ms: None,
                proof_check_timeout_seconds: None,
                proof_check_timed_out: false,
                authority_closure_path: None,
                authority_closure_sha256: None,
                authority_closure_bytes: None,
                candidate_problem_sha256,
                candidate_problem_compile_passed,
                candidate_has_final_theorem,
                candidate_claim,
                active_problem_compile_checkpoint_sha256: active_problem_compile_checkpoint_sha256
                    .to_owned(),
                updated_problem_compile_checkpoint_sha256,
                compile_checkpoint_restored: checkpoint_transition
                    == ProofCheckpointTransition::RestoredExisting,
                diagnostic_checker_telemetry_path: None,
                diagnostic_checker_invocations: broker_outcome.invocations,
                diagnostic_checker_telemetry_error: broker_outcome.trusted_environment_error,
                diagnostic_requests_seen: broker_outcome.requests_seen,
                diagnostic_requested_timeout_seconds_reserved: broker_outcome
                    .requested_timeout_seconds_reserved,
                diagnostic_accepted_count: broker_outcome.accepted_count,
                diagnostic_rejected_source_audit_count: broker_outcome.rejected_source_audit_count,
                diagnostic_other_rejected_request_count: broker_outcome
                    .other_rejected_request_count,
                diagnostic_accepted_source_audits: broker_outcome.accepted_source_audits,
                diagnostic_rejected_source_audits: broker_outcome.rejected_source_audits,
                scratch_file_count: scratch_state.file_count,
                scratch_bytes: scratch_state.total_bytes,
                stdout_path,
                stderr_path,
                stdout_bytes: 0,
                stderr_bytes: 0,
                events_path,
                usage: None,
                usage_error: Some(source.to_string()),
                audit,
                precondition_source,
                precondition_definition,
                counterexample_handoff: None,
                error: Some(source.to_string()),
            };
            write_agent_run_log(artifacts, &round_dir, &log, None)?;
            return Err(Error::ProofAgentCommand(source.to_string()));
        }
    };
    let stdout_artifact = artifacts.root().join(&stdout_path);
    let stderr_artifact = artifacts.root().join(&stderr_path);
    let events_artifact = artifacts.root().join(&events_path);
    materialize_agent_output_file(
        round_stage.path(),
        "agent-stdout",
        &stdout_artifact,
        &output.stdout,
    )?;
    materialize_agent_output_file(
        round_stage.path(),
        "agent-stderr",
        &stderr_artifact,
        &output.stderr,
    )?;
    if let Some(parent) = events_artifact.parent() {
        std::fs::create_dir_all(parent).map_err(|source| Error::CreateDir {
            path: parent.to_owned(),
            source,
        })?;
    }
    std::fs::copy(&stdout_artifact, &events_artifact).map_err(|source| Error::Write {
        path: events_artifact.clone(),
        source,
    })?;

    // The untrusted container is gone before this snapshot is created.  Both
    // the lexical audit and the final Rocq compiler consume this trusted copy,
    // so an agent descendant cannot swap Problem.v between the two checks.
    let authority_closure = match validate_authority_closure(&proof_workdir, &logos_repo_root) {
        Ok(binding) => binding,
        Err(error) => {
            let launcher_stdout = String::from_utf8_lossy(&output.stdout).into_owned();
            let launcher_stderr = String::from_utf8_lossy(&output.stderr).into_owned();
            return Err(Error::TrustedRocqEnvironment(format!(
                "{error}; proof-agent launcher exited with status {}; stderr: {}; stdout: {}",
                output.status, launcher_stderr, launcher_stdout
            )));
        }
    };
    validate_proof_agent_context(artifacts, proof_agent_context)?;
    let checked_workspace = snapshot_proof_workspace(artifacts, round)?;
    let (counterexample_handoff, handoff_error) = load_counterexample_handoff(&proof_workdir);
    if let Some(error) = handoff_error.as_ref() {
        append_output_file(&stderr_artifact, "counterexample handoff", error.as_bytes())?;
    }
    let audit_purpose = match counterexample_handoff
        .as_ref()
        .map(|handoff| handoff.decision)
    {
        Some(ProofAgentDecision::NeedsManualReview) => AuditPurpose::ManualReview,
        _ => AuditPurpose::Certificate,
    };
    let WorkspaceAudit {
        audit,
        candidate_claim,
        precondition_source,
        precondition_definition,
    } = audit_proof_workspace_for_mode(
        artifacts,
        &checked_workspace,
        trusted_sources,
        options.verification_mode,
        audit_purpose,
    )?;
    let mapped_stdout = ReadOnlyMappedFile::open_utf8(&stdout_artifact)?;
    let parsed_thread_id = parse_codex_thread_id(mapped_stdout.as_str());
    let parsed_usage = parse_codex_jsonl(mapped_stdout.as_str());
    drop(mapped_stdout);
    let observed_session_id = parsed_thread_id.as_ref().ok().and_then(|session_id| {
        is_codex_session_id(session_id).then(|| session_id.to_ascii_lowercase())
    });
    let session_continuity_error = match (session_id, observed_session_id.as_deref()) {
        (Some(expected), Some(observed)) if expected != observed => Some(format!(
            "resumed Codex session changed from {expected} to {observed}"
        )),
        (Some(expected), None) => Some(format!(
            "resumed Codex invocation did not report the expected session UUID {expected}"
        )),
        _ => None,
    };
    let session_resumable = observed_session_id.is_some() && session_continuity_error.is_none();
    let reconciliation_state_error = match (session_id, previous_cumulative_usage) {
        (Some(expected), Some(previous)) if previous.session_id != expected => Some(format!(
            "proof usage state belongs to session {}, expected {expected}",
            previous.session_id
        )),
        (None, Some(previous)) => Some(format!(
            "initial Codex invocation unexpectedly has prior usage for session {}",
            previous.session_id
        )),
        _ => None,
    };
    let continuity_error = reconciliation_state_error.or(session_continuity_error);
    // `events.jsonl` above retains Codex's authoritative cumulative record.
    // Normalize only the report-facing usage to the invocation delta so the
    // existing report sums count a resumed session exactly once.
    let (cumulative_usage, usage, usage_error) = match &parsed_usage {
        Err(error) => (None, None, Some(error.to_string())),
        Ok(record) if !is_codex_session_id(&record.session_id) => (
            None,
            None,
            Some(format!(
                "Codex thread.started returned malformed session UUID {:?}",
                record.session_id
            )),
        ),
        Ok(record) if continuity_error.is_some() => (None, None, continuity_error),
        Ok(record) => {
            let mut cumulative = record.clone();
            cumulative.session_id.make_ascii_lowercase();
            match cumulative.incremental_usage(previous_cumulative_usage) {
                Ok(increment) => (Some(cumulative), Some(increment), None),
                Err(error) => (None, None, Some(error.to_string())),
            }
        }
    };
    let diagnostic_checker_telemetry_error = broker_outcome.trusted_environment_error.clone();
    let diagnostic_requests_seen = broker_outcome.requests_seen;
    let diagnostic_requested_timeout_seconds_reserved =
        broker_outcome.requested_timeout_seconds_reserved;
    let diagnostic_accepted_count = broker_outcome.accepted_count;
    let diagnostic_rejected_source_audit_count = broker_outcome.rejected_source_audit_count;
    let diagnostic_other_rejected_request_count = broker_outcome.other_rejected_request_count;
    let diagnostic_accepted_source_audits = broker_outcome.accepted_source_audits;
    let diagnostic_rejected_source_audits = broker_outcome.rejected_source_audits;
    let diagnostic_checker_invocations = broker_outcome.invocations;
    let diagnostic_checker_telemetry_path = if diagnostic_checker_invocations.is_empty() {
        None
    } else {
        let relative = format!("{round_dir}/interactive-diagnostics.json");
        artifacts.write_json(&relative, &diagnostic_checker_invocations)?;
        Some(relative)
    };
    let latest_problem_compile_checkpoint = broker_outcome.latest_checkpoint;
    let updated_problem_compile_checkpoint_sha256 = latest_problem_compile_checkpoint
        .as_ref()
        .map(|checkpoint| checkpoint.sha256.clone());
    let latest_diagnostic_feedback = broker_outcome.latest_feedback;
    let mut trusted_environment_error = broker_outcome.trusted_environment_error;
    let candidate_problem_path = checked_workspace.join("Problem.v");
    let candidate_problem_sha256 = sha256_file_hex(&candidate_problem_path)?;
    let candidate_problem_compile_passed = candidate_problem_has_compile_authority(
        &candidate_problem_sha256,
        active_problem_compile_checkpoint_sha256,
        &diagnostic_checker_invocations,
    );
    let mapped_candidate_problem = ReadOnlyMappedFile::open_utf8(&candidate_problem_path)?;
    let candidate_has_final_theorem = problem_declares_final_theorem(
        mapped_candidate_problem.as_str(),
        options.verification_mode,
    );
    drop(mapped_candidate_problem);
    let attempt_trusted_check =
        audit.passed && candidate_problem_compile_passed && candidate_has_final_theorem;
    let mut proof_check_exit_code = None;
    let mut proof_check_elapsed_ms = None;
    let mut proof_check_timeout_seconds = None;
    let mut proof_check_timed_out = false;
    let mut proof_check_error = None;
    let mut trusted_final_check_feedback = None;
    let proof_check_success = if attempt_trusted_check {
        let check_started = Instant::now();
        let check_budget = remaining
            .saturating_sub(started.elapsed())
            .min(Duration::from_secs(options.proof_check_timeout_seconds));
        proof_check_timeout_seconds = Some(check_budget.as_secs());
        if check_budget.is_zero() {
            proof_check_elapsed_ms = Some(check_started.elapsed().as_millis());
            proof_check_timed_out = true;
            proof_check_error = Some(
                "proof-search deadline exhausted before the trusted final Rocq check".to_owned(),
            );
            false
        } else {
            let check = run_trusted_rocq_check(
                &trusted_checker_path,
                &checked_workspace,
                &logos_repo_root,
                options.proof_rocq_opam_switch.as_deref(),
                check_budget,
            );
            match check {
                Ok(check_output) => {
                    proof_check_elapsed_ms = Some(check_started.elapsed().as_millis());
                    proof_check_exit_code = check_output.status.code();
                    proof_check_timed_out = matches!(check_output.status.code(), Some(124 | 137));
                    append_output_file(
                        &stdout_artifact,
                        "trusted Rocq check",
                        &check_output.stdout,
                    )?;
                    append_output_file(
                        &stderr_artifact,
                        "trusted Rocq check",
                        &check_output.stderr,
                    )?;
                    if check_output.status.success() {
                        true
                    } else {
                        trusted_final_check_feedback = trusted_final_check_repair_feedback(
                            &check_output.stdout,
                            &check_output.stderr,
                        );
                        let error = format!(
                            "trusted Rocq check exited with status {}",
                            check_output.status
                        );
                        if is_trusted_rocq_environment_failure(check_output.status.code()) {
                            trusted_environment_error = Some(format!(
                                "{error}: {}",
                                String::from_utf8_lossy(&check_output.stderr)
                            ));
                        }
                        proof_check_error = Some(error);
                        false
                    }
                }
                Err(source) => {
                    proof_check_elapsed_ms = Some(check_started.elapsed().as_millis());
                    let error = format!("failed to start trusted Rocq check: {source}");
                    trusted_environment_error = Some(error.clone());
                    proof_check_error = Some(error);
                    false
                }
            }
        }
    } else if audit.passed {
        let reason = if !candidate_problem_compile_passed {
            match latest_diagnostic_feedback.as_deref() {
                Some(feedback) => format!(
                    "the final Problem.v candidate did not pass an interactive host problem-only compilation; continue in the same proof session and repair it using the latest diagnostic: {feedback}"
                ),
                None => "the final Problem.v candidate did not receive a successful interactive host problem-only compilation; continue in the same proof session, select diagnostic timeouts from the current invocation budget while editing, and retain a compile-clean candidate"
                    .to_owned(),
            }
        } else if !candidate_has_final_theorem {
            let theorem = match options.verification_mode {
                VerificationMode::SafeUnconditional | VerificationMode::OutcomeUnconditional => {
                    "generated_queries_verified"
                }
                VerificationMode::Conditional => "generated_queries_equivalent",
            };
            format!(
                "the final Problem.v candidate compiled and was checkpointed, but it does not yet contain the required {theorem} theorem; continue compositionally from this compile-clean state"
            )
        } else {
            "the final Problem.v candidate was not eligible for the trusted final check under the deterministic proof audit"
                .to_owned()
        };
        proof_check_error = Some(format!(
            "trusted Rocq check was not attempted because {reason}"
        ));
        false
    } else {
        false
    };
    let stdout_bytes = usize::try_from(
        std::fs::metadata(&stdout_artifact)
            .map_err(|source| Error::Read {
                path: stdout_artifact.clone(),
                source,
            })?
            .len(),
    )
    .map_err(|_| Error::ProofAgentCommand("agent stdout size is not addressable".to_owned()))?;
    let stderr_bytes = usize::try_from(
        std::fs::metadata(&stderr_artifact)
            .map_err(|source| Error::Read {
                path: stderr_artifact.clone(),
                source,
            })?
            .len(),
    )
    .map_err(|_| Error::ProofAgentCommand("agent stderr size is not addressable".to_owned()))?;
    let success = audit.passed && proof_check_success;
    let log = AgentRunLog {
        round,
        workspace_generation,
        session_generation,
        session_restarted,
        session_restart_reason,
        checkpoint_transition,
        command,
        context_manifest_sha256: proof_agent_context.report.manifest_sha256.clone(),
        remaining_proof_search_seconds: remaining.as_secs(),
        round_budget_seconds: round_budget.as_secs(),
        session_id: observed_session_id,
        docker_image,
        started_ms_since_epoch,
        elapsed_ms: started.elapsed().as_millis(),
        success,
        exit_code: output.status.code(),
        proof_check_exit_code,
        proof_check_elapsed_ms,
        proof_check_timeout_seconds,
        proof_check_timed_out,
        authority_closure_path: Some(format!(
            "{round_dir}/checked-workspace/{AUTHORITY_CLOSURE_FILE}"
        )),
        authority_closure_sha256: Some(authority_closure.sha256),
        authority_closure_bytes: Some(authority_closure.bytes),
        candidate_problem_sha256,
        candidate_problem_compile_passed,
        candidate_has_final_theorem,
        candidate_claim,
        active_problem_compile_checkpoint_sha256: active_problem_compile_checkpoint_sha256
            .to_owned(),
        updated_problem_compile_checkpoint_sha256,
        compile_checkpoint_restored: checkpoint_transition
            == ProofCheckpointTransition::RestoredExisting,
        diagnostic_checker_telemetry_path,
        diagnostic_checker_invocations,
        diagnostic_checker_telemetry_error,
        diagnostic_requests_seen,
        diagnostic_requested_timeout_seconds_reserved,
        diagnostic_accepted_count,
        diagnostic_rejected_source_audit_count,
        diagnostic_other_rejected_request_count,
        diagnostic_accepted_source_audits,
        diagnostic_rejected_source_audits,
        scratch_file_count: scratch_state.file_count,
        scratch_bytes: scratch_state.total_bytes,
        stdout_path,
        stderr_path,
        stdout_bytes,
        stderr_bytes,
        events_path,
        usage,
        usage_error: usage_error.clone(),
        audit,
        precondition_source,
        precondition_definition,
        counterexample_handoff,
        error: if success {
            None
        } else if let Some(error) = proof_check_error.or(handoff_error) {
            Some(error)
        } else if !output.status.success() {
            Some(format!("proof agent exited with status {}", output.status))
        } else if let Some(error) = usage_error {
            Some(error)
        } else {
            Some("proof agent output failed deterministic proof audit".to_owned())
        },
    };
    let repair_feedback =
        proof_round_repair_feedback(&log, trusted_final_check_feedback.as_deref());
    write_agent_run_log(
        artifacts,
        &round_dir,
        &log,
        cumulative_usage.as_ref().map(|record| &record.usage),
    )?;
    if let Some(error) = trusted_environment_error {
        return Err(Error::TrustedRocqEnvironment(error));
    }
    Ok(AgentRoundResult {
        log,
        repair_feedback,
        cumulative_usage,
        session_resumable,
        problem_compile_checkpoint: latest_problem_compile_checkpoint,
    })
}

fn clear_stale_proof_artifact(
    proof_workdir: &Path,
    filename: &str,
    description: &str,
) -> Result<()> {
    let path = proof_workdir.join(filename);
    match std::fs::remove_file(&path) {
        Ok(()) => Ok(()),
        Err(source) if source.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(source) => Err(Error::ProofAgentCommand(format!(
            "failed to clear stale {description} {}: {source}",
            path.display()
        ))),
    }
}

fn validate_authority_closure(proof_workdir: &Path, logos_repo_root: &Path) -> Result<FileBinding> {
    let path = proof_workdir.join(AUTHORITY_CLOSURE_FILE);
    let metadata = std::fs::symlink_metadata(&path).map_err(|source| {
        Error::TrustedRocqEnvironment(format!(
            "failed to inspect host-generated proof-agent authority closure {}: {source}",
            path.display()
        ))
    })?;
    if !metadata.file_type().is_file() {
        return Err(Error::TrustedRocqEnvironment(format!(
            "host-generated proof-agent authority closure {} is not a regular file",
            path.display()
        )));
    }
    let bytes = std::fs::read(&path).map_err(|source| Error::Read {
        path: path.clone(),
        source,
    })?;
    let text = std::str::from_utf8(&bytes).map_err(|source| {
        Error::TrustedRocqEnvironment(format!(
            "proof-agent authority closure {} is not UTF-8: {source}",
            path.display()
        ))
    })?;
    if !text.starts_with("# Logos proof-agent authority closure\n# schemaVersion: 1\n")
        || !text.contains("# policy: logos-proof-agent-source-object-closure-v1\n")
    {
        return Err(Error::TrustedRocqEnvironment(format!(
            "proof-agent authority closure {} has an unsupported policy or schema",
            path.display()
        )));
    }

    let declared_pairs = text
        .lines()
        .find_map(|line| line.strip_prefix("# sourcePairs: "))
        .and_then(|value| value.parse::<usize>().ok())
        .ok_or_else(|| {
            Error::TrustedRocqEnvironment(format!(
                "proof-agent authority closure {} has no valid sourcePairs declaration",
                path.display()
            ))
        })?;
    let declared_entries = declared_pairs.checked_mul(2).ok_or_else(|| {
        Error::TrustedRocqEnvironment(
            "proof-agent authority closure sourcePairs declaration overflowed".to_owned(),
        )
    })?;
    if declared_pairs == 0 {
        return Err(Error::TrustedRocqEnvironment(
            "proof-agent authority closure cannot be empty".to_owned(),
        ));
    }
    let mut sources = BTreeSet::new();
    let mut objects = BTreeSet::new();
    let mut entries = 0usize;
    for line in text
        .lines()
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
    {
        let Some((digest, relative)) = line.split_once("  ") else {
            return Err(Error::TrustedRocqEnvironment(format!(
                "proof-agent authority closure {} contains a malformed digest line",
                path.display()
            )));
        };
        if digest.len() != 64 || !digest.bytes().all(|byte| byte.is_ascii_hexdigit()) {
            return Err(Error::TrustedRocqEnvironment(format!(
                "proof-agent authority closure {} contains a malformed SHA-256",
                path.display()
            )));
        }
        let allowed_vendor = relative.starts_with("vendor/FormalSQL/src/");
        let allowed_logos = relative
            .strip_prefix("theories/FormalSQL/")
            .is_some_and(|tail| !tail.contains('/'));
        let lower = relative.to_ascii_lowercase();
        if (!allowed_vendor && !allowed_logos)
            || relative.starts_with('/')
            || relative
                .split('/')
                .any(|part| matches!(part, "" | "." | ".."))
            || lower.contains("example")
            || lower.contains("/catalog/")
            || lower.contains("/build/")
            || lower.contains("/_build/")
            || lower.contains("/var/")
        {
            return Err(Error::TrustedRocqEnvironment(format!(
                "proof-agent authority closure {} exposes a path outside the source-backed non-example policy: {relative}",
                path.display()
            )));
        }
        let base = if let Some(base) = relative.strip_suffix(".vo") {
            objects.insert(base.to_owned());
            base
        } else if let Some(base) = relative.strip_suffix(".v") {
            sources.insert(base.to_owned());
            base
        } else {
            return Err(Error::TrustedRocqEnvironment(format!(
                "proof-agent authority closure {} contains a non-.v/.vo path: {relative}",
                path.display()
            )));
        };
        if base.is_empty() {
            return Err(Error::TrustedRocqEnvironment(
                "proof-agent authority closure contains an empty module path".to_owned(),
            ));
        }
        let host_path = logos_repo_root.join(relative);
        let host_metadata = std::fs::symlink_metadata(&host_path).map_err(|source| {
            Error::TrustedRocqEnvironment(format!(
                "authority closure path {} cannot be inspected: {source}",
                host_path.display()
            ))
        })?;
        if !host_metadata.file_type().is_file() {
            return Err(Error::TrustedRocqEnvironment(format!(
                "authority closure path is not a regular file: {}",
                host_path.display()
            )));
        }
        let host_bytes = std::fs::read(&host_path).map_err(|source| Error::Read {
            path: host_path.clone(),
            source,
        })?;
        if sha256_hex(&host_bytes) != digest {
            return Err(Error::TrustedRocqEnvironment(format!(
                "authority closure digest drifted after staging: {relative}"
            )));
        }
        entries = entries.saturating_add(1);
    }
    if sources != objects || sources.len() != declared_pairs || entries != declared_entries {
        return Err(Error::TrustedRocqEnvironment(format!(
            "proof-agent authority closure {} is not an exact set of {} source/object pairs",
            path.display(),
            declared_pairs
        )));
    }
    Ok(context_binding(AUTHORITY_CLOSURE_FILE, &bytes))
}

fn load_counterexample_handoff(
    proof_workdir: &Path,
) -> (Option<ProofCounterexampleHandoff>, Option<String>) {
    let path = proof_workdir.join(COUNTEREXAMPLE_HANDOFF_FILE);
    let metadata = match std::fs::symlink_metadata(&path) {
        Ok(metadata) => metadata,
        Err(source) if source.kind() == std::io::ErrorKind::NotFound => return (None, None),
        Err(source) => {
            return (
                None,
                Some(format!("failed to inspect {}: {source}", path.display())),
            );
        }
    };
    if !metadata.file_type().is_file() || metadata.file_type().is_symlink() {
        return (
            None,
            Some(format!(
                "{} is not a regular non-symlink file",
                path.display()
            )),
        );
    }
    let text = match std::fs::read_to_string(&path) {
        Ok(text) => text,
        Err(source) => {
            return (
                None,
                Some(format!("failed to read {}: {source}", path.display())),
            );
        }
    };
    let handoff = match serde_json::from_str::<ProofCounterexampleHandoff>(&text) {
        Ok(handoff) => handoff,
        Err(source) => {
            return (
                None,
                Some(format!(
                    "failed to parse {} as a proof counterexample handoff: {source}",
                    path.display()
                )),
            );
        }
    };
    if handoff.reason.trim().is_empty() || handoff.guidance.trim().is_empty() {
        return (
            None,
            Some(format!(
                "{} must contain non-empty reason and guidance fields",
                path.display()
            )),
        );
    }
    (Some(handoff), None)
}

fn write_agent_run_log(
    artifacts: &ArtifactWriter,
    round_dir: &str,
    log: &AgentRunLog,
    cumulative_usage: Option<&LlmUsage>,
) -> Result<()> {
    let record = AgentRunArtifact {
        log,
        cumulative_usage,
    };
    artifacts.write_json(format!("{round_dir}/run.json"), &record)?;
    artifacts.write_json("proof-stage/proof-agent/run.json", &record)
}

fn proof_round_repair_feedback(
    log: &AgentRunLog,
    trusted_final_check_feedback: Option<&str>,
) -> String {
    let mut feedback = format!(
        "Proof round {} did not pass the trusted certification boundary.",
        log.round
    );
    if let Some(error) = log.error.as_deref() {
        feedback.push_str("\nRecorded failure: ");
        feedback.push_str(error);
    }
    if !log.audit.findings.is_empty() {
        feedback.push_str("\nDeterministic audit findings:");
        for finding in &log.audit.findings {
            feedback.push_str(&format!(
                "\n- {}:{}: {} ({})",
                finding.path, finding.line, finding.excerpt, finding.token
            ));
        }
    }
    if let Some(trusted_feedback) = trusted_final_check_feedback {
        feedback.push_str("\nBounded host final-check diagnostics:");
        feedback.push('\n');
        feedback.push_str(trusted_feedback);
    }
    if log.stdout_bytes != 0 || log.stderr_bytes != 0 {
        if trusted_final_check_feedback.is_some() {
            feedback.push_str(
                "\nThe complete agent/trusted-check streams remain preserved in the prior round stdout/stderr artifacts for audit; only the bounded host final-check tails above are duplicated into this repair prompt.",
            );
        } else {
            feedback.push_str(
                "\nThe complete agent/trusted-check streams remain preserved in the prior round stdout/stderr artifacts for audit.",
            );
        }
    }
    feedback
}

fn write_trusted_proof_agent_launcher(artifacts: &ArtifactWriter) -> Result<PathBuf> {
    let path = artifacts
        .root()
        .join("proof-stage/proof-agent/trusted-launcher/run-proof-agent-docker.sh");
    let parent = path
        .parent()
        .expect("trusted proof-agent launcher has a parent directory");
    std::fs::create_dir_all(parent).map_err(|source| Error::CreateDir {
        path: parent.to_owned(),
        source,
    })?;
    std::fs::write(&path, FORMAL_SQL_DOCKER_AGENT_SCRIPT).map_err(|source| Error::Write {
        path: path.clone(),
        source,
    })?;
    Ok(path)
}

fn write_trusted_rocq_checker(artifacts: &ArtifactWriter) -> Result<PathBuf> {
    let path = artifacts
        .root()
        .join("proof-stage/proof-agent/trusted-launcher/run-trusted-rocq-check.sh");
    let parent = path
        .parent()
        .expect("trusted Rocq checker has a parent directory");
    std::fs::create_dir_all(parent).map_err(|source| Error::CreateDir {
        path: parent.to_owned(),
        source,
    })?;
    std::fs::write(&path, FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT).map_err(|source| Error::Write {
        path: path.clone(),
        source,
    })?;
    Ok(path)
}

fn validated_proof_module_sources(root: &Path) -> Result<Vec<(PathBuf, Vec<u8>)>> {
    let metadata = match std::fs::symlink_metadata(root) {
        Ok(metadata) => metadata,
        Err(source) if source.kind() == std::io::ErrorKind::NotFound => return Ok(Vec::new()),
        Err(source) => {
            return Err(Error::Read {
                path: root.to_owned(),
                source,
            });
        }
    };
    if metadata.file_type().is_symlink() || !metadata.is_dir() {
        return Err(Error::ProofAgentCommand(format!(
            "proof module root {} must be a regular non-symlink directory",
            root.display()
        )));
    }
    let mut modules = Vec::new();
    for entry in std::fs::read_dir(root).map_err(|source| Error::Read {
        path: root.to_owned(),
        source,
    })? {
        let entry = entry.map_err(|source| Error::Read {
            path: root.to_owned(),
            source,
        })?;
        let path = entry.path();
        let metadata = std::fs::symlink_metadata(&path).map_err(|source| Error::Read {
            path: path.clone(),
            source,
        })?;
        if metadata.file_type().is_symlink() || !metadata.file_type().is_file() {
            return Err(Error::ProofAgentCommand(format!(
                "proof module tree contains a non-regular entry: {}",
                path.display()
            )));
        }
        let file_name = entry.file_name().into_string().map_err(|_| {
            Error::ProofAgentCommand("proof module file name is not UTF-8".to_owned())
        })?;
        let relative = Path::new(PROOF_MODULE_DIRECTORY).join(&file_name);
        let candidate = relative
            .to_str()
            .ok_or_else(|| Error::ProofAgentCommand("proof module path is not UTF-8".to_owned()))?;
        validate_proof_module_candidate_path(candidate).map_err(Error::ProofAgentCommand)?;
        let bytes = std::fs::read(&path).map_err(|source| Error::Read {
            path: path.clone(),
            source,
        })?;
        std::str::from_utf8(&bytes).map_err(|source| {
            Error::ProofAgentCommand(format!(
                "proof module {} is not UTF-8: {source}",
                path.display()
            ))
        })?;
        modules.push((relative, bytes));
    }
    modules.sort_by(|left, right| left.0.cmp(&right.0));
    Ok(modules)
}

fn copy_witness_support_sources(source_root: &Path, destination_root: &Path) -> Result<()> {
    let source_modules = source_root.join(WITNESS_MODULE_DIRECTORY);
    let destination_modules = destination_root.join(WITNESS_MODULE_DIRECTORY);
    std::fs::create_dir(&destination_modules).map_err(|source| Error::CreateDir {
        path: destination_modules.clone(),
        source,
    })?;
    for entry in std::fs::read_dir(&source_modules).map_err(|source| Error::Read {
        path: source_modules.clone(),
        source,
    })? {
        let entry = entry.map_err(|source| Error::Read {
            path: source_modules.clone(),
            source,
        })?;
        let source_path = entry.path();
        let metadata = std::fs::symlink_metadata(&source_path).map_err(|source| Error::Read {
            path: source_path.clone(),
            source,
        })?;
        if metadata.file_type().is_symlink() || !metadata.file_type().is_file() {
            return Err(Error::TrustedRocqEnvironment(format!(
                "generated witness support entry is unsafe: {}",
                source_path.display()
            )));
        }
        let destination = destination_modules.join(entry.file_name());
        std::fs::copy(&source_path, &destination)
            .map(|_| ())
            .map_err(|source| Error::Write {
                path: destination,
                source,
            })?;
    }
    Ok(())
}

fn snapshot_proof_workspace(artifacts: &ArtifactWriter, round: usize) -> Result<PathBuf> {
    let source_dir = artifacts.root().join("proof-stage/formal-sql");
    let snapshot_dir = artifacts.root().join(format!(
        "proof-stage/proof-agent/rounds/{round:02}/checked-workspace"
    ));
    if let Some(parent) = snapshot_dir.parent() {
        std::fs::create_dir_all(parent).map_err(|source| Error::CreateDir {
            path: parent.to_owned(),
            source,
        })?;
    }
    std::fs::create_dir(&snapshot_dir).map_err(|source| Error::CreateDir {
        path: snapshot_dir.clone(),
        source,
    })?;
    for name in PROOF_SOURCE_FILES.iter().chain(PROOF_CONTEXT_FILES) {
        let source_path = source_dir.join(name);
        let bytes = std::fs::read(&source_path).map_err(|source| Error::Read {
            path: source_path,
            source,
        })?;
        let snapshot_path = snapshot_dir.join(name);
        std::fs::write(&snapshot_path, bytes).map_err(|source| Error::Write {
            path: snapshot_path,
            source,
        })?;
    }
    copy_witness_support_sources(&source_dir, &snapshot_dir)?;
    let module_snapshot_root = snapshot_dir.join(PROOF_MODULE_DIRECTORY);
    std::fs::create_dir(&module_snapshot_root).map_err(|source| Error::CreateDir {
        path: module_snapshot_root.clone(),
        source,
    })?;
    for (relative, bytes) in
        validated_proof_module_sources(&source_dir.join(PROOF_MODULE_DIRECTORY))?
    {
        let snapshot_path = snapshot_dir.join(&relative);
        std::fs::write(&snapshot_path, bytes).map_err(|source| Error::Write {
            path: snapshot_path,
            source,
        })?;
    }
    let authority_closure = source_dir.join(AUTHORITY_CLOSURE_FILE);
    if authority_closure.is_file() {
        let bytes = std::fs::read(&authority_closure).map_err(|source| Error::Read {
            path: authority_closure,
            source,
        })?;
        let snapshot_path = snapshot_dir.join(AUTHORITY_CLOSURE_FILE);
        std::fs::write(&snapshot_path, bytes).map_err(|source| Error::Write {
            path: snapshot_path,
            source,
        })?;
    }
    Ok(snapshot_dir)
}

fn write_pretty_json_file<T: Serialize>(path: PathBuf, value: &T) -> std::io::Result<()> {
    let mut bytes = serde_json::to_vec_pretty(value).map_err(std::io::Error::other)?;
    bytes.push(b'\n');
    std::fs::write(path, bytes)
}

fn capture_trusted_proof_sources(artifacts: &ArtifactWriter) -> Result<TrustedProofSources> {
    let source_dir = artifacts.root().join("proof-stage/formal-sql");
    TRUSTED_PROOF_SOURCE_FILES
        .iter()
        .map(|&name| {
            let path = source_dir.join(name);
            let text =
                std::fs::read_to_string(&path).map_err(|source| Error::Read { path, source })?;
            Ok((name, text))
        })
        .collect()
}

fn persist_initial_problem_compile_checkpoint_evidence(
    artifacts: &ArtifactWriter,
    workspace_generation: usize,
    problem_path: &Path,
    stdout: &[u8],
    stderr: &[u8],
    invocation: &DiagnosticCheckerInvocation,
) -> Result<PathBuf> {
    if workspace_generation == 0 {
        return Err(Error::ProofAgentCommand(
            "proof workspace generation must be positive".to_owned(),
        ));
    }
    let checkpoint_root = artifacts.root().join(format!(
        "proof-stage/proof-agent/workspace-generations/{workspace_generation:04}/initial-problem-checkpoint"
    ));
    let checkpoint_parent = checkpoint_root.parent().ok_or_else(|| {
        Error::ProofAgentCommand("initial problem checkpoint path has no parent".to_owned())
    })?;
    std::fs::create_dir_all(checkpoint_parent).map_err(|source| Error::CreateDir {
        path: checkpoint_parent.to_owned(),
        source,
    })?;
    std::fs::create_dir(&checkpoint_root).map_err(|source| {
        Error::ProofAgentCommand(format!(
            "refusing to replace create-once initial checkpoint evidence {}: {source}",
            checkpoint_root.display()
        ))
    })?;
    let checkpoint_path = checkpoint_root.join("Problem.v");
    std::fs::copy(problem_path, &checkpoint_path).map_err(|source| Error::Write {
        path: checkpoint_path.clone(),
        source,
    })?;
    for (name, bytes) in [("stdout.txt", stdout), ("stderr.txt", stderr)] {
        let path = checkpoint_root.join(name);
        std::fs::write(&path, bytes).map_err(|source| Error::Write { path, source })?;
    }
    let invocation_path = checkpoint_root.join("invocation.json");
    write_pretty_json_file(invocation_path.clone(), invocation).map_err(|source| Error::Write {
        path: invocation_path,
        source,
    })?;
    Ok(checkpoint_path)
}

fn establish_initial_problem_compile_checkpoint(
    artifacts: &ArtifactWriter,
    options: &Config,
    workspace_generation: usize,
) -> Result<CompileCheckpoint> {
    if workspace_generation == 0 {
        return Err(Error::ProofAgentCommand(
            "proof workspace generation must be positive".to_owned(),
        ));
    }
    let workspace = artifacts.root().join("proof-stage/formal-sql");
    let problem_path = workspace.join("Problem.v");
    let metadata = std::fs::symlink_metadata(&problem_path).map_err(|source| Error::Read {
        path: problem_path.clone(),
        source,
    })?;
    if !metadata.file_type().is_file() {
        return Err(Error::ProofAgentCommand(format!(
            "generated Problem.v {} is not a regular file",
            problem_path.display()
        )));
    }
    let _mapped_problem = ReadOnlyMappedFile::open_utf8(&problem_path)?;
    let problem_sha256 = sha256_file_hex(&problem_path)?;
    let checker = write_trusted_rocq_checker(artifacts)?;
    let logos_repo_root = options
        .logos_repo_root
        .clone()
        .map(Ok)
        .unwrap_or_else(std::env::current_dir)
        .map_err(|source| Error::TrustedRocqEnvironment(source.to_string()))?;
    let (mut invocation, output) = run_host_diagnostic_rocq_check(
        &checker,
        &workspace,
        &logos_repo_root,
        options.proof_rocq_opam_switch.as_deref(),
        CandidateKind::Problem,
        "Problem.v",
        options.proof_check_timeout_seconds,
        options.proof_check_timeout_seconds,
        None,
        None,
        checker::DiagnosticOperation::Check,
    );
    let (stdout, stderr) = output
        .as_ref()
        .map(|output| (output.stdout.as_slice(), output.stderr.as_slice()))
        .unwrap_or((&[][..], &[][..]));
    let passed = output
        .as_ref()
        .is_some_and(|output| output.status.success());
    invocation.sequence = Some(0);
    invocation.mode = Some("problem".to_owned());
    invocation.candidate_sha256 = Some(problem_sha256.clone());
    invocation.candidate_path = Some("Problem.v".to_owned());
    invocation.purpose = Some("assembly".to_owned());
    invocation.compile_passed = Some(passed);
    invocation.problem_compile_passed = Some(passed);
    invocation.compile_checkpoint_advanced = Some(passed);
    invocation.stdout_sha256 = Some(sha256_hex(stdout));
    invocation.stderr_sha256 = Some(sha256_hex(stderr));
    let checkpoint_path = persist_initial_problem_compile_checkpoint_evidence(
        artifacts,
        workspace_generation,
        &problem_path,
        stdout,
        stderr,
        &invocation,
    )?;
    if passed {
        return Ok(CompileCheckpoint {
            path: checkpoint_path,
            sha256: problem_sha256,
            workspace_generation,
            round: 0,
            sequence: 0,
        });
    }
    let message = format!(
        "generated Problem.v failed the initial host problem-only compilation (exit {:?}, timed out {}, elapsed {} ms): {}",
        invocation.exit_code,
        invocation.timed_out,
        invocation.elapsed_ms,
        String::from_utf8_lossy(stderr)
    );
    if is_trusted_rocq_environment_failure(invocation.exit_code) {
        Err(Error::TrustedRocqEnvironment(message))
    } else {
        Err(Error::ProofAgentCommand(message))
    }
}

fn restore_problem_compile_checkpoint(
    problem_path: &Path,
    checkpoint: &CompileCheckpoint,
    workspace_generation: usize,
) -> Result<()> {
    if checkpoint.workspace_generation != workspace_generation {
        return Err(Error::ProofAgentCommand(format!(
            "refusing to restore workspace generation {} Problem.v checkpoint in generation {}",
            checkpoint.workspace_generation, workspace_generation
        )));
    }
    if sha256_file_hex(&checkpoint.path)? != checkpoint.sha256 {
        return Err(Error::ProofAgentCommand(
            "refusing to restore a Problem.v checkpoint whose retained bytes do not match its digest"
                .to_owned(),
        ));
    }
    let parent = problem_path.parent().ok_or_else(|| {
        Error::ProofAgentCommand(format!(
            "Problem.v checkpoint path has no parent: {}",
            problem_path.display()
        ))
    })?;
    let temporary = parent.join(format!(
        ".Problem.v.restore-{}-{}",
        std::process::id(),
        now_ms_since_epoch()
    ));
    std::fs::copy(&checkpoint.path, &temporary).map_err(|source| Error::Write {
        path: temporary.clone(),
        source,
    })?;
    if let Err(source) = std::fs::rename(&temporary, problem_path) {
        let _ = std::fs::remove_file(&temporary);
        return Err(Error::Write {
            path: problem_path.to_owned(),
            source,
        });
    }
    if sha256_file_hex(problem_path)? != checkpoint.sha256 {
        return Err(Error::ProofAgentCommand(format!(
            "restored Problem.v digest drifted from retained checkpoint {}",
            checkpoint.sha256
        )));
    }
    Ok(())
}

fn render_proof_agent_prompt(
    verification_mode: VerificationMode,
    round: Option<(usize, Duration, Duration, usize, bool)>,
    feedback: Option<&str>,
) -> String {
    let include_static_instructions = round
        .as_ref()
        .is_none_or(|(round, _, _, _, session_restarted)| *round == 1 || *session_restarted);
    let mut prompt = format!(
        "Selected verification mode: `{}`.\n",
        verification_mode.label(),
    );
    if let Some((round, remaining, round_budget, session_generation, session_restarted)) = round {
        let final_theorem = match verification_mode {
            VerificationMode::SafeUnconditional | VerificationMode::OutcomeUnconditional => {
                "generated_queries_verified"
            }
            VerificationMode::Conditional => "generated_queries_equivalent",
        };
        prompt.push_str(&format!(
            "Proof continuation invocation: {round}. Remaining overall proof-search time: {} seconds.\n",
            remaining.as_secs()
        ));
        prompt.push_str(&format!(
            "Invocation budget: {} seconds; the trusted final check is reserved separately. Diagnostics are sequential (parallelism {PROOF_AGENT_DIAGNOSTIC_PARALLELISM_MAX}) and share this invocation's wall-clock deadline; there is no completed-check or broker-request quota. End only after exact Problem.v has compile-clean authority (a current problem-mode pass or byte-identity with the active host checkpoint) and contains {final_theorem}, or after writing one of the structured counterexample/manual-review decisions documented below. A bare early exit is not terminal and will be resumed. An unchanged active checkpoint is deliberately not recompiled.\n",
            round_budget.as_secs()
        ));
        prompt.push_str("This is one continuous proof search; later invocations resume after handoff, process failure, or a failed host check, not at a planned phase boundary.\n");
        prompt.push_str("Within one fixed proof-workspace generation, Problem.v, immutable checked ProofModules, and scratch state persist across continuations. Scratch is untrusted WIP; scratch/checked holds host-checked reusable fragments. A fixed-witness handoff starts a new generation. PostgreSQL does not certify divergence. Only a passing Problem.v advances the restart checkpoint.\n");
        prompt.push_str(&format!(
            "Proof-session generation: {session_generation}. Sessions are restarted after {PROOF_AGENT_SESSION_RESTART_AFTER_FAILED_ROUNDS} unsuccessful turns to bound transcript growth.\n"
        ));
        if session_restarted {
            prompt.push_str(
                "This is a fresh Codex session. The current host-selected Problem.v, any checked ProofModules and scratch belonging to this workspace generation, and the host feedback below are the complete available state; do not assume material from an earlier witness generation survived.\n",
            );
        }
        if let Some(feedback) = feedback {
            prompt.push_str("\nPrevious host-side certification feedback begins here:\n");
            prompt.push_str(feedback);
            prompt.push_str("\nPrevious host-side certification feedback ends here.\n");
        }
    }
    prompt.push('\n');
    if include_static_instructions {
        prompt.push_str(&proof_agent_instruction_body());
    } else {
        prompt.push_str(
            "Continue under the complete proof contract from this proof-session generation. Reuse the retained SQL/shape survey, proof plan, source locations, and compiled subgoals; focus on the bounded feedback and next unresolved subgoal above.\n",
        );
    }
    prompt
}

fn write_proof_agent_round_prompt(
    artifacts: &ArtifactWriter,
    lemma_availability: crate::engine::config::LemmaAvailability,
    verification_mode: VerificationMode,
    round: usize,
    remaining: Duration,
    round_budget: Duration,
    feedback: Option<&str>,
    session_generation: usize,
    session_restarted: bool,
) -> Result<()> {
    let prompt = render_proof_agent_prompt(
        verification_mode,
        Some((
            round,
            remaining,
            round_budget,
            session_generation,
            session_restarted,
        )),
        feedback,
    );
    artifacts.write_text(
        "proof-stage/formal-sql/proof-agent-prompt.md",
        &ablation::select_prompt(prompt, lemma_availability),
    )
}

/// Materialize one generation's sources and validate its context exactly once.
/// Both initial setup and fixed-witness restart use this entry point; agent
/// execution still independently validates the context before and after a round.
fn write_proof_workspace(
    artifacts: &ArtifactWriter,
    input: &VerificationInput,
    ir_input: &VerificationIr,
    lowering: &ProofLoweringReport,
    observation_certificates: &ObservationCertificateReport,
    schema_module: &str,
    queries_module: &str,
    witness_modules: &WitnessModules,
    problem_module: &str,
    goal_module: &str,
    options: &Config,
) -> Result<(ProofWorkspace, PreparedContext)> {
    artifacts.write_text("proof-stage/formal-sql/Schema.v", schema_module)?;
    artifacts.write_text("proof-stage/formal-sql/Queries.v", queries_module)?;
    artifacts.write_text("proof-stage/formal-sql/Problem.v", problem_module)?;
    write_formal_sql_witness_modules(artifacts, witness_modules)?;
    artifacts.write_text("proof-stage/formal-sql/Goal.v", goal_module)?;
    ablation::prepare(artifacts, options)?;
    let proof_modules_dir = artifacts
        .root()
        .join("proof-stage/formal-sql")
        .join(PROOF_MODULE_DIRECTORY);
    std::fs::create_dir_all(&proof_modules_dir).map_err(|source| Error::CreateDir {
        path: proof_modules_dir.clone(),
        source,
    })?;
    std::fs::set_permissions(&proof_modules_dir, std::fs::Permissions::from_mode(0o700)).map_err(
        |source| {
            Error::ProofAgentCommand(format!(
                "failed to secure proof-agent module directory {}: {source}",
                proof_modules_dir.display()
            ))
        },
    )?;
    let scratch_dir = artifacts.root().join("proof-stage/formal-sql/scratch");
    std::fs::create_dir_all(&scratch_dir).map_err(|source| Error::CreateDir {
        path: scratch_dir.clone(),
        source,
    })?;
    std::fs::set_permissions(&scratch_dir, std::fs::Permissions::from_mode(0o700)).map_err(
        |source| {
            Error::ProofAgentCommand(format!(
                "failed to secure proof-agent scratch directory {}: {source}",
                scratch_dir.display()
            ))
        },
    )?;
    let query_shape = build_query_shape(input, ir_input, lowering, schema_module, queries_module)?;
    let observation_certificates = serde_json::to_string_pretty(observation_certificates)? + "\n";
    let context = write_proof_agent_context(
        artifacts,
        input,
        options.verification_mode,
        options.lemma_availability,
        &query_shape.text,
        &query_shape.ordered_signatures_text,
        &observation_certificates,
        schema_module,
        queries_module,
        &witness_modules.witness,
        problem_module,
        goal_module,
    )?;
    let proof_prompt = ablation::select_prompt(
        render_proof_agent_prompt(options.verification_mode, None, None),
        options.lemma_availability,
    );
    artifacts.write_text(
        "proof-stage/formal-sql/proof-agent-prompt.md",
        &proof_prompt,
    )?;
    artifacts.write_text(
        "proof-stage/formal-sql/run-rocq-check.sh",
        FORMAL_SQL_ROCQ_CHECK_REQUEST_SCRIPT,
    )?;
    write_trusted_proof_agent_launcher(artifacts)?;

    let workspace = ProofWorkspace {
        generated_module_dir: "proof-stage/formal-sql".to_owned(),
        problem_path: "proof-stage/formal-sql/Problem.v".to_owned(),
        proof_modules_dir: "proof-stage/formal-sql/ProofModules".to_owned(),
        scratch_dir: "proof-stage/formal-sql/scratch".to_owned(),
        goal_path: "proof-stage/formal-sql/Goal.v".to_owned(),
        witness_path: "proof-stage/formal-sql/Witness.v".to_owned(),
        source_sql_path: "proof-stage/formal-sql/source.sql".to_owned(),
        target_sql_path: "proof-stage/formal-sql/target.sql".to_owned(),
        query_shape_path: "proof-stage/formal-sql/query-shape.json".to_owned(),
        ordered_signatures_path: "proof-stage/formal-sql/ordered-signatures.json".to_owned(),
        observation_certificates_path: "proof-stage/formal-sql/observation-certificates.json"
            .to_owned(),
        semantic_primer_path: "proof-stage/formal-sql/semantic-primer.md".to_owned(),
        declaration_search_path: "proof-stage/formal-sql/search-rocq-declarations.py".to_owned(),
        context_manifest_path: "proof-stage/formal-sql/context-manifest.json".to_owned(),
        proof_agent_prompt_path: "proof-stage/formal-sql/proof-agent-prompt.md".to_owned(),
        rocq_check_script_path: "proof-stage/formal-sql/run-rocq-check.sh".to_owned(),
        docker_agent_script_path:
            "proof-stage/proof-agent/trusted-launcher/run-proof-agent-docker.sh".to_owned(),
    };
    Ok((workspace, context))
}

#[cfg(test)]
#[path = "../../tests/proof_stage/mod.rs"]
mod tests;
