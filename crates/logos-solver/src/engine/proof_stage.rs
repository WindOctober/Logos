use std::collections::{BTreeMap, BTreeSet};
use std::ffi::{CString, OsStr};
use std::fs::{File, OpenOptions};
use std::io::{Read, Write};
use std::os::fd::{AsRawFd, FromRawFd};
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::{DirBuilderExt, OpenOptionsExt, PermissionsExt};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Arc, LazyLock, Mutex};
use std::thread::{self, JoinHandle};
use std::time::{Duration, Instant};

use logos_ir::ShellSqlIrFrontend;
use logos_ir::ir::{RelExpr, SqlStringType};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::artifacts::ArtifactWriter;
use crate::core::{
    FormalAttribute, FormalAttributeType, FormalProofModule, FormalQueryDefinitionGraph,
    FormalQueryExpr, FormalQueryStatementSymbols, FormalScalarExpr, FormalScalarSelectItem,
    FormalSchema, LoweredProgram, LoweredQuery, LoweringConfig, ObservationCertificateReport,
    ProofInputBindings, ProofLoweringReport, VerificationInput, VerificationIr, VerificationMode,
    analyze_observation_certificates, lower_verification_input_with_mode,
    query_expr_output_signature,
};
use crate::engine::config::Config;
use crate::engine::now_ms_since_epoch;
use crate::engine::report::{
    AcceptedDiagnosticSourceAudit, AgentAudit, AgentRunLog, AuditFinding, Backend, BackendStatus,
    CertificationLevel, DiagnosticArtifactBinding, DiagnosticCheckerInvocation,
    LaunchEnvironmentPolicy, PreconditionSource, ProblemCompileCheckpointEvidence,
    ProofAgentConfiguration, ProofAgentContext, ProofCheckpointTransition,
    ProofCounterexampleHandoff, ProofReport, ProofSessionRestartReason, ProofWorkspace,
    ProofWorkspaceTransition, ProofWorkspaceTransitionReason, RejectedDiagnosticSourceAudit,
    TrustedCheckInvocation, TrustedDiagnosticCacheEvidence, VerificationClaimKind,
};
use crate::error::{Error, Result};
use crate::usage::{CodexInvocationUsage, LlmUsage, parse_codex_jsonl, parse_codex_thread_id};
use crate::validation::{FormalWitnessSnapshot, FormalWitnessValue};

pub const DEFAULT_PROOF_AGENT_COMMAND: &str = "codex exec --disable plugins --disable remote_plugin --disable plugin_hooks --disable skill_mcp_dependency_install --disable goals --json --model gpt-5.6-sol -c model_reasoning_effort=medium --dangerously-bypass-approvals-and-sandbox --skip-git-repo-check --cd /workspace/problem - < proof-agent-prompt.md";
pub const DEFAULT_PROOF_AGENT_RESUME_COMMAND: &str = "codex exec resume --disable plugins --disable remote_plugin --disable plugin_hooks --disable skill_mcp_dependency_install --disable goals --json --model gpt-5.6-sol -c model_reasoning_effort=medium --dangerously-bypass-approvals-and-sandbox --skip-git-repo-check {session_id} - < proof-agent-prompt.md";

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
];
const COUNTEREXAMPLE_HANDOFF_FILE: &str = "counterexample-handoff.json";
const AUTHORITY_CLOSURE_FILE: &str = "authority-closure.txt";
const COMPACT_DEFINITION_GRAPH_NOTATION: &str = "skeletonNodes[i]=[head,[ordered child node IDs]]; definitions retain every exact Rocq symbol, kind, and root node; @symbol heads bind exact Queries.v definitions. IDs are deterministic postorder. Reused nodes mean identical displayed skeleton only, never Rocq-term or SQL equality; opaque scalar/list payloads remain authoritative in Queries.v";
const COMPACT_FRONTEND_SKELETON_NOTATION: &str = "nodes[i]=[operator{compact fields},[ordered child node IDs]]; each typedFrontendTree.rootNode selects a source/target root. IDs are deterministic postorder. Reused nodes mean identical displayed skeleton only, never SQL equality; exact SQL and the typed IR remain authoritative";
type TrustedProofSources = BTreeMap<&'static str, String>;

pub(super) enum ProofHandoffResolution {
    Continue(String),
    NeedsManualReview(String),
    RestartWithFormalWitness {
        feedback: String,
        snapshot: FormalWitnessSnapshot,
    },
}

pub(super) enum ProofStageResult {
    Finished(Box<ProofReport>),
}

/// Authoritative IR and lowering shared by witness synthesis and the Rocq proof
/// stage. Constructing it once prevents the two agents from silently reasoning
/// about different frontend snapshots.
pub(super) struct PreparedFormalInput {
    pub(super) ir_input: VerificationIr,
    pub(super) lowering_report: ProofLoweringReport,
    pub(super) observation_certificates: ObservationCertificateReport,
}

type ProofHandoffHandler<'a> =
    dyn FnMut(&ProofCounterexampleHandoff) -> Result<ProofHandoffResolution> + 'a;

struct AgentRoundResult {
    log: AgentRunLog,
    repair_feedback: String,
    cumulative_usage: Option<CodexInvocationUsage>,
    session_resumable: bool,
    problem_compile_checkpoint: Option<ProblemCompileCheckpoint>,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct AgentRunArtifact<'a> {
    #[serde(flatten)]
    log: &'a AgentRunLog,
    #[serde(skip_serializing_if = "Option::is_none")]
    cumulative_usage: Option<&'a LlmUsage>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
struct ContextFileBinding {
    path: String,
    bytes: usize,
    sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
struct ProofAgentContextManifest {
    schema_version: u32,
    authority: &'static str,
    verification_mode: VerificationMode,
    static_prompt_and_primer_bytes: usize,
    source_sql: ContextFileBinding,
    target_sql: ContextFileBinding,
    query_shape: ContextFileBinding,
    ordered_signatures: ContextFileBinding,
    observation_certificates: ContextFileBinding,
    semantic_primer: ContextFileBinding,
    declaration_search: ContextFileBinding,
    schema_module: ContextFileBinding,
    queries_module: ContextFileBinding,
    witness_module: ContextFileBinding,
    goal_module: ContextFileBinding,
}

struct PreparedProofAgentContext {
    manifest: ProofAgentContextManifest,
    manifest_text: String,
    report: ProofAgentContext,
}

struct BuiltQueryShape {
    text: String,
    ordered_signatures_text: String,
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct QueryShapeArtifact {
    schema_version: u32,
    authority: &'static str,
    frontend_sql_role: &'static str,
    operator_tree_notation: &'static str,
    source_sql_sha256: String,
    target_sql_sha256: String,
    schema_module_sha256: String,
    queries_module_sha256: String,
    emitted_rocq_symbols: Vec<String>,
    emitted_definition_graph: CompactDefinitionGraph,
    typed_frontend_skeleton: CompactSkeletonDag,
    source_program: Vec<CompactQueryStatementShape>,
    target_program: Vec<CompactQueryStatementShape>,
}

#[derive(Clone, Debug)]
struct QueryStatementShape {
    statement_index: usize,
    exact_sql_sha256: String,
    frontend_sql_sha256: String,
    exact_frontend_bytes_equal: bool,
    emitted_rocq_root_symbol: String,
    emitted_rocq_output_signature_symbol: String,
    final_output_canonicalization: bool,
    output_signature: Vec<CompactAttribute>,
    typed_frontend_tree: CompactOperatorTree,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
struct CompactAttribute {
    name: String,
    r#type: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    nullable: Option<bool>,
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct OrderedSignaturesArtifact {
    schema_version: u32,
    authority: &'static str,
    derivation: &'static str,
    occurrence_order: &'static str,
    signature_identity: &'static str,
    comparison_policy: &'static str,
    frontier_policy: &'static str,
    signatures: Vec<OrderedSignaturePoolEntry>,
    source_program: Vec<OrderedSignatureStatement>,
    target_program: Vec<OrderedSignatureStatement>,
    nodes: Vec<OrderedSignatureNode>,
    comparisons: Vec<OrderedSignatureComparison>,
    normalization_frontier_hints: Vec<OrderedSignatureFrontierHint>,
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct OrderedSignaturePoolEntry {
    signature_id: String,
    arity: usize,
    attributes: Vec<CompactAttribute>,
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct OrderedSignatureStatement {
    statement_index: usize,
    emitted_rocq_root_symbol: String,
    root_node_id: String,
    node_count: usize,
}

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct OrderedSignatureNode {
    node_id: String,
    side: &'static str,
    statement_index: usize,
    preorder_index: usize,
    role_path: String,
    operator_kind: &'static str,
    signature_id: String,
    arity: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    parent_node_id: Option<String>,
    children: Vec<OrderedSignatureChild>,
}

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct OrderedSignatureChild {
    role: String,
    edge_kind: &'static str,
    node_id: String,
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct OrderedSignatureComparison {
    statement_index: usize,
    role_path: String,
    source_node_id: String,
    target_node_id: String,
    source_operator_kind: &'static str,
    target_operator_kind: &'static str,
    operator_kind_equal: bool,
    source_signature_id: String,
    target_signature_id: String,
    signature_equal: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    mismatch: Option<OrderedSignatureMismatch>,
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct OrderedSignatureMismatch {
    kind: &'static str,
    source_arity: usize,
    target_arity: usize,
    first_differing_index: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    source_attribute: Option<CompactAttribute>,
    #[serde(skip_serializing_if = "Option::is_none")]
    target_attribute: Option<CompactAttribute>,
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct OrderedSignatureFrontierHint {
    statement_index: usize,
    role_path: String,
    source_node_id: String,
    target_node_id: String,
    operator_kind: &'static str,
    signature_id: String,
    incompatible_relational_child_roles: Vec<String>,
    reason: &'static str,
}

#[derive(Clone, Debug)]
struct OrderedSignatureNodeRecord {
    artifact: OrderedSignatureNode,
    exact_signature: Vec<FormalAttribute>,
}

#[derive(Clone, Debug)]
struct CompactOperatorTree {
    node_count: usize,
    max_depth: usize,
    expression: String,
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct CompactQueryStatementShape {
    statement_index: usize,
    exact_sql_sha256: String,
    frontend_sql_sha256: String,
    exact_frontend_bytes_equal: bool,
    emitted_rocq_root_symbol: String,
    emitted_rocq_output_signature_symbol: String,
    final_output_canonicalization: bool,
    output_signature: Vec<CompactAttribute>,
    typed_frontend_tree: CompactOperatorTreeRoot,
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct CompactOperatorTreeRoot {
    node_count: usize,
    max_depth: usize,
    root_node: usize,
}

/// A lossless, topologically ordered structural DAG. Each node serializes as
/// `[head, [ordered child node IDs]]` to keep the navigation artifact small
/// without abbreviating any constructor, field, or emitted-symbol reference.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct CompactSkeletonNode(String, Vec<usize>);

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
struct CompactSkeletonDag {
    schema_version: u32,
    notation: &'static str,
    expanded_trees_sha256: String,
    nodes: Vec<CompactSkeletonNode>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
struct CompactShapeDefinition {
    symbol: String,
    kind: String,
    root_node: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
struct CompactDefinitionGraph {
    schema_version: u32,
    notation: &'static str,
    expanded_graph_sha256: String,
    expanded_trees_sha256: String,
    opaque_helper_symbols: Vec<String>,
    skeleton_nodes: Vec<CompactSkeletonNode>,
    definitions: Vec<CompactShapeDefinition>,
    source_statements: Vec<FormalQueryStatementSymbols>,
    target_statements: Vec<FormalQueryStatementSymbols>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct SkeletonTree {
    head: String,
    children: Vec<SkeletonTree>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct CompactedSkeletonForest {
    expanded_trees_sha256: String,
    nodes: Vec<CompactSkeletonNode>,
    roots: Vec<usize>,
}

struct TreeExpression {
    node_count: usize,
    max_depth: usize,
    expression: String,
}

#[derive(Clone)]
enum TrustedRocqCheckMode {
    Full,
    Preflight,
    WitnessPreflight,
    ProblemDiagnostic {
        timeout_seconds: u64,
    },
    ModuleDiagnostic {
        timeout_seconds: u64,
        candidate_path: String,
    },
}

#[derive(Clone, Copy, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
enum DiagnosticCandidateMode {
    Problem,
    Module,
    Scratch,
}

impl DiagnosticCandidateMode {
    fn as_str(self) -> &'static str {
        match self {
            Self::Problem => "problem",
            Self::Module => "module",
            Self::Scratch => "scratch",
        }
    }
}

#[derive(Clone, Copy, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
enum DiagnosticPurpose {
    StaticObligation,
    SemanticEquivalence,
    Assembly,
}

impl DiagnosticPurpose {
    fn as_str(self) -> &'static str {
        match self {
            Self::StaticObligation => "static-obligation",
            Self::SemanticEquivalence => "semantic-equivalence",
            Self::Assembly => "assembly",
        }
    }
}

#[derive(Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct DiagnosticBrokerRequest {
    schema_version: u32,
    nonce: String,
    mode: DiagnosticCandidateMode,
    candidate_path: String,
    purpose: DiagnosticPurpose,
    candidate_sha256: String,
    candidate_bytes: u64,
    requested_timeout_seconds: u64,
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct DiagnosticBrokerResponse {
    schema_version: u32,
    sequence: Option<usize>,
    mode: Option<DiagnosticCandidateMode>,
    candidate_path: Option<String>,
    purpose: Option<DiagnosticPurpose>,
    candidate_sha256: Option<String>,
    compile_passed: bool,
    problem_compile_passed: bool,
    compile_checkpoint_advanced: bool,
    exit_code: Option<i32>,
    timed_out: bool,
    elapsed_ms: u128,
    stdout: String,
    stderr: String,
    error: Option<String>,
}

#[derive(Clone, Debug)]
struct ProblemCompileCheckpoint {
    // The path only needs to retain Problem.v: every imported agent module is
    // host-checked and immutable by logical name for the lifetime of this
    // generated workspace. A fixed-witness restart discards the live workspace
    // and module cache; the generation-tagged checkpoint remains immutable
    // evidence but can never be reused by a later workspace generation.
    path: PathBuf,
    sha256: String,
    workspace_generation: usize,
    round: usize,
    sequence: usize,
}

impl ProblemCompileCheckpoint {
    fn report_evidence(
        &self,
        artifacts: &ArtifactWriter,
    ) -> Result<ProblemCompileCheckpointEvidence> {
        let path = self.path.strip_prefix(artifacts.root()).map_err(|_| {
            Error::ProofAgentCommand(format!(
                "problem compile checkpoint {} escapes the case artifact root",
                self.path.display()
            ))
        })?;
        let path = path.to_str().ok_or_else(|| {
            Error::ProofAgentCommand("problem compile checkpoint path is not UTF-8".to_owned())
        })?;
        Ok(ProblemCompileCheckpointEvidence {
            workspace_generation: self.workspace_generation,
            path: path.to_owned(),
            sha256: self.sha256.clone(),
            round: self.round,
            sequence: self.sequence,
        })
    }
}

struct PendingDiagnosticUpload {
    path: PathBuf,
}

impl PendingDiagnosticUpload {
    fn new(path: PathBuf) -> Self {
        Self { path }
    }

    fn path(&self) -> &Path {
        &self.path
    }
}

impl Drop for PendingDiagnosticUpload {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.path);
        if let Some(parent) = self.path.parent() {
            let _ = std::fs::remove_dir(parent);
        }
    }
}

struct ReadOnlyMappedFile {
    pointer: *mut libc::c_void,
    length: usize,
}

impl ReadOnlyMappedFile {
    fn open_utf8(path: &Path) -> Result<Self> {
        let file = File::open(path).map_err(|source| Error::Read {
            path: path.to_owned(),
            source,
        })?;
        let length = usize::try_from(
            file.metadata()
                .map_err(|source| Error::Read {
                    path: path.to_owned(),
                    source,
                })?
                .len(),
        )
        .map_err(|_| {
            Error::ProofAgentCommand(format!(
                "file is too large to address on this host: {}",
                path.display()
            ))
        })?;
        if length == 0 {
            return Ok(Self {
                pointer: std::ptr::null_mut(),
                length,
            });
        }
        // SAFETY: `file` is open for the mmap call, the returned mapping is
        // read-only/private, and `Drop` unmaps exactly `length` bytes.  The
        // mapped artifact is host-owned and not writable by the container.
        let pointer = unsafe {
            libc::mmap(
                std::ptr::null_mut(),
                length,
                libc::PROT_READ,
                libc::MAP_PRIVATE,
                file.as_raw_fd(),
                0,
            )
        };
        if pointer == libc::MAP_FAILED {
            return Err(Error::Read {
                path: path.to_owned(),
                source: std::io::Error::last_os_error(),
            });
        }
        let mapped = Self { pointer, length };
        std::str::from_utf8(mapped.as_bytes()).map_err(|source| {
            Error::ProofAgentCommand(format!(
                "mapped file {} is not UTF-8: {source}",
                path.display()
            ))
        })?;
        Ok(mapped)
    }

    fn as_bytes(&self) -> &[u8] {
        if self.length == 0 {
            return &[];
        }
        // SAFETY: the mapping remains live for `self` and contains `length`
        // readable bytes by construction.
        unsafe { std::slice::from_raw_parts(self.pointer.cast::<u8>(), self.length) }
    }

    fn as_str(&self) -> &str {
        // UTF-8 validity is established once by `open_utf8`.
        unsafe { std::str::from_utf8_unchecked(self.as_bytes()) }
    }
}

impl Drop for ReadOnlyMappedFile {
    fn drop(&mut self) {
        if self.length != 0 {
            // SAFETY: this is the exact live mapping created by `open_utf8`.
            let _ = unsafe { libc::munmap(self.pointer, self.length) };
        }
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct ScratchWorkspaceState {
    file_count: usize,
    total_bytes: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ScratchFileSnapshot {
    relative_path: PathBuf,
    bytes: Vec<u8>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct ValidatedScratchTree {
    files: Vec<ScratchFileSnapshot>,
    /// Relative directory paths, with the empty path representing the root.
    directories: BTreeSet<PathBuf>,
    /// Structurally safe regular files that are not eligible for persistence.
    dropped_unsupported_files: Vec<PathBuf>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum UnsupportedScratchFilePolicy {
    Reject,
    Drop,
}

#[derive(Default)]
struct DiagnosticBrokerState {
    requests_seen: usize,
    timeout_seconds_reserved: u64,
    workspace_generation: usize,
    active_problem_compile_checkpoint_sha256: Option<String>,
    invocations: Vec<DiagnosticCheckerInvocation>,
    accepted_source_audits: Vec<AcceptedDiagnosticSourceAudit>,
    rejected_source_audits: Vec<RejectedDiagnosticSourceAudit>,
    latest_checkpoint: Option<ProblemCompileCheckpoint>,
    latest_feedback: Option<String>,
    trusted_environment_error: Option<String>,
}

#[derive(Debug)]
struct DiagnosticBrokerOutcome {
    requests_seen: usize,
    requested_timeout_seconds_reserved: u64,
    accepted_count: usize,
    rejected_source_audit_count: usize,
    other_rejected_request_count: usize,
    invocations: Vec<DiagnosticCheckerInvocation>,
    accepted_source_audits: Vec<AcceptedDiagnosticSourceAudit>,
    rejected_source_audits: Vec<RejectedDiagnosticSourceAudit>,
    latest_checkpoint: Option<ProblemCompileCheckpoint>,
    latest_feedback: Option<String>,
    trusted_environment_error: Option<String>,
}

struct DiagnosticBroker {
    socket_path: PathBuf,
    // Unix-domain socket paths have a small platform limit. Keep only this
    // zero-byte rendezvous point in a short, private /tmp directory; all proof
    // state and generated artifacts remain in the case-local host-tmp tree.
    _socket_directory: ProofDiagnosticSocketDirectory,
    nonce: String,
    artifacts_root: PathBuf,
    round: usize,
    stop: Arc<AtomicBool>,
    state: Arc<Mutex<DiagnosticBrokerState>>,
    handle: Option<JoinHandle<()>>,
}

struct ProofDiagnosticSocketDirectory {
    path: PathBuf,
    sidecar_path: PathBuf,
}

fn parse_case_process_supervisor_pid(value: &OsStr) -> Result<u32> {
    let bytes = value.as_bytes();
    if bytes.is_empty() || bytes[0] == b'0' || bytes.iter().any(|byte| !byte.is_ascii_digit()) {
        return Err(Error::ProofAgentCommand(format!(
            "{CASE_PROCESS_SUPERVISOR_PID_ENVIRONMENT} must be a canonical positive decimal u32"
        )));
    }
    let text = std::str::from_utf8(bytes).map_err(|_| {
        Error::ProofAgentCommand(format!(
            "{CASE_PROCESS_SUPERVISOR_PID_ENVIRONMENT} must be a canonical positive decimal u32"
        ))
    })?;
    let process_id = text.parse::<u32>().map_err(|_| {
        Error::ProofAgentCommand(format!(
            "{CASE_PROCESS_SUPERVISOR_PID_ENVIRONMENT} must be a canonical positive decimal u32"
        ))
    })?;
    if process_id.to_string() != text {
        return Err(Error::ProofAgentCommand(format!(
            "{CASE_PROCESS_SUPERVISOR_PID_ENVIRONMENT} must be a canonical positive decimal u32"
        )));
    }
    Ok(process_id)
}

fn case_process_supervisor_pid() -> Result<u32> {
    if let Some(value) = std::env::var_os(CASE_PROCESS_SUPERVISOR_PID_ENVIRONMENT) {
        return parse_case_process_supervisor_pid(&value);
    }
    // Unit tests exercise the broker in-process, outside the benchmark runner.
    // Production builds fail closed when the runner-authenticated channel is
    // absent; tests separately cover the strict parser above.
    #[cfg(test)]
    {
        Ok(std::process::id())
    }
    #[cfg(not(test))]
    {
        Err(Error::ProofAgentCommand(format!(
            "missing required {CASE_PROCESS_SUPERVISOR_PID_ENVIRONMENT} environment binding"
        )))
    }
}

impl ProofDiagnosticSocketDirectory {
    fn create(artifacts_root: &Path, round: usize) -> Result<Self> {
        let process_id = case_process_supervisor_pid()?;
        let temp_root = Path::new(DIAGNOSTIC_SOCKET_TEMP_ROOT);
        let root_metadata = std::fs::symlink_metadata(temp_root).map_err(|source| {
            Error::ProofAgentCommand(format!(
                "failed to inspect diagnostic socket temp root {}: {source}",
                temp_root.display()
            ))
        })?;
        if root_metadata.file_type().is_symlink() || !root_metadata.is_dir() {
            return Err(Error::ProofAgentCommand(format!(
                "diagnostic socket temp root {} must be a real directory",
                temp_root.display()
            )));
        }
        let host_tmp = artifacts_root.join(PROOF_AGENT_HOST_TMP_DIRECTORY);
        std::fs::create_dir_all(&host_tmp).map_err(|source| {
            Error::ProofAgentCommand(format!(
                "failed to create proof-agent host temp root {} for diagnostic sidecar: {source}",
                host_tmp.display()
            ))
        })?;
        let host_tmp_metadata = std::fs::symlink_metadata(&host_tmp).map_err(|source| {
            Error::ProofAgentCommand(format!(
                "failed to inspect proof-agent host temp root {} for diagnostic sidecar: {source}",
                host_tmp.display()
            ))
        })?;
        if host_tmp_metadata.file_type().is_symlink() || !host_tmp_metadata.is_dir() {
            return Err(Error::ProofAgentCommand(format!(
                "diagnostic socket sidecar root {} must be a real directory",
                host_tmp.display()
            )));
        }
        std::fs::set_permissions(&host_tmp, std::fs::Permissions::from_mode(0o700)).map_err(
            |source| {
                Error::ProofAgentCommand(format!(
                    "failed to secure diagnostic socket sidecar root {}: {source}",
                    host_tmp.display()
                ))
            },
        )?;

        // Publish the exact external path before creating anything under /tmp.
        // A case-level SIGKILL can therefore leave either no external resource,
        // a harmless sidecar whose directory is absent, or a fully discoverable
        // directory.  In particular, there is no tempdir-before-sidecar window.
        let token_seed = format!(
            "{}:{}:{}:{}:{}",
            artifacts_root.display(),
            process_id,
            round,
            now_ms_since_epoch(),
            PROOF_AGENT_SESSION_HOME_COUNTER.fetch_add(1, Ordering::Relaxed),
        );
        let token = &sha256_hex(token_seed.as_bytes())[..32];
        let socket_directory_name = format!("logos-pds-{process_id}-{token}");
        let socket_directory = temp_root.join(&socket_directory_name);
        match std::fs::symlink_metadata(&socket_directory) {
            Ok(_) => {
                return Err(Error::ProofAgentCommand(format!(
                    "refusing pre-existing diagnostic socket directory {}",
                    socket_directory.display()
                )));
            }
            Err(source) if source.kind() == std::io::ErrorKind::NotFound => {}
            Err(source) => {
                return Err(Error::ProofAgentCommand(format!(
                    "failed to inspect diagnostic socket directory {}: {source}",
                    socket_directory.display()
                )));
            }
        }
        let sidecar_path = host_tmp.join(format!(
            ".diagnostic-socket-{process_id}-{round:02}-{socket_directory_name}.json"
        ));
        let pending_sidecar = host_tmp.join(format!(
            ".pending-diagnostic-socket-{process_id}-{round:02}-{socket_directory_name}.{}.tmp",
            now_ms_since_epoch()
        ));
        if std::fs::symlink_metadata(&sidecar_path).is_ok() {
            return Err(Error::ProofAgentCommand(format!(
                "refusing pre-existing diagnostic socket sidecar {}",
                sidecar_path.display()
            )));
        }
        let sidecar = serde_json::json!({
            "schemaVersion": 1,
            "solverPid": process_id,
            "directory": socket_directory,
        });
        let mut pending = OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(&pending_sidecar)
            .map_err(|source| {
                Error::ProofAgentCommand(format!(
                    "failed to create diagnostic socket sidecar {}: {source}",
                    pending_sidecar.display()
                ))
            })?;
        let sidecar_bytes = serde_json::to_vec(&sidecar)
            .map_err(|source| Error::ProofAgentCommand(source.to_string()))?;
        if let Err(source) = pending
            .write_all(&sidecar_bytes)
            .and_then(|()| pending.write_all(b"\n"))
            .and_then(|()| pending.sync_all())
        {
            let _ = std::fs::remove_file(&pending_sidecar);
            return Err(Error::ProofAgentCommand(format!(
                "failed to write diagnostic socket sidecar {}: {source}",
                pending_sidecar.display()
            )));
        }
        drop(pending);
        if let Err(source) = std::fs::hard_link(&pending_sidecar, &sidecar_path) {
            let _ = std::fs::remove_file(&pending_sidecar);
            return Err(Error::ProofAgentCommand(format!(
                "failed to publish diagnostic socket sidecar {}: {source}",
                sidecar_path.display()
            )));
        }
        if let Err(source) = std::fs::remove_file(&pending_sidecar) {
            let _ = std::fs::remove_file(&sidecar_path);
            return Err(Error::ProofAgentCommand(format!(
                "failed to finalize diagnostic socket sidecar {}: {source}",
                sidecar_path.display()
            )));
        }
        let host_tmp_directory = File::open(&host_tmp).map_err(|source| {
            Error::ProofAgentCommand(format!(
                "failed to open diagnostic socket sidecar root {}: {source}",
                host_tmp.display()
            ))
        })?;
        host_tmp_directory.sync_all().map_err(|source| {
            Error::ProofAgentCommand(format!(
                "failed to sync diagnostic socket sidecar root {}: {source}",
                host_tmp.display()
            ))
        })?;

        let mut directory_builder = std::fs::DirBuilder::new();
        directory_builder.mode(0o700);
        if let Err(source) = directory_builder.create(&socket_directory) {
            let _ = std::fs::remove_file(&sidecar_path);
            return Err(Error::ProofAgentCommand(format!(
                "failed to create recorded diagnostic socket directory {}: {source}",
                socket_directory.display()
            )));
        }
        let metadata = match std::fs::symlink_metadata(&socket_directory) {
            Ok(metadata) => metadata,
            Err(source) => {
                let _ = std::fs::remove_dir(&socket_directory);
                let _ = std::fs::remove_file(&sidecar_path);
                return Err(Error::ProofAgentCommand(format!(
                    "failed to inspect short diagnostic socket directory {}: {source}",
                    socket_directory.display()
                )));
            }
        };
        if metadata.file_type().is_symlink()
            || !metadata.is_dir()
            || metadata.permissions().mode() & 0o777 != 0o700
        {
            let _ = std::fs::remove_dir(&socket_directory);
            let _ = std::fs::remove_file(&sidecar_path);
            return Err(Error::ProofAgentCommand(format!(
                "short diagnostic socket directory {} is not an atomically-created mode-0700 directory",
                socket_directory.display()
            )));
        }
        Ok(Self {
            path: socket_directory,
            sidecar_path,
        })
    }

    fn socket_path(&self) -> PathBuf {
        self.path.join(DIAGNOSTIC_SOCKET_FILE)
    }
}

impl Drop for ProofDiagnosticSocketDirectory {
    fn drop(&mut self) {
        let socket_path = self.socket_path();
        match std::fs::remove_file(&socket_path) {
            Ok(()) => {}
            Err(source) if source.kind() == std::io::ErrorKind::NotFound => {}
            Err(_) => return,
        }
        match std::fs::remove_dir(&self.path) {
            Ok(()) => {}
            Err(source) if source.kind() == std::io::ErrorKind::NotFound => {}
            Err(_) => return,
        }
        // Keep the sidecar discoverable until the external directory is gone.
        let _ = std::fs::remove_file(&self.sidecar_path);
    }
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

fn unavailable_formal_sql_witness_module() -> String {
    "From SQLFS Require Import SqlSyntax GenericInstance SchemaConstraints.\n\
From LogosGenerated Require Import Schema.\n\
\n\
(** No PostgreSQL candidate was losslessly frozen for this proof run.  Keeping\n\
    a fixed, unavailable witness makes the countermodel branch fail closed; an\n\
    agent may still prove the independent equivalence branch. *)\n\
Definition generated_witness_available : bool := false.\n\
Definition generated_witness_db : db_state := Schema.generated_schema.\n\
\n\
Lemma generated_witness_schema_conforms :\n\
  generated_witness_available = true ->\n\
  Schema.generated_schema_conforms generated_witness_db.\n\
Proof. discriminate. Qed.\n"
        .to_owned()
}

fn rocq_byte_string(value: &str) -> String {
    value
        .as_bytes()
        .iter()
        .rev()
        .fold("EmptyString".to_owned(), |rest, byte| {
            format!("String (Ascii.ascii_of_nat {}) ({rest})", byte)
        })
}

fn rocq_identifier_string(value: &str) -> String {
    format!("\"{}\"", value.replace('"', "\"\""))
}

fn rocq_witness_string_typmod(typmod: SqlStringType) -> String {
    match typmod {
        SqlStringType::Text => "StringText".to_owned(),
        SqlStringType::Varchar { length: None } => "StringVarchar".to_owned(),
        SqlStringType::Varchar {
            length: Some(length),
        } => format!("StringVarcharN {length}"),
        SqlStringType::Char { length } => format!("StringChar {length}"),
        SqlStringType::Bpchar => "StringBpchar".to_owned(),
    }
}

fn rocq_witness_attribute(attribute: &FormalAttribute) -> String {
    let name = rocq_identifier_string(&attribute.name);
    match attribute.ty {
        FormalAttributeType::Z => format!("Attr_Z ({name})"),
        FormalAttributeType::Int32 => format!("Attr_int32 ({name})"),
        FormalAttributeType::Int64 => format!("Attr_int64 ({name})"),
        FormalAttributeType::String { typmod } => format!(
            "Attr_string ({name}) ({})",
            rocq_witness_string_typmod(typmod)
        ),
        FormalAttributeType::Bool => format!("Attr_bool ({name})"),
        FormalAttributeType::Float => format!("Attr_float ({name})"),
        FormalAttributeType::Double => format!("Attr_double ({name})"),
        FormalAttributeType::Numeric => format!("Attr_numeric ({name})"),
        FormalAttributeType::Decimal { precision, scale } => {
            format!("Attr_decimal ({name}) {precision} {scale}")
        }
        FormalAttributeType::Date => format!("Attr_date ({name})"),
        FormalAttributeType::Time => format!("Attr_time ({name})"),
        FormalAttributeType::Timestamp { precision } => {
            format!("Attr_timestamp ({name}) {}", precision.unwrap_or(6))
        }
        FormalAttributeType::Timestamptz { precision } => {
            format!("Attr_timestamptz ({name}) {}", precision.unwrap_or(6))
        }
    }
}

fn rocq_witness_null(ty: FormalAttributeType) -> String {
    match ty {
        FormalAttributeType::Z => "Value_Z None".to_owned(),
        FormalAttributeType::Int32 => "Value_int32 None".to_owned(),
        FormalAttributeType::Int64 => "Value_int64 None".to_owned(),
        FormalAttributeType::String { typmod } => format!(
            "Value_string (StringValue ({}) None)",
            rocq_witness_string_typmod(typmod)
        ),
        FormalAttributeType::Bool => "Value_bool None".to_owned(),
        FormalAttributeType::Float => "Value_float None".to_owned(),
        FormalAttributeType::Double => "Value_double None".to_owned(),
        FormalAttributeType::Numeric | FormalAttributeType::Decimal { .. } => {
            "Value_numeric None".to_owned()
        }
        FormalAttributeType::Date => "Value_date None".to_owned(),
        FormalAttributeType::Time => "Value_time None".to_owned(),
        FormalAttributeType::Timestamp { .. } => "Value_timestamp None".to_owned(),
        FormalAttributeType::Timestamptz { .. } => "Value_timestamptz None".to_owned(),
    }
}

fn rocq_witness_value(value: &FormalWitnessValue, ty: FormalAttributeType) -> Result<String> {
    match (value, ty) {
        (FormalWitnessValue::Null, ty) => Ok(rocq_witness_null(ty)),
        (FormalWitnessValue::Bool(value), FormalAttributeType::Bool) => {
            Ok(format!("Value_bool (Some {value})"))
        }
        (FormalWitnessValue::Int32(value), FormalAttributeType::Int32) => {
            // Do not emit [int32_checked] here.  Its executable branch is
            // driven by an opaque range proof, so closed reflection gets
            // stuck while merely deciding whether the payload is [Some].
            // Rust's [i32] already establishes the range; Rocq independently
            // checks the explicit constructor proof below.
            Ok(format!(
                "Value_int32 (Some (Int32 ({value})%Z ltac:(unfold int32_min, int32_max; lia)))"
            ))
        }
        (FormalWitnessValue::Int64(value), FormalAttributeType::Int64) => Ok(format!(
            "Value_int64 (Some (Int64 ({value})%Z ltac:(unfold int64_min, int64_max; lia)))"
        )),
        (FormalWitnessValue::String(value), FormalAttributeType::String { typmod }) => Ok(format!(
            "Value_string (StringValue ({}) (Some ({})))",
            rocq_witness_string_typmod(typmod),
            rocq_byte_string(value)
        )),
        (FormalWitnessValue::Float32Bits(bits), FormalAttributeType::Float) => {
            Ok(format!("Value_float (Some (Float32OfBits ({bits})%Z))"))
        }
        (FormalWitnessValue::Float64Bits(bits), FormalAttributeType::Double) => {
            Ok(format!("Value_double (Some (Float64OfBits ({bits})%Z))"))
        }
        (
            FormalWitnessValue::NumericFinite { coefficient, scale },
            FormalAttributeType::Numeric | FormalAttributeType::Decimal { .. },
        ) => Ok(format!(
            "Value_numeric (Some (numeric_of_scaled ({coefficient})%Z ({scale})%Z))"
        )),
        (
            FormalWitnessValue::NumericNegInfinity,
            FormalAttributeType::Numeric | FormalAttributeType::Decimal { .. },
        ) => Ok("Value_numeric (Some NumericNegInfinity)".to_owned()),
        (
            FormalWitnessValue::NumericPosInfinity,
            FormalAttributeType::Numeric | FormalAttributeType::Decimal { .. },
        ) => Ok("Value_numeric (Some NumericPosInfinity)".to_owned()),
        (
            FormalWitnessValue::NumericNaN,
            FormalAttributeType::Numeric | FormalAttributeType::Decimal { .. },
        ) => Ok("Value_numeric (Some NumericNaN)".to_owned()),
        (FormalWitnessValue::Date(value), FormalAttributeType::Date) => {
            Ok(format!("Value_date (Some ({value})%Z)"))
        }
        (FormalWitnessValue::Time(value), FormalAttributeType::Time) => {
            Ok(format!("Value_time (Some ({value})%Z)"))
        }
        (FormalWitnessValue::Timestamp(value), FormalAttributeType::Timestamp { .. }) => {
            Ok(format!("Value_timestamp (Some ({value})%Z)"))
        }
        (FormalWitnessValue::Timestamptz(value), FormalAttributeType::Timestamptz { .. }) => {
            Ok(format!("Value_timestamptz (Some ({value})%Z)"))
        }
        (value, ty) => Err(Error::ProofAgentCommand(format!(
            "typed witness cell {value:?} does not match FormalSQL column type {ty:?}"
        ))),
    }
}

fn rocq_list(items: &[String]) -> String {
    if items.is_empty() {
        "[]".to_owned()
    } else {
        format!("[{}]", items.join("; "))
    }
}

fn rocq_forall_certificate_chain(lemmas: &[String]) -> String {
    let mut proof = String::new();
    for lemma in lemmas {
        proof.push_str(&format!("  constructor; [exact {lemma}|].\n"));
    }
    proof.push_str("  constructor.");
    proof
}

struct FormalSqlWitnessModules {
    witness: String,
    data: Option<String>,
    constraint_modules: Vec<(String, String)>,
}

fn formal_sql_witness_modules(
    schema: &FormalSchema,
    snapshot: Option<&FormalWitnessSnapshot>,
) -> Result<FormalSqlWitnessModules> {
    let Some(snapshot) = snapshot else {
        return Ok(FormalSqlWitnessModules {
            witness: unavailable_formal_sql_witness_module(),
            data: Some(
                "From LogosGenerated Require Import Schema.\n\
                 Definition generated_witness_data_unavailable_marker : Prop := True.\n"
                    .to_owned(),
            ),
            constraint_modules: Vec::new(),
        });
    };
    if snapshot.schema_version != 1 || snapshot.tables.len() != schema.tables.len() {
        return Err(Error::ProofAgentCommand(format!(
            "typed witness snapshot schema mismatch: version {}, {} tables; expected version 1 and {} tables",
            snapshot.schema_version,
            snapshot.tables.len(),
            schema.tables.len()
        )));
    }

    let mut row_definitions = Vec::with_capacity(schema.tables.len());
    let mut table_values = Vec::with_capacity(schema.tables.len());
    let mut table_relations = Vec::with_capacity(schema.tables.len());
    let mut cardinality_lemmas = Vec::with_capacity(schema.tables.len());
    for (index, (table, snapshot_table)) in schema.tables.iter().zip(&snapshot.tables).enumerate() {
        let snapshot_attributes = snapshot_table
            .columns
            .iter()
            .map(|column| FormalAttribute {
                name: column.name.clone(),
                ty: column.ty,
            })
            .collect::<Vec<_>>();
        if snapshot_table.relation != table.relation || snapshot_attributes != table.attributes {
            return Err(Error::ProofAgentCommand(format!(
                "typed witness table {index} does not exactly match the lowered FormalSQL schema"
            )));
        }
        let attributes = table
            .attributes
            .iter()
            .map(rocq_witness_attribute)
            .collect::<Vec<_>>();
        let attribute_list = rocq_list(&attributes);
        let attribute_name = format!("generated_witness_table_{index}_attributes");
        let mut rows = Vec::with_capacity(snapshot_table.rows.len());
        for (row_index, row) in snapshot_table.rows.iter().enumerate() {
            if row.cells.len() != table.attributes.len() {
                return Err(Error::ProofAgentCommand(format!(
                    "typed witness row {row_index} of table {:?} has {} cells, expected {}",
                    table.relation,
                    row.cells.len(),
                    table.attributes.len()
                )));
            }
            let values = row
                .cells
                .iter()
                .zip(&table.attributes)
                .map(|(value, attribute)| rocq_witness_value(value, attribute.ty))
                .collect::<Result<Vec<_>>>()?;
            rows.push(format!(
                "mk_tuple_lists {attribute_name} ({})",
                rocq_list(&values)
            ));
        }
        if rows.is_empty() {
            continue;
        }
        let row_name = format!("generated_witness_table_{index}_rows");
        row_definitions.push(format!(
            "Definition {attribute_name} : list (attribute TNull) :=\n  {attribute_list}."
        ));
        row_definitions.push(format!(
            "Definition {row_name} : list (tuple TNull) :=\n  {}.",
            rocq_list(&rows)
        ));
        let relation = rocq_identifier_string(&table.relation);
        cardinality_lemmas.push(format!(
            "Lemma generated_witness_table_{index}_instance_cardinal :\n\
  Febag.cardinal (Fecol.CBag (CTuple TNull))\n\
    (@_instance TNull generated_witness_db (Rel ({relation}))) =\n\
  ({}%N).\n\
Proof.\n\
  rewrite generated_witness_instance_cardinal.\n\
  reflexivity.\n\
Qed.",
            snapshot_table.rows.len()
        ));
        table_values.push(format!("WitnessTable (Rel ({})) {row_name}", relation));
        table_relations.push(format!("Rel ({relation})"));
    }
    // [create_table] prepends each relation to [_relnames].  The witness
    // inventory follows that exact generated-schema order, while the snapshot
    // JSON remains in declaration order for a direct schema binding audit.
    table_values.reverse();
    table_relations.reverse();

    let mut table_constraint_certificates = Vec::new();
    let mut constraint_modules = Vec::new();
    let mut table_constraint_lemma_names = Vec::with_capacity(schema.tables.len());
    for (index, (table, snapshot_table)) in schema.tables.iter().zip(&snapshot.tables).enumerate() {
        if snapshot_table.rows.is_empty() {
            let relation = rocq_identifier_string(&table.relation);
            table_constraint_certificates.push(format!(
                "Lemma generated_witness_table_constraint_{index}_conforms :\n\
  table_constraint_conforms generated_witness_db\n\
    Schema.generated_table_constraint_{index}.\n\
Proof.\n\
  apply (table_constraint_conforms_empty\n\
    generated_witness_db Schema.generated_schema_constraints).\n\
  - exact Schema.generated_table_constraint_{index}_declarations_well_formed.\n\
  - change (instance_rows\n\
      (witness_database Schema.generated_schema WitnessData.generated_witness_tables)\n\
      (constraint_relation Schema.generated_table_constraint_{index}) = nil).\n\
    rewrite witness_database_instance_rows.\n\
    change (witness_instance_rows WitnessData.generated_witness_tables\n\
      (Rel ({relation})) = nil).\n\
    apply witness_instance_rows_absent.\n\
    rewrite WitnessData.generated_witness_table_relations.\n\
    vm_compute.\n\
    intuition discriminate.\n\
Qed."
            ));
            table_constraint_lemma_names.push(format!(
                "generated_witness_table_constraint_{index}_conforms"
            ));
        } else {
            let relation = rocq_identifier_string(&table.relation);
            let rows = format!(
                "witness_instance_rows WitnessData.generated_witness_tables (Rel ({relation}))"
            );
            let header = "From SQLFS Require Import SqlSyntax GenericInstance Values FTuples SchemaConstraints.\nFrom Logos Require Import FormalSQL.WitnessFacts.\nFrom LogosGenerated Require Import Schema.\nFrom LogosGenerated Require WitnessData.\nFrom Stdlib Require Import List String SetoidList.\nImport ListNotations.\nOpen Scope string_scope.\n\n";
            let mut component_imports = Vec::new();
            let mut add_component = |module: String,
                                     theorem: String,
                                     statement: String,
                                     proof: String| {
                constraint_modules.push((
                    module.clone(),
                    format!("{header}Lemma {theorem} :\n  {statement}.\nProof.\n{proof}\nQed.\n"),
                ));
                component_imports.push(module.clone());
                format!("{module}.{theorem}")
            };
            let not_null = add_component(
                format!("Table{index:04}NotNull"),
                format!("generated_witness_table_{index}_not_null"),
                format!(
                    "rows_attributes_not_null (constraint_not_null Schema.generated_table_constraint_{index}) ({rows})"
                ),
                "  apply rows_attributes_not_nullb_sound.\n  vm_compute.\n  reflexivity."
                    .to_owned(),
            );
            let primary = table.constraints.primary_key.as_ref().map(|_| add_component(
                format!("Table{index:04}Primary"),
                format!("generated_witness_table_{index}_primary"),
                format!("forall key, constraint_primary_key Schema.generated_table_constraint_{index} = Some key -> primary_key_conforms key ({rows})"),
                "  intros key Hkey.\n  vm_compute in Hkey.\n  inversion Hkey; subst; clear Hkey.\n  apply primary_key_conformsb_sound.\n  vm_compute.\n  reflexivity.".to_owned(),
            ));
            let mut make_group = |kind: &str,
                                  count: usize,
                                  list: &str,
                                  conclusion: &str,
                                  sound: &str| {
                (0..count).map(|position| {
                    let module = format!("Table{index:04}{kind}{position:04}");
                    let theorem = format!("generated_witness_table_{index}_{}_{}", kind.to_ascii_lowercase(), position);
                    add_component(
                        module,
                        theorem,
                        format!("forall item, nth_error ({list}) {position} = Some item -> {conclusion}"),
                        format!("  intros item Hitem.\n  vm_compute in Hitem.\n  inversion Hitem; subst; clear Hitem.\n  {sound}\n  vm_compute.\n  reflexivity."),
                    )
                }).collect::<Vec<_>>()
            };
            let unique = make_group(
                "Unique",
                table.constraints.unique.len(),
                &format!("constraint_unique_keys Schema.generated_table_constraint_{index}"),
                &format!("unique_key_conforms item ({rows})"),
                "apply unique_key_conformsb_sound.",
            );
            let foreign = make_group(
                "Foreign",
                table.constraints.foreign_keys.len(),
                &format!("constraint_foreign_keys Schema.generated_table_constraint_{index}"),
                &format!("foreign_key_conforms WitnessData.generated_witness_db ({rows}) item"),
                "apply (foreign_key_conformsb_sound Schema.generated_schema WitnessData.generated_witness_tables).",
            );
            let checks = make_group(
                "Check",
                table.constraints.checks.len(),
                &format!("constraint_checks Schema.generated_table_constraint_{index}"),
                &format!(
                    "check_constraint_conforms WitnessData.generated_witness_db ({rows}) item"
                ),
                "apply check_constraint_conformsb_sound.",
            );
            drop(make_group);
            drop(add_component);
            let index_list =
                format!("constraint_unique_indexes Schema.generated_table_constraint_{index}");
            let mut indexes = Vec::new();
            for position in 0..table.constraints.unique_indexes.len() {
                let premise = format!("nth_error ({index_list}) {position} = Some item");
                let mut parts = Vec::new();
                for (suffix, conclusion, finish) in [
                    (
                        "Nonempty",
                        "list_nonemptyb (unique_index_terms item) = true".to_owned(),
                        "  vm_compute.\n  reflexivity.".to_owned(),
                    ),
                    (
                        "Predicate",
                        format!(
                            "forallb (fun row => unique_index_predicate_succeedsb WitnessData.generated_witness_db row item) ({rows}) = true"
                        ),
                        "  vm_compute.\n  reflexivity.".to_owned(),
                    ),
                    (
                        "Terms",
                        format!(
                            "forallb (fun row => if unique_index_row_participates WitnessData.generated_witness_db item row then unique_index_row_terms_succeedb item row else true) ({rows}) = true"
                        ),
                        "  vm_compute.\n  reflexivity.".to_owned(),
                    ),
                    (
                        "Unique",
                        format!(
                            "no_relatedb sql_key_equal_trueb (map (unique_index_key (unique_index_terms item)) (filter (unique_index_row_participates WitnessData.generated_witness_db item) ({rows}))) = true"
                        ),
                        "  vm_compute.\n  reflexivity.".to_owned(),
                    ),
                ] {
                    let module = format!("Table{index:04}Index{position:04}{suffix}");
                    let theorem = format!(
                        "generated_witness_table_{index}_index_{position}_{}",
                        suffix.to_ascii_lowercase()
                    );
                    constraint_modules.push((module.clone(), format!(
                        "{header}Lemma {theorem} :\n  forall item, {premise} -> {conclusion}.\nProof.\n  intros item Hitem.\n  vm_compute in Hitem.\n  inversion Hitem; subst; clear Hitem.\n{finish}\nQed.\n"
                    )));
                    component_imports.push(module.clone());
                    parts.push(format!("{module}.{theorem}"));
                }
                let module = format!("Table{index:04}Index{position:04}");
                let theorem = format!("generated_witness_table_{index}_index_{position}");
                let imports = component_imports.join(" ");
                constraint_modules.push((module.clone(), format!(
                    "{header}From LogosGenerated.WitnessModules Require {imports}.\nLemma {theorem} :\n  forall item, {premise} -> unique_index_conforms WitnessData.generated_witness_db ({rows}) item.\nProof.\n  intros item Hitem.\n  apply unique_index_conforms_of_reflected_components.\n  - apply {}; exact Hitem.\n  - apply {}; exact Hitem.\n  - apply {}; exact Hitem.\n  - apply {}; exact Hitem.\nQed.\n",
                    parts[0], parts[1], parts[2], parts[3],
                )));
                component_imports.push(module.clone());
                indexes.push(format!("{module}.{theorem}"));
            }
            let forall_proof = |references: &[String]| {
                let mut result = String::new();
                for reference in references {
                    result.push_str(&format!(
                        "    constructor; [apply {reference}; reflexivity|].\n"
                    ));
                }
                result.push_str("    constructor.");
                result
            };
            let module = format!("TableConstraint{index:04}");
            let theorem = format!("generated_witness_table_constraint_{index}_conforms");
            let imports = component_imports.join(" ");
            constraint_modules.push((module.clone(), format!(
                "From SQLFS Require Import SqlSyntax GenericInstance SchemaConstraints.\nFrom Logos Require Import FormalSQL.WitnessFacts.\nFrom LogosGenerated Require Import Schema.\nFrom LogosGenerated Require WitnessData.\nFrom LogosGenerated.WitnessModules Require {imports}.\nFrom Stdlib Require Import List String.\nImport ListNotations.\nOpen Scope string_scope.\n\nLemma {theorem} :\n  table_constraint_conforms WitnessData.generated_witness_db Schema.generated_table_constraint_{index}.\nProof.\n  change (table_constraint_conforms (witness_database Schema.generated_schema WitnessData.generated_witness_tables) Schema.generated_table_constraint_{index}).\n  apply table_constraint_conforms_of_components with (rows := {rows}).\n  - apply witness_database_instance_rows.\n  - exact {not_null}.\n  - rewrite Schema.generated_table_constraint_{index}_primary_key.\n    {}\n  - rewrite Schema.generated_table_constraint_{index}_unique_keys.\n{}\n  - rewrite Schema.generated_table_constraint_{index}_foreign_keys.\n{}\n  - rewrite Schema.generated_table_constraint_{index}_checks.\n{}\n  - rewrite Schema.generated_table_constraint_{index}_unique_indexes.\n{}\nQed.\n",
                primary.as_ref().map_or("exact I.".to_owned(), |reference| format!("apply {reference}; reflexivity.")),
                forall_proof(&unique), forall_proof(&foreign), forall_proof(&checks), forall_proof(&indexes),
            )));
            table_constraint_lemma_names.push(format!("{module}.{theorem}"));
        }
    }
    let table_constraints_aggregate = format!(
        "Lemma generated_witness_table_constraints_conform :\n\
  Forall (table_constraint_conforms generated_witness_db)\n\
    Schema.generated_schema_constraints.\n\
Proof.\n\
  unfold Schema.generated_schema_constraints.\n{}\n\
Qed.",
        rocq_forall_certificate_chain(&table_constraint_lemma_names)
    );

    let data = format!(
        "From SQLFS Require Import SqlSyntax GenericInstance Values FTuples FiniteBag FiniteCollection SchemaConstraints.\n\
From Logos Require Import FormalSQL.TNullSyntax FormalSQL.WitnessFacts.\n\
From LogosGenerated Require Import Schema.\n\
From Stdlib Require Import List String Ascii ZArith NArith Lia.\n\
Import ListNotations Tuple.\n\
Open Scope string_scope.\n\
Open Scope Z_scope.\n\
\n\
{}\n\
\n\
Definition generated_witness_tables : list witness_table :=\n  {}.\n\
\n\
Definition generated_witness_relations : list relname :=\n  {}.\n\
\n\
Lemma generated_witness_table_relations :\n\
  map witness_table_relation generated_witness_tables =\n\
  generated_witness_relations.\n\
Proof. reflexivity. Qed.\n\
\n\
Definition generated_witness_available : bool := true.\n\
Definition generated_witness_db : db_state :=\n\
  witness_database Schema.generated_schema generated_witness_tables.\n\
\n\
Lemma generated_witness_instance_cardinal :\n\
  forall relation,\n\
    Febag.cardinal (Fecol.CBag (CTuple TNull))\n\
      (@_instance TNull generated_witness_db relation) =\n\
    N.of_nat (List.length (witness_rows_for generated_witness_tables relation)).\n\
Proof.\n\
  intro relation.\n\
  unfold generated_witness_db.\n\
  apply witness_database_instance_cardinal.\n\
Qed.\n\
\n\
{}\n\
\n\
Lemma generated_witness_values_reflection :\n\
  witness_values_conformb\n\
    Schema.generated_schema generated_witness_tables = true.\n\
Proof.\n\
  vm_compute.\n\
  reflexivity.\n\
Qed.\n\
\n\
",
        row_definitions.join("\n\n"),
        rocq_list(&table_values),
        rocq_list(&table_relations),
        cardinality_lemmas.join("\n\n"),
    );
    let constraint_imports = constraint_modules
        .iter()
        .map(|(module, _)| module.as_str())
        .collect::<Vec<_>>()
        .join(" ");
    let witness = format!(
        "From SQLFS Require Import SqlSyntax GenericInstance SchemaConstraints.\n\
From Logos Require Import FormalSQL.WitnessFacts.\n\
From LogosGenerated Require Import Schema.\n\
From LogosGenerated Require WitnessData.\n\
{}\n\
From Stdlib Require Import List String.\n\
Import ListNotations.\n\
Open Scope string_scope.\n\
\n\
Definition generated_witness_available : bool :=\n\
  WitnessData.generated_witness_available.\n\
Definition generated_witness_db : db_state :=\n\
  WitnessData.generated_witness_db.\n\
\n\
{}\n\
\n\
{}\n\
\n\
Lemma generated_witness_schema_conforms :\n\
  generated_witness_available = true ->\n\
  Schema.generated_schema_conforms generated_witness_db.\n\
Proof.\n\
  intros _.\n\
  unfold Schema.generated_schema_conforms, generated_witness_db.\n\
  apply witness_database_conforms_of_certificates.\n\
  - exact WitnessData.generated_witness_values_reflection.\n\
  - exact Schema.generated_schema_constraints_well_formed.\n\
  - exact generated_witness_table_constraints_conform.\n\
Qed.\n",
        if constraint_imports.is_empty() {
            String::new()
        } else {
            format!("From LogosGenerated.WitnessModules Require {constraint_imports}.")
        },
        table_constraint_certificates.join("\n\n"),
        table_constraints_aggregate,
    );
    Ok(FormalSqlWitnessModules {
        witness,
        data: Some(data),
        constraint_modules,
    })
}

fn write_formal_sql_witness_modules(
    artifacts: &ArtifactWriter,
    modules: &FormalSqlWitnessModules,
) -> Result<()> {
    artifacts.write_text("proof-stage/formal-sql/Witness.v", &modules.witness)?;
    if let Some(data) = modules.data.as_ref() {
        artifacts.write_text("proof-stage/formal-sql/WitnessData.v", data)?;
    }
    let mut order = String::new();
    for (module, source) in &modules.constraint_modules {
        let file = format!("{module}.v");
        artifacts.write_text(
            &format!("proof-stage/formal-sql/{WITNESS_MODULE_DIRECTORY}/{file}"),
            source,
        )?;
        order.push_str(&file);
        order.push('\n');
    }
    artifacts.write_text(
        &format!("proof-stage/formal-sql/{WITNESS_MODULE_DIRECTORY}/ORDER"),
        &order,
    )
}

/// Write the minimal trusted-check workspace used only by the deterministic
/// typed-witness coverage gate. Query lowering is intentionally absent here:
/// support for a query operator must not decide whether the lowered schema and
/// its Witness.v inventory can be emitted and kernel-checked.
pub(super) fn write_typed_witness_audit_workspace(
    artifacts: &ArtifactWriter,
    schema: &FormalSchema,
    snapshot: &FormalWitnessSnapshot,
) -> Result<()> {
    let witness_modules = formal_sql_witness_modules(schema, Some(snapshot))?;
    artifacts.write_text("proof-stage/formal-sql/Schema.v", &schema.rocq_module)?;
    artifacts.write_text(
        "proof-stage/formal-sql/Queries.v",
        "From LogosGenerated Require Import Schema.\n\
         Definition typed_witness_audit_queries_marker : Prop := True.\n",
    )?;
    write_formal_sql_witness_modules(artifacts, &witness_modules)?;
    artifacts.write_text(
        "proof-stage/formal-sql/Problem.v",
        "From LogosGenerated Require Import Schema Queries Witness.\n\
         Lemma typed_witness_audit_available :\n\
           Witness.generated_witness_available = true.\n\
         Proof. reflexivity. Qed.\n\
         Lemma typed_witness_audit_schema_conforms :\n\
           Schema.generated_schema_conforms Witness.generated_witness_db.\n\
         Proof.\n\
           apply Witness.generated_witness_schema_conforms.\n\
           exact typed_witness_audit_available.\n\
         Qed.\n",
    )?;
    artifacts.write_text(
        "proof-stage/formal-sql/Goal.v",
        "From LogosGenerated Require Import Problem.\n\
         Definition typed_witness_audit_goal : Prop := True.\n",
    )?;
    Ok(())
}

fn formal_sql_goal_module(verification_mode: VerificationMode) -> String {
    let program_equivalence = match verification_mode {
        VerificationMode::SafeUnconditional => "query_program_possible_equiv",
        VerificationMode::OutcomeUnconditional | VerificationMode::Conditional => {
            "query_program_possible_outcome_equiv"
        }
    };
    let condition_parameter = match verification_mode {
        VerificationMode::Conditional => "\n    (condition : verification_condition)",
        VerificationMode::SafeUnconditional | VerificationMode::OutcomeUnconditional => "",
    };
    let condition_premise = match verification_mode {
        VerificationMode::Conditional => "      verification_condition_holds db condition ->\n",
        VerificationMode::SafeUnconditional | VerificationMode::OutcomeUnconditional => "",
    };
    let unconditional_claim_contract = match verification_mode {
        VerificationMode::SafeUnconditional | VerificationMode::OutcomeUnconditional => {
            "
Definition required_countermodel_statement : Prop :=
  Witness.generated_witness_available = true /\\
  Schema.generated_schema_conforms Witness.generated_witness_db /\\
      required_query_program_admissible
        Witness.generated_witness_db
        Queries.source_query_program /\\
      required_query_program_admissible
        Witness.generated_witness_db
        Queries.target_query_program /\\
      ~ required_query_program_outcome_equiv Witness.generated_witness_db
          Queries.source_query_program
          Queries.target_query_program.

Definition required_verification_statement
    (claim : verification_claim_kind) : Prop :=
  verification_claim_goal
    claim required_equivalence_statement required_countermodel_statement.
"
        }
        VerificationMode::Conditional => "",
    };
    let trusted_certificate = match verification_mode {
        VerificationMode::Conditional => {
            "
Theorem generated_precondition_certificate :
  precondition_source_obligation
    Schema.generated_schema
    Schema.generated_schema_constraints
    Problem.generated_precondition_source
    Problem.generated_precondition.
Proof.
  exact Problem.generated_precondition_valid.
Qed.

Theorem generated_equivalence_certificate :
  required_equivalence_statement Problem.generated_precondition.
Proof.
  exact Problem.generated_queries_equivalent.
Qed.
"
        }
        VerificationMode::SafeUnconditional | VerificationMode::OutcomeUnconditional => {
            "
Theorem generated_verification_certificate :
  required_verification_statement Problem.generated_verification_claim.
Proof.
  exact Problem.generated_queries_verified.
Qed.
"
        }
    };
    format!(
        "{FORMAL_SQL_GOAL_HEADER}
Definition required_query_program_equiv
    (db : db_state)
    (left right : list QueryExpr) : Prop :=
  @{program_equivalence} TNull relname
    (@_basesort TNull db)
    (@_instance TNull db)
    unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error
    required_value_is_null
    nil
    left
    right.

Definition required_query_program_outcome_equiv
    (db : db_state)
    (left right : list QueryExpr) : Prop :=
  @query_program_possible_outcome_equiv TNull relname
    (@_basesort TNull db)
    (@_instance TNull db)
    unknown3
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error
    required_value_is_null
    nil
    left
    right.

Definition required_query_program_admissible
    (db : db_state) (program : list QueryExpr) : Prop :=
  Forall
    (TNullQueryExprAdmissible (@_basesort TNull db))
    program.

Definition required_equivalence_statement{condition_parameter} : Prop :=
    Queries.source_program_output_signatures =
      map query_expr_outputs
        Queries.source_query_program /\\
    Queries.target_program_output_signatures =
      map query_expr_outputs
        Queries.target_query_program /\\
    Queries.source_program_output_signatures =
      Queries.target_program_output_signatures /\\
    (forall db : db_state,
      Schema.generated_schema_conforms db ->
{condition_premise}      required_query_program_admissible
        db Queries.source_query_program /\\
      required_query_program_admissible
        db Queries.target_query_program /\\
      required_query_program_equiv db
        Queries.source_query_program
        Queries.target_query_program).

{unconditional_claim_contract}

From LogosGenerated Require Problem.
{trusted_certificate}"
    )
}

fn formal_sql_bound_goal_module(verification_mode: VerificationMode) -> String {
    let program_equivalence = match verification_mode {
        VerificationMode::SafeUnconditional => "bound_query_program_possible_equiv",
        VerificationMode::OutcomeUnconditional | VerificationMode::Conditional => {
            "bound_query_program_demand_safe_outcome_equiv"
        }
    };
    let condition_parameter = match verification_mode {
        VerificationMode::Conditional => "\n    (condition : verification_condition)",
        VerificationMode::SafeUnconditional | VerificationMode::OutcomeUnconditional => "",
    };
    let condition_premise = match verification_mode {
        VerificationMode::Conditional => "      verification_condition_holds db condition ->\n",
        VerificationMode::SafeUnconditional | VerificationMode::OutcomeUnconditional => "",
    };
    let unconditional_claim_contract = match verification_mode {
        VerificationMode::SafeUnconditional | VerificationMode::OutcomeUnconditional => {
            "
Definition required_countermodel_statement : Prop :=
  Witness.generated_witness_available = true /\\
  Schema.generated_schema_conforms Witness.generated_witness_db /\\
      required_query_program_admissible
        Witness.generated_witness_db
        Queries.source_bound_query_program /\\
      required_query_program_admissible
        Witness.generated_witness_db
        Queries.target_bound_query_program /\\
      required_query_program_materialization_safe
        Witness.generated_witness_db
        Queries.source_bound_query_program /\\
      required_query_program_materialization_safe
        Witness.generated_witness_db
        Queries.target_bound_query_program /\\
      ~ required_query_program_outcome_equiv Witness.generated_witness_db
          Queries.source_bound_query_program
          Queries.target_bound_query_program.

Definition required_verification_statement
    (claim : verification_claim_kind) : Prop :=
  verification_claim_goal
    claim required_equivalence_statement required_countermodel_statement.
"
        }
        VerificationMode::Conditional => "",
    };
    let trusted_certificate = match verification_mode {
        VerificationMode::Conditional => {
            "
Theorem generated_precondition_certificate :
  precondition_source_obligation
    Schema.generated_schema
    Schema.generated_schema_constraints
    Problem.generated_precondition_source
    Problem.generated_precondition.
Proof.
  exact Problem.generated_precondition_valid.
Qed.

Theorem generated_equivalence_certificate :
  required_equivalence_statement Problem.generated_precondition.
Proof.
  exact Problem.generated_queries_equivalent.
Qed.
"
        }
        VerificationMode::SafeUnconditional | VerificationMode::OutcomeUnconditional => {
            "
Theorem generated_verification_certificate :
  required_verification_statement Problem.generated_verification_claim.
Proof.
  exact Problem.generated_queries_verified.
Qed.
"
        }
    };
    format!(
        "{FORMAL_SQL_GOAL_HEADER}
From Logos Require Import FormalSQL.QueryBindingSemantics.

Definition required_query_program_equiv
    (db : db_state)
    (left right : BoundQueryProgram) : Prop :=
  {program_equivalence}
    db Queries.generated_local_query_schemas nil left right.

Definition required_query_program_outcome_equiv
    (db : db_state)
    (left right : BoundQueryProgram) : Prop :=
  bound_query_program_possible_outcome_equiv
    db Queries.generated_local_query_schemas nil left right.

Definition required_query_program_materialization_safe
    (db : db_state) (program : BoundQueryProgram) : Prop :=
  bound_query_program_materialization_safe
    db Queries.generated_local_query_schemas nil program.

Definition required_query_program_admissible
    (db : db_state) (program : BoundQueryProgram) : Prop :=
  bound_query_program_admissible
    db Queries.generated_local_query_schemas program.

Definition required_equivalence_statement{condition_parameter} : Prop :=
    Queries.source_program_output_signatures =
      map bound_query_outputs
        Queries.source_bound_query_program /\\
    Queries.target_program_output_signatures =
      map bound_query_outputs
        Queries.target_bound_query_program /\\
    Queries.source_program_output_signatures =
      Queries.target_program_output_signatures /\\
    (forall db : db_state,
      Schema.generated_schema_conforms db ->
{condition_premise}      required_query_program_admissible
        db Queries.source_bound_query_program /\\
      required_query_program_admissible
        db Queries.target_bound_query_program /\\
      required_query_program_equiv db
        Queries.source_bound_query_program
        Queries.target_bound_query_program).

{unconditional_claim_contract}

From LogosGenerated Require Problem.
{trusted_certificate}"
    )
}

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

struct SkeletonTreeParser<'a> {
    input: &'a str,
    position: usize,
    role: &'a str,
}

impl SkeletonTree {
    fn render(&self) -> String {
        let mut rendered = self.head.clone();
        if !self.children.is_empty() {
            rendered.push('(');
            for (index, child) in self.children.iter().enumerate() {
                if index > 0 {
                    rendered.push(',');
                }
                rendered.push_str(&child.render());
            }
            rendered.push(')');
        }
        rendered
    }

    fn metrics(&self) -> (usize, usize) {
        let mut node_count = 1;
        let mut child_depth = 0;
        for child in &self.children {
            let (child_nodes, depth) = child.metrics();
            node_count += child_nodes;
            child_depth = child_depth.max(depth);
        }
        (node_count, child_depth + 1)
    }
}

impl<'a> SkeletonTreeParser<'a> {
    fn error(&self, message: impl AsRef<str>) -> Error {
        Error::ProofAgentCommand(format!(
            "query context drift: malformed {} skeleton at byte {}: {}",
            self.role,
            self.position,
            message.as_ref()
        ))
    }

    fn parse(mut self) -> Result<SkeletonTree> {
        if self.input.is_empty() {
            return Err(self.error("empty tree"));
        }
        if !self.input.is_ascii() {
            return Err(self.error("tree must use the emitter's ASCII-safe notation"));
        }
        let tree = self.parse_node()?;
        if self.position != self.input.len() {
            return Err(self.error("trailing bytes after the root node"));
        }
        if tree.render() != self.input {
            return Err(self.error("parser round trip changed the tree"));
        }
        Ok(tree)
    }

    fn parse_node(&mut self) -> Result<SkeletonTree> {
        let bytes = self.input.as_bytes();
        let head_start = self.position;
        while self.position < bytes.len()
            && !matches!(bytes[self.position], b'{' | b'}' | b'(' | b')' | b',')
        {
            self.position += 1;
        }
        if self.position == head_start {
            return Err(self.error("missing node head"));
        }
        let bare_head = &self.input[head_start..self.position];
        if bare_head.trim() != bare_head
            || bare_head
                .bytes()
                .any(|byte| byte.is_ascii_whitespace() && byte != b' ')
        {
            return Err(self.error(
                "node heads may contain only internal ASCII spaces, not boundary or control whitespace",
            ));
        }
        let mut head = bare_head.to_owned();

        if bytes.get(self.position) == Some(&b'{') {
            let fields_start = self.position;
            self.position += 1;
            let content_start = self.position;
            while self.position < bytes.len() && bytes[self.position] != b'}' {
                if matches!(bytes[self.position], b'{' | b'(' | b')') {
                    return Err(self.error("invalid delimiter inside compact fields"));
                }
                self.position += 1;
            }
            if self.position == bytes.len() {
                return Err(self.error("unterminated compact fields"));
            }
            if self.position == content_start {
                return Err(self.error("empty compact fields"));
            }
            self.position += 1;
            head.push_str(&self.input[fields_start..self.position]);
        }

        let mut children = Vec::new();
        if bytes.get(self.position) == Some(&b'(') {
            self.position += 1;
            if bytes.get(self.position) == Some(&b')') {
                return Err(self.error("empty child list is not canonical"));
            }
            loop {
                if self.position == bytes.len() {
                    return Err(self.error("unterminated child list"));
                }
                children.push(self.parse_node()?);
                match bytes.get(self.position) {
                    Some(b',') => {
                        self.position += 1;
                        if bytes.get(self.position) == Some(&b')') {
                            return Err(self.error("trailing comma in child list"));
                        }
                    }
                    Some(b')') => {
                        self.position += 1;
                        break;
                    }
                    Some(_) => {
                        return Err(self.error("expected ',' or ')' after child node"));
                    }
                    None => return Err(self.error("unterminated child list")),
                }
            }
        }

        Ok(SkeletonTree { head, children })
    }
}

fn parse_skeleton_tree(tree: &str, role: &str) -> Result<SkeletonTree> {
    SkeletonTreeParser {
        input: tree,
        position: 0,
        role,
    }
    .parse()
}

fn intern_skeleton_tree(
    tree: &SkeletonTree,
    index: &mut BTreeMap<(String, Vec<usize>), usize>,
    nodes: &mut Vec<CompactSkeletonNode>,
) -> usize {
    let children = tree
        .children
        .iter()
        .map(|child| intern_skeleton_tree(child, index, nodes))
        .collect::<Vec<_>>();
    let key = (tree.head.clone(), children.clone());
    if let Some(node_id) = index.get(&key) {
        return *node_id;
    }
    let node_id = nodes.len();
    nodes.push(CompactSkeletonNode(tree.head.clone(), children));
    index.insert(key, node_id);
    node_id
}

fn expand_compact_skeleton_node(nodes: &[CompactSkeletonNode], node_id: usize) -> Result<String> {
    let CompactSkeletonNode(head, children) = nodes.get(node_id).ok_or_else(|| {
        Error::ProofAgentCommand(format!(
            "query context drift: compact skeleton root {node_id} is out of range"
        ))
    })?;
    let mut expanded = head.clone();
    if !children.is_empty() {
        expanded.push('(');
        for (index, child) in children.iter().enumerate() {
            if index > 0 {
                expanded.push(',');
            }
            expanded.push_str(&expand_compact_skeleton_node(nodes, *child)?);
        }
        expanded.push(')');
    }
    Ok(expanded)
}

fn compact_skeleton_digest(trees: &[&str]) -> Result<String> {
    Ok(sha256_hex(&serde_json::to_vec(trees)?))
}

fn validate_compacted_skeleton_forest(
    compacted: &CompactedSkeletonForest,
    expected_trees: &[&str],
    role: &str,
) -> Result<()> {
    if compacted.roots.len() != expected_trees.len() {
        return Err(Error::ProofAgentCommand(format!(
            "query context drift: compact {role} skeleton has {} roots for {} trees",
            compacted.roots.len(),
            expected_trees.len()
        )));
    }
    let mut unique_nodes = BTreeMap::new();
    for (node_id, CompactSkeletonNode(head, children)) in compacted.nodes.iter().enumerate() {
        if head.is_empty() {
            return Err(Error::ProofAgentCommand(format!(
                "query context drift: compact {role} skeleton node {node_id} has an empty head"
            )));
        }
        if children.iter().any(|child| *child >= node_id) {
            return Err(Error::ProofAgentCommand(format!(
                "query context drift: compact {role} skeleton node {node_id} is not in strict postorder"
            )));
        }
        let key = (head.clone(), children.clone());
        if let Some(previous) = unique_nodes.insert(key, node_id) {
            return Err(Error::ProofAgentCommand(format!(
                "query context drift: compact {role} skeleton duplicates nodes {previous} and {node_id}"
            )));
        }
    }

    let mut reachable = BTreeSet::new();
    fn mark_reachable(
        nodes: &[CompactSkeletonNode],
        node_id: usize,
        reachable: &mut BTreeSet<usize>,
    ) -> Result<()> {
        let node = nodes.get(node_id).ok_or_else(|| {
            Error::ProofAgentCommand(format!(
                "query context drift: compact skeleton node {node_id} is out of range"
            ))
        })?;
        if reachable.insert(node_id) {
            for child in &node.1 {
                mark_reachable(nodes, *child, reachable)?;
            }
        }
        Ok(())
    }

    for ((root, expected), index) in compacted.roots.iter().zip(expected_trees).zip(1usize..) {
        mark_reachable(&compacted.nodes, *root, &mut reachable)?;
        let expanded = expand_compact_skeleton_node(&compacted.nodes, *root)?;
        if expanded != *expected {
            return Err(Error::ProofAgentCommand(format!(
                "query context drift: compact {role} skeleton root {index} does not round-trip exactly"
            )));
        }
    }
    if reachable.len() != compacted.nodes.len() {
        return Err(Error::ProofAgentCommand(format!(
            "query context drift: compact {role} skeleton contains unreachable nodes"
        )));
    }
    let expected_digest = compact_skeleton_digest(expected_trees)?;
    if compacted.expanded_trees_sha256 != expected_digest {
        return Err(Error::ProofAgentCommand(format!(
            "query context drift: compact {role} skeleton expansion digest disagrees with its input trees"
        )));
    }
    Ok(())
}

fn compact_skeleton_forest(trees: &[&str], role: &str) -> Result<CompactedSkeletonForest> {
    let parsed = trees
        .iter()
        .map(|tree| parse_skeleton_tree(tree, role))
        .collect::<Result<Vec<_>>>()?;
    let mut nodes = Vec::new();
    let mut index = BTreeMap::new();
    let roots = parsed
        .iter()
        .map(|tree| intern_skeleton_tree(tree, &mut index, &mut nodes))
        .collect::<Vec<_>>();
    let compacted = CompactedSkeletonForest {
        expanded_trees_sha256: compact_skeleton_digest(trees)?,
        nodes,
        roots,
    };
    validate_compacted_skeleton_forest(&compacted, trees, role)?;
    Ok(compacted)
}

fn serialized_enum_name(value: &impl Serialize, role: &str) -> Result<String> {
    let value = serde_json::to_value(value)?;
    value.as_str().map(str::to_owned).ok_or_else(|| {
        Error::ProofAgentCommand(format!(
            "query context drift: {role} did not serialize as a string"
        ))
    })
}

fn validate_compact_definition_graph(
    compact: &CompactDefinitionGraph,
    expanded: &FormalQueryDefinitionGraph,
) -> Result<()> {
    if compact.schema_version != 2
        || compact.notation != COMPACT_DEFINITION_GRAPH_NOTATION
        || compact.expanded_graph_sha256 != sha256_hex(&serde_json::to_vec(expanded)?)
        || compact.opaque_helper_symbols != expanded.opaque_helper_symbols
        || compact.source_statements != expanded.source_statements
        || compact.target_statements != expanded.target_statements
        || compact.definitions.len() != expanded.definitions.len()
    {
        return Err(Error::ProofAgentCommand(
            "query context drift: compact emitted definition graph metadata disagrees with the emitter graph"
                .to_owned(),
        ));
    }
    let trees = expanded
        .definitions
        .iter()
        .map(|definition| definition.tree.as_str())
        .collect::<Vec<_>>();
    let compacted = CompactedSkeletonForest {
        expanded_trees_sha256: compact.expanded_trees_sha256.clone(),
        nodes: compact.skeleton_nodes.clone(),
        roots: compact
            .definitions
            .iter()
            .map(|definition| definition.root_node)
            .collect(),
    };
    validate_compacted_skeleton_forest(&compacted, &trees, "emitted definition graph")?;
    for (compact_definition, expanded_definition) in
        compact.definitions.iter().zip(&expanded.definitions)
    {
        if compact_definition.symbol != expanded_definition.symbol
            || compact_definition.kind
                != serialized_enum_name(&expanded_definition.kind, "emitted definition kind")?
        {
            return Err(Error::ProofAgentCommand(format!(
                "query context drift: compact mapping for emitted definition {} changed its symbol or kind",
                expanded_definition.symbol
            )));
        }
    }
    Ok(())
}

fn compact_definition_graph(graph: &FormalQueryDefinitionGraph) -> Result<CompactDefinitionGraph> {
    let trees = graph
        .definitions
        .iter()
        .map(|definition| definition.tree.as_str())
        .collect::<Vec<_>>();
    let compacted = compact_skeleton_forest(&trees, "emitted definition graph")?;
    let definitions = graph
        .definitions
        .iter()
        .zip(&compacted.roots)
        .map(|(definition, root_node)| {
            Ok(CompactShapeDefinition {
                symbol: definition.symbol.clone(),
                kind: serialized_enum_name(&definition.kind, "emitted definition kind")?,
                root_node: *root_node,
            })
        })
        .collect::<Result<Vec<_>>>()?;
    let compact = CompactDefinitionGraph {
        schema_version: 2,
        notation: COMPACT_DEFINITION_GRAPH_NOTATION,
        expanded_graph_sha256: sha256_hex(&serde_json::to_vec(graph)?),
        expanded_trees_sha256: compacted.expanded_trees_sha256,
        opaque_helper_symbols: graph.opaque_helper_symbols.clone(),
        skeleton_nodes: compacted.nodes,
        definitions,
        source_statements: graph.source_statements.clone(),
        target_statements: graph.target_statements.clone(),
    };
    validate_compact_definition_graph(&compact, graph)?;
    Ok(compact)
}

fn compact_query_statement(
    statement: &QueryStatementShape,
    root_node: usize,
) -> CompactQueryStatementShape {
    CompactQueryStatementShape {
        statement_index: statement.statement_index,
        exact_sql_sha256: statement.exact_sql_sha256.clone(),
        frontend_sql_sha256: statement.frontend_sql_sha256.clone(),
        exact_frontend_bytes_equal: statement.exact_frontend_bytes_equal,
        emitted_rocq_root_symbol: statement.emitted_rocq_root_symbol.clone(),
        emitted_rocq_output_signature_symbol: statement
            .emitted_rocq_output_signature_symbol
            .clone(),
        final_output_canonicalization: statement.final_output_canonicalization,
        output_signature: statement.output_signature.clone(),
        typed_frontend_tree: CompactOperatorTreeRoot {
            node_count: statement.typed_frontend_tree.node_count,
            max_depth: statement.typed_frontend_tree.max_depth,
            root_node,
        },
    }
}

fn compact_frontend_programs(
    source: &[QueryStatementShape],
    target: &[QueryStatementShape],
) -> Result<(
    CompactSkeletonDag,
    Vec<CompactQueryStatementShape>,
    Vec<CompactQueryStatementShape>,
)> {
    let statements = source.iter().chain(target).collect::<Vec<_>>();
    for statement in &statements {
        let parsed = parse_skeleton_tree(
            &statement.typed_frontend_tree.expression,
            "typed frontend operator",
        )?;
        let (node_count, max_depth) = parsed.metrics();
        if node_count != statement.typed_frontend_tree.node_count
            || max_depth != statement.typed_frontend_tree.max_depth
        {
            return Err(Error::ProofAgentCommand(format!(
                "query context drift: typed frontend skeleton metrics disagree for statement {}",
                statement.statement_index
            )));
        }
    }
    let trees = statements
        .iter()
        .map(|statement| statement.typed_frontend_tree.expression.as_str())
        .collect::<Vec<_>>();
    let compacted = compact_skeleton_forest(&trees, "typed frontend operator")?;
    let (source_roots, target_roots) = compacted.roots.split_at(source.len());
    let compact_source = source
        .iter()
        .zip(source_roots)
        .map(|(statement, root)| compact_query_statement(statement, *root))
        .collect();
    let compact_target = target
        .iter()
        .zip(target_roots)
        .map(|(statement, root)| compact_query_statement(statement, *root))
        .collect();
    Ok((
        CompactSkeletonDag {
            schema_version: 1,
            notation: COMPACT_FRONTEND_SKELETON_NOTATION,
            expanded_trees_sha256: compacted.expanded_trees_sha256,
            nodes: compacted.nodes,
        },
        compact_source,
        compact_target,
    ))
}

fn context_binding(path: impl Into<String>, bytes: &[u8]) -> ContextFileBinding {
    ContextFileBinding {
        path: path.into(),
        bytes: bytes.len(),
        sha256: sha256_hex(bytes),
    }
}

fn compact_formal_attributes(attributes: &[FormalAttribute]) -> Vec<CompactAttribute> {
    attributes
        .iter()
        .map(|attribute| CompactAttribute {
            name: attribute.name.clone(),
            r#type: format!("{:?}", attribute.ty),
            nullable: None,
        })
        .collect()
}

fn ordered_signature_operator_kind(query: &FormalQueryExpr) -> &'static str {
    match query {
        FormalQueryExpr::Error { .. } => "Error",
        FormalQueryExpr::Empty { .. } => "Empty",
        FormalQueryExpr::EmptyTuple => "EmptyTuple",
        FormalQueryExpr::Table { .. } => "Table",
        FormalQueryExpr::Set { .. } => "Set",
        FormalQueryExpr::CrossJoin { .. } => "CrossJoin",
        FormalQueryExpr::Join { .. } => "Join",
        FormalQueryExpr::Projection { .. } => "Projection",
        FormalQueryExpr::Selection { .. } => "Selection",
        FormalQueryExpr::Group { .. } => "Group",
        FormalQueryExpr::GroupingSets { .. } => "GroupingSets",
        FormalQueryExpr::Rank { .. } => "Rank",
        FormalQueryExpr::Window { .. } => "Window",
        FormalQueryExpr::Distinct { .. } => "Distinct",
        FormalQueryExpr::OrderBy { .. } => "OrderBy",
        FormalQueryExpr::Offset { .. } => "Offset",
        FormalQueryExpr::Fetch { .. } => "Fetch",
    }
}

#[derive(Default)]
struct OrderedSignatureArtifactBuilder {
    exact_signatures: Vec<Vec<FormalAttribute>>,
    signature_pool: Vec<OrderedSignaturePoolEntry>,
    nodes: Vec<OrderedSignatureNodeRecord>,
}

impl OrderedSignatureArtifactBuilder {
    fn intern_signature(&mut self, signature: &[FormalAttribute]) -> String {
        if let Some(index) = self
            .exact_signatures
            .iter()
            .position(|candidate| candidate == signature)
        {
            return format!("SIG{index}");
        }
        let index = self.exact_signatures.len();
        self.exact_signatures.push(signature.to_vec());
        self.signature_pool.push(OrderedSignaturePoolEntry {
            signature_id: format!("SIG{index}"),
            arity: signature.len(),
            attributes: compact_formal_attributes(signature),
        });
        format!("SIG{index}")
    }

    fn add_query_occurrence(
        &mut self,
        side: &'static str,
        side_prefix: char,
        statement_index: usize,
        role_path: String,
        parent_node_id: Option<String>,
        query: &FormalQueryExpr,
        next_preorder: &mut usize,
    ) -> Result<String> {
        let exact_signature = query_expr_output_signature(query).ok_or_else(|| {
            Error::ProofAgentCommand(format!(
                "cannot derive ordered signature for {side} statement {statement_index} at {role_path}"
            ))
        })?;
        let preorder_index = *next_preorder;
        *next_preorder += 1;
        let node_id = format!("{side_prefix}{statement_index}.N{preorder_index}");
        let signature_id = self.intern_signature(&exact_signature);
        let record_index = self.nodes.len();
        self.nodes.push(OrderedSignatureNodeRecord {
            artifact: OrderedSignatureNode {
                node_id: node_id.clone(),
                side,
                statement_index,
                preorder_index,
                role_path: role_path.clone(),
                operator_kind: ordered_signature_operator_kind(query),
                signature_id,
                arity: exact_signature.len(),
                parent_node_id,
                children: Vec::new(),
            },
            exact_signature,
        });

        let mut children = Vec::new();
        let mut add_relational_child =
            |builder: &mut Self, role: &str, child: &FormalQueryExpr| -> Result<()> {
                let child_id = builder.add_query_occurrence(
                    side,
                    side_prefix,
                    statement_index,
                    format!("{role_path}.{role}"),
                    Some(node_id.clone()),
                    child,
                    next_preorder,
                )?;
                children.push(OrderedSignatureChild {
                    role: role.to_owned(),
                    edge_kind: "relational",
                    node_id: child_id,
                });
                Ok(())
            };

        match query {
            FormalQueryExpr::Set { left, right, .. }
            | FormalQueryExpr::CrossJoin { left, right } => {
                add_relational_child(self, "left", left)?;
                add_relational_child(self, "right", right)?;
            }
            FormalQueryExpr::Join {
                predicate,
                matched_select,
                left_select,
                right_select,
                left,
                right,
                ..
            } => {
                add_relational_child(self, "left", left)?;
                add_relational_child(self, "right", right)?;
                self.add_scalar_subqueries(
                    side,
                    side_prefix,
                    statement_index,
                    &role_path,
                    "predicate",
                    &node_id,
                    predicate,
                    next_preorder,
                    &mut children,
                )?;
                for (list_role, select) in [
                    ("matchedSelect", matched_select),
                    ("leftSelect", left_select),
                    ("rightSelect", right_select),
                ] {
                    for (index, item) in select.iter().enumerate() {
                        self.add_scalar_subqueries(
                            side,
                            side_prefix,
                            statement_index,
                            &role_path,
                            &format!("{list_role}[{index}]"),
                            &node_id,
                            &item.expr,
                            next_preorder,
                            &mut children,
                        )?;
                    }
                }
            }
            FormalQueryExpr::Rank { input, .. }
            | FormalQueryExpr::Window { input, .. }
            | FormalQueryExpr::Distinct { input }
            | FormalQueryExpr::OrderBy { input, .. }
            | FormalQueryExpr::Offset { input, .. }
            | FormalQueryExpr::Fetch { input, .. } => {
                add_relational_child(self, "input", input)?;
            }
            FormalQueryExpr::Projection { select, input } => {
                add_relational_child(self, "input", input)?;
                for (index, item) in select.iter().enumerate() {
                    self.add_scalar_subqueries(
                        side,
                        side_prefix,
                        statement_index,
                        &role_path,
                        &format!("select[{index}]"),
                        &node_id,
                        &item.expr,
                        next_preorder,
                        &mut children,
                    )?;
                }
            }
            FormalQueryExpr::Selection { predicate, input } => {
                add_relational_child(self, "input", input)?;
                self.add_scalar_subqueries(
                    side,
                    side_prefix,
                    statement_index,
                    &role_path,
                    "predicate",
                    &node_id,
                    predicate,
                    next_preorder,
                    &mut children,
                )?;
            }
            FormalQueryExpr::Group {
                select,
                group_by,
                having,
                input,
                ..
            } => {
                add_relational_child(self, "input", input)?;
                for (index, item) in select.iter().enumerate() {
                    self.add_scalar_subqueries(
                        side,
                        side_prefix,
                        statement_index,
                        &role_path,
                        &format!("select[{index}]"),
                        &node_id,
                        &item.expr,
                        next_preorder,
                        &mut children,
                    )?;
                }
                for (index, key) in group_by.iter().enumerate() {
                    self.add_scalar_subqueries(
                        side,
                        side_prefix,
                        statement_index,
                        &role_path,
                        &format!("groupBy[{index}]"),
                        &node_id,
                        key,
                        next_preorder,
                        &mut children,
                    )?;
                }
                self.add_scalar_subqueries(
                    side,
                    side_prefix,
                    statement_index,
                    &role_path,
                    "having",
                    &node_id,
                    having,
                    next_preorder,
                    &mut children,
                )?;
            }
            FormalQueryExpr::GroupingSets {
                grouping_sets,
                input,
            } => {
                add_relational_child(self, "input", input)?;
                for (set_index, grouping_set) in grouping_sets.iter().enumerate() {
                    for (index, item) in grouping_set.select.iter().enumerate() {
                        self.add_scalar_subqueries(
                            side,
                            side_prefix,
                            statement_index,
                            &role_path,
                            &format!("groupingSets[{set_index}].select[{index}]"),
                            &node_id,
                            &item.expr,
                            next_preorder,
                            &mut children,
                        )?;
                    }
                    for (index, key) in grouping_set.group_by.iter().enumerate() {
                        self.add_scalar_subqueries(
                            side,
                            side_prefix,
                            statement_index,
                            &role_path,
                            &format!("groupingSets[{set_index}].groupBy[{index}]"),
                            &node_id,
                            key,
                            next_preorder,
                            &mut children,
                        )?;
                    }
                }
            }
            FormalQueryExpr::Error { .. }
            | FormalQueryExpr::Empty { .. }
            | FormalQueryExpr::EmptyTuple
            | FormalQueryExpr::Table { .. } => {}
        }
        self.nodes[record_index].artifact.children = children;
        Ok(node_id)
    }

    #[allow(clippy::too_many_arguments)]
    fn add_scalar_subqueries(
        &mut self,
        side: &'static str,
        side_prefix: char,
        statement_index: usize,
        parent_role_path: &str,
        scalar_role: &str,
        parent_node_id: &str,
        expression: &FormalScalarExpr,
        next_preorder: &mut usize,
        children: &mut Vec<OrderedSignatureChild>,
    ) -> Result<()> {
        let mut visit =
            |builder: &mut Self, role: String, child: &FormalScalarExpr| -> Result<()> {
                builder.add_scalar_subqueries(
                    side,
                    side_prefix,
                    statement_index,
                    parent_role_path,
                    &role,
                    parent_node_id,
                    child,
                    next_preorder,
                    children,
                )
            };
        match expression {
            FormalScalarExpr::Leaf { .. } | FormalScalarExpr::True => Ok(()),
            FormalScalarExpr::Call { args, .. } | FormalScalarExpr::Predicate { args, .. } => {
                for (index, arg) in args.iter().enumerate() {
                    visit(self, format!("{scalar_role}.args[{index}]"), arg)?;
                }
                Ok(())
            }
            FormalScalarExpr::Case {
                condition,
                then_expr,
                else_expr,
                ..
            } => {
                visit(self, format!("{scalar_role}.condition"), condition)?;
                visit(self, format!("{scalar_role}.then"), then_expr)?;
                visit(self, format!("{scalar_role}.else"), else_expr)
            }
            FormalScalarExpr::BooleanValue { expression }
            | FormalScalarExpr::ValueBoolean { expression }
            | FormalScalarExpr::Not { expression } => {
                visit(self, format!("{scalar_role}.expression"), expression)
            }
            FormalScalarExpr::And { operands, .. } | FormalScalarExpr::Or { operands, .. } => {
                for (index, operand) in operands.iter().enumerate() {
                    visit(self, format!("{scalar_role}.operands[{index}]"), operand)?;
                }
                Ok(())
            }
            FormalScalarExpr::QuantifiedComparison { args, query, .. } => {
                for (index, arg) in args.iter().enumerate() {
                    visit(self, format!("{scalar_role}.args[{index}]"), arg)?;
                }
                self.add_scalar_query(
                    side,
                    side_prefix,
                    statement_index,
                    parent_role_path,
                    &format!("{scalar_role}.quantifiedComparison.query"),
                    parent_node_id,
                    query,
                    next_preorder,
                    children,
                )
            }
            FormalScalarExpr::In { args, query } => {
                for (index, arg) in args.iter().enumerate() {
                    visit(self, format!("{scalar_role}.args[{index}]"), arg)?;
                }
                self.add_scalar_query(
                    side,
                    side_prefix,
                    statement_index,
                    parent_role_path,
                    &format!("{scalar_role}.in.query"),
                    parent_node_id,
                    query,
                    next_preorder,
                    children,
                )
            }
            FormalScalarExpr::Exists { query } => self.add_scalar_query(
                side,
                side_prefix,
                statement_index,
                parent_role_path,
                &format!("{scalar_role}.exists.query"),
                parent_node_id,
                query,
                next_preorder,
                children,
            ),
            FormalScalarExpr::Subquery { query, .. } => self.add_scalar_query(
                side,
                side_prefix,
                statement_index,
                parent_role_path,
                &format!("{scalar_role}.subquery.query"),
                parent_node_id,
                query,
                next_preorder,
                children,
            ),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn add_scalar_query(
        &mut self,
        side: &'static str,
        side_prefix: char,
        statement_index: usize,
        parent_role_path: &str,
        edge_role: &str,
        parent_node_id: &str,
        query: &FormalQueryExpr,
        next_preorder: &mut usize,
        children: &mut Vec<OrderedSignatureChild>,
    ) -> Result<()> {
        let child_id = self.add_query_occurrence(
            side,
            side_prefix,
            statement_index,
            format!("{parent_role_path}.{edge_role}"),
            Some(parent_node_id.to_owned()),
            query,
            next_preorder,
        )?;
        children.push(OrderedSignatureChild {
            role: edge_role.to_owned(),
            edge_kind: "scalar_subquery",
            node_id: child_id,
        });
        Ok(())
    }

    fn add_program(
        &mut self,
        side: &'static str,
        side_prefix: char,
        program: &LoweredProgram,
    ) -> Result<Vec<OrderedSignatureStatement>> {
        let statement_count = program.statements.len();
        program
            .statements
            .iter()
            .enumerate()
            .map(|(zero_index, statement)| {
                let statement_index = zero_index + 1;
                let query = statement.query_expr.as_ref().ok_or_else(|| {
                    Error::ProofAgentCommand(format!(
                        "cannot build ordered-signature navigation for {side} statement {statement_index}: FormalSQL lowering is incomplete"
                    ))
                })?;
                let declared_signature = statement.output_signature.as_ref().ok_or_else(|| {
                    Error::ProofAgentCommand(format!(
                        "cannot build ordered-signature navigation for {side} statement {statement_index}: lowered output signature is incomplete"
                    ))
                })?;
                let recomputed_signature = query_expr_output_signature(query).ok_or_else(|| {
                    Error::ProofAgentCommand(format!(
                        "cannot build ordered-signature navigation for {side} statement {statement_index}: root signature is inconsistent"
                    ))
                })?;
                if &recomputed_signature != declared_signature {
                    return Err(Error::ProofAgentCommand(format!(
                        "ordered-signature context drift for {side} statement {statement_index}: recomputed root signature differs from LoweredQuery.output_signature"
                    )));
                }
                let before = self.nodes.len();
                let mut next_preorder = 0;
                let root_node_id = self.add_query_occurrence(
                    side,
                    side_prefix,
                    statement_index,
                    "root".to_owned(),
                    None,
                    query,
                    &mut next_preorder,
                )?;
                let suffix = if statement_count == 1 {
                    String::new()
                } else {
                    format!("_{zero_index}")
                };
                Ok(OrderedSignatureStatement {
                    statement_index,
                    emitted_rocq_root_symbol: format!("{side}_query_expr{suffix}"),
                    root_node_id,
                    node_count: self.nodes.len() - before,
                })
            })
            .collect()
    }
}

fn ordered_signature_mismatch(
    source: &[FormalAttribute],
    target: &[FormalAttribute],
) -> Option<OrderedSignatureMismatch> {
    if source == target {
        return None;
    }
    let first_differing_index = (0..source.len().max(target.len()))
        .find(|index| source.get(*index) != target.get(*index))
        .expect("unequal signatures have a first differing position");
    Some(OrderedSignatureMismatch {
        kind: if first_differing_index < source.len().min(target.len()) {
            "ordered_attribute"
        } else {
            "arity"
        },
        source_arity: source.len(),
        target_arity: target.len(),
        first_differing_index,
        source_attribute: source
            .get(first_differing_index)
            .map(|attribute| compact_formal_attributes(std::slice::from_ref(attribute)).remove(0)),
        target_attribute: target
            .get(first_differing_index)
            .map(|attribute| compact_formal_attributes(std::slice::from_ref(attribute)).remove(0)),
    })
}

fn ordered_signature_aligned_ancestor_chain_is_compatible(
    source_index: usize,
    target_index: usize,
    nodes: &[OrderedSignatureNodeRecord],
    node_by_id: &BTreeMap<String, usize>,
) -> bool {
    let mut source = &nodes[source_index];
    let mut target = &nodes[target_index];
    loop {
        if source.artifact.statement_index != target.artifact.statement_index
            || source.artifact.role_path != target.artifact.role_path
            || source.artifact.operator_kind != target.artifact.operator_kind
            || source.exact_signature != target.exact_signature
        {
            return false;
        }
        match (
            source.artifact.parent_node_id.as_ref(),
            target.artifact.parent_node_id.as_ref(),
        ) {
            (None, None) => return source.artifact.role_path == "root",
            (Some(source_parent), Some(target_parent)) => {
                let (Some(source_parent_index), Some(target_parent_index)) =
                    (node_by_id.get(source_parent), node_by_id.get(target_parent))
                else {
                    return false;
                };
                source = &nodes[*source_parent_index];
                target = &nodes[*target_parent_index];
            }
            _ => return false,
        }
    }
}

fn build_ordered_signatures(source: &LoweredProgram, target: &LoweredProgram) -> Result<String> {
    let mut builder = OrderedSignatureArtifactBuilder::default();
    let source_program = builder.add_program("source", 'S', source)?;
    let target_program = builder.add_program("target", 'T', target)?;

    let source_by_role = builder
        .nodes
        .iter()
        .enumerate()
        .filter(|(_, node)| node.artifact.side == "source")
        .map(|(index, node)| {
            (
                (
                    node.artifact.statement_index,
                    node.artifact.role_path.clone(),
                ),
                index,
            )
        })
        .collect::<BTreeMap<_, _>>();
    let target_by_role = builder
        .nodes
        .iter()
        .enumerate()
        .filter(|(_, node)| node.artifact.side == "target")
        .map(|(index, node)| {
            (
                (
                    node.artifact.statement_index,
                    node.artifact.role_path.clone(),
                ),
                index,
            )
        })
        .collect::<BTreeMap<_, _>>();
    let node_by_id = builder
        .nodes
        .iter()
        .enumerate()
        .map(|(index, node)| (node.artifact.node_id.clone(), index))
        .collect::<BTreeMap<_, _>>();

    let mut comparisons = Vec::new();
    let mut frontier_hints = Vec::new();
    for ((statement_index, role_path), source_index) in &source_by_role {
        let Some(target_index) = target_by_role.get(&(*statement_index, role_path.clone())) else {
            continue;
        };
        let source_node = &builder.nodes[*source_index];
        let target_node = &builder.nodes[*target_index];
        let signature_equal = source_node.exact_signature == target_node.exact_signature;
        let operator_kind_equal =
            source_node.artifact.operator_kind == target_node.artifact.operator_kind;
        comparisons.push(OrderedSignatureComparison {
            statement_index: *statement_index,
            role_path: role_path.clone(),
            source_node_id: source_node.artifact.node_id.clone(),
            target_node_id: target_node.artifact.node_id.clone(),
            source_operator_kind: source_node.artifact.operator_kind,
            target_operator_kind: target_node.artifact.operator_kind,
            operator_kind_equal,
            source_signature_id: source_node.artifact.signature_id.clone(),
            target_signature_id: target_node.artifact.signature_id.clone(),
            signature_equal,
            mismatch: ordered_signature_mismatch(
                &source_node.exact_signature,
                &target_node.exact_signature,
            ),
        });

        if !signature_equal
            || !operator_kind_equal
            || !ordered_signature_aligned_ancestor_chain_is_compatible(
                *source_index,
                *target_index,
                &builder.nodes,
                &node_by_id,
            )
        {
            continue;
        }
        let source_relational = source_node
            .artifact
            .children
            .iter()
            .filter(|child| child.edge_kind == "relational")
            .map(|child| (child.role.as_str(), child.node_id.as_str()))
            .collect::<BTreeMap<_, _>>();
        let target_relational = target_node
            .artifact
            .children
            .iter()
            .filter(|child| child.edge_kind == "relational")
            .map(|child| (child.role.as_str(), child.node_id.as_str()))
            .collect::<BTreeMap<_, _>>();
        let roles = source_relational
            .keys()
            .chain(target_relational.keys())
            .copied()
            .collect::<BTreeSet<_>>();
        let incompatible_relational_child_roles = roles
            .into_iter()
            .filter(|role| {
                let (Some(source_child_id), Some(target_child_id)) =
                    (source_relational.get(role), target_relational.get(role))
                else {
                    return true;
                };
                let source_child = &builder.nodes[node_by_id[*source_child_id]];
                let target_child = &builder.nodes[node_by_id[*target_child_id]];
                source_child.artifact.operator_kind != target_child.artifact.operator_kind
                    || source_child.exact_signature != target_child.exact_signature
            })
            .map(str::to_owned)
            .collect::<Vec<_>>();

        // Experimental navigation heuristic: no controlled on/off ablation has
        // yet measured whether exposing these frontier hints improves proof
        // success, search time, or token use.  Existing runs changed other
        // prompts and proof interfaces at the same time, so they cannot support
        // that causal claim.  Treat a hint only as a candidate inspection point,
        // never as semantic evidence, and revisit this mechanism after an
        // otherwise-identical ablation.
        if !incompatible_relational_child_roles.is_empty() {
            frontier_hints.push(OrderedSignatureFrontierHint {
                statement_index: *statement_index,
                role_path: role_path.clone(),
                source_node_id: source_node.artifact.node_id.clone(),
                target_node_id: target_node.artifact.node_id.clone(),
                operator_kind: source_node.artifact.operator_kind,
                signature_id: source_node.artifact.signature_id.clone(),
                incompatible_relational_child_roles,
                reason: "same aligned operator kind and exact ordered signature, with at least one direct relational child that is missing, differently shaped, or has a different exact ordered signature; navigation hint only",
            });
        }
    }

    let artifact = OrderedSignaturesArtifact {
        schema_version: 2,
        authority: "navigation_only; exact SQL, generated Rocq, FormalSQL semantics, and Rocq kernel checking remain authoritative; no node, comparison, or frontier hint proves query equivalence",
        derivation: "host-derived from every occurrence in the successfully lowered FormalQueryExpr trees using the same query_expr_output_signature function that lowering validates",
        occurrence_order: "deterministic preorder per side and one-based statement: visit the query node, then relational children in constructor order, then subqueries in predicate/having scalar-expression order; node IDs are S<statement>.N<preorder> and T<statement>.N<preorder>",
        signature_identity: "signature IDs are interned by exact Rust Vec<FormalAttribute>::eq over ordered names and types; digests are not used for equality",
        comparison_policy: "comparisons pair only source and target occurrences with the same one-based statementIndex and exact rolePath; signatureEqual is exact ordered attribute equality and never semantic equivalence; mismatch.firstDifferingIndex is zero-based",
        frontier_policy: "a conservative navigation hint requires every aligned ancestor from root through the candidate to have the same operator kind and exact signature, while at least one aligned direct relational child is absent, differently shaped, or signature-incompatible; hints suggest where output layout is restored but prove nothing",
        signatures: builder.signature_pool,
        source_program,
        target_program,
        nodes: builder
            .nodes
            .into_iter()
            .map(|node| node.artifact)
            .collect(),
        comparisons,
        normalization_frontier_hints: frontier_hints,
    };
    let mut bytes = serde_json::to_vec(&artifact)?;
    bytes.push(b'\n');
    String::from_utf8(bytes).map_err(|source| {
        Error::ProofAgentCommand(format!(
            "serialized ordered-signature navigation artifact was not UTF-8: {source}"
        ))
    })
}

fn compact_tree_node(
    operator: &'static str,
    detail: String,
    children: Vec<TreeExpression>,
) -> TreeExpression {
    let node_count = 1 + children.iter().map(|child| child.node_count).sum::<usize>();
    let max_depth = 1 + children
        .iter()
        .map(|child| child.max_depth)
        .max()
        .unwrap_or(0);
    let mut expression = operator.to_owned();
    if !detail.is_empty() {
        expression.push('{');
        expression.push_str(&detail);
        expression.push('}');
    }
    if !children.is_empty() {
        expression.push('(');
        for (index, child) in children.into_iter().enumerate() {
            if index > 0 {
                expression.push(',');
            }
            expression.push_str(&child.expression);
        }
        expression.push(')');
    }
    TreeExpression {
        node_count,
        max_depth,
        expression,
    }
}

fn compact_operator_tree(tree: TreeExpression) -> CompactOperatorTree {
    CompactOperatorTree {
        node_count: tree.node_count,
        max_depth: tree.max_depth,
        expression: tree.expression,
    }
}

fn encode_tree_value(value: &str) -> String {
    const HEX: &[u8; 16] = b"0123456789ABCDEF";
    let mut encoded = String::with_capacity(value.len());
    for byte in value.bytes() {
        if byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'-' | b'.') {
            encoded.push(char::from(byte));
        } else {
            encoded.push('%');
            encoded.push(char::from(HEX[usize::from(byte >> 4)]));
            encoded.push(char::from(HEX[usize::from(byte & 0x0f)]));
        }
    }
    encoded
}

fn compact_surface_query(rel: &RelExpr) -> TreeExpression {
    match rel {
        RelExpr::Bindings {
            bindings,
            body,
            output,
        } => {
            let mut children = bindings
                .iter()
                .map(|binding| compact_surface_query(&binding.rel))
                .collect::<Vec<_>>();
            children.push(compact_surface_query(body));
            compact_tree_node(
                "bindings",
                format!("out={},defs={}", output.len(), bindings.len()),
                children,
            )
        }
        RelExpr::TableScan { table, output } => compact_tree_node(
            "table_scan",
            format!(
                "out={},table={}",
                output.len(),
                encode_tree_value(&table.join("."))
            ),
            Vec::new(),
        ),
        RelExpr::QueryRef { binding, output } => compact_tree_node(
            "query_ref",
            format!(
                "out={},binding={}",
                output.len(),
                encode_tree_value(binding)
            ),
            Vec::new(),
        ),
        RelExpr::Project {
            input,
            exprs,
            correlations,
            output,
        } => compact_tree_node(
            "project",
            format!(
                "out={},exprs={},corr={}",
                output.len(),
                exprs.len(),
                correlations.len()
            ),
            vec![compact_surface_query(input)],
        ),
        RelExpr::Filter {
            input,
            correlations,
            output,
            ..
        } => compact_tree_node(
            "filter",
            format!("out={},corr={}", output.len(), correlations.len()),
            vec![compact_surface_query(input)],
        ),
        RelExpr::NativeHaving {
            input,
            correlations,
            output,
            ..
        } => compact_tree_node(
            "native_having",
            format!("out={},corr={}", output.len(), correlations.len()),
            vec![compact_surface_query(input)],
        ),
        RelExpr::Join {
            left,
            right,
            join_type,
            correlations,
            output,
            ..
        } => compact_tree_node(
            "join",
            format!(
                "out={},kind={join_type:?},corr={}",
                output.len(),
                correlations.len()
            ),
            vec![compact_surface_query(left), compact_surface_query(right)],
        ),
        RelExpr::Aggregate {
            input,
            group_keys,
            grouping_sets,
            agg_calls,
            output,
        } => compact_tree_node(
            "aggregate",
            format!(
                "out={},keys={},sets={},aggs={}",
                output.len(),
                group_keys.len(),
                grouping_sets.len(),
                agg_calls.len()
            ),
            vec![compact_surface_query(input)],
        ),
        RelExpr::Distinct { input, output } => compact_tree_node(
            "distinct",
            format!("out={}", output.len()),
            vec![compact_surface_query(input)],
        ),
        RelExpr::Sort {
            input,
            collation,
            fetch,
            offset,
            output,
        } => compact_tree_node(
            "sort",
            format!(
                "out={},keys={},fetch={},offset={}",
                output.len(),
                collation.len(),
                fetch.is_some(),
                offset.is_some()
            ),
            vec![compact_surface_query(input)],
        ),
        RelExpr::Set {
            op,
            all,
            inputs,
            output,
        } => compact_tree_node(
            "set",
            format!("out={},op={op:?},all={all}", output.len()),
            inputs.iter().map(compact_surface_query).collect(),
        ),
        RelExpr::Values { rows, output } => compact_tree_node(
            "values",
            format!("out={},rows={}", output.len(), rows.len()),
            Vec::new(),
        ),
    }
}

fn final_output_is_canonicalized(query: &FormalQueryExpr) -> bool {
    fn select_is_canonical(select: &[FormalScalarSelectItem]) -> bool {
        !select.is_empty()
            && select
                .iter()
                .enumerate()
                .all(|(index, item)| item.alias == format!("__logos_output_{index}"))
    }

    match query {
        FormalQueryExpr::Projection { select, .. } => select_is_canonical(select),
        _ => false,
    }
}

fn emitted_rocq_symbols(query_module: &str) -> Vec<String> {
    let mut symbols = BTreeSet::new();
    for line in query_module.lines() {
        let Some(rest) = line.strip_prefix("Definition ") else {
            continue;
        };
        let name = rest
            .split(|character: char| !(character.is_ascii_alphanumeric() || character == '_'))
            .next()
            .unwrap_or_default();
        if !name.is_empty() {
            symbols.insert(name.to_owned());
        }
    }
    symbols.into_iter().collect()
}

fn build_program_shape(
    side: &str,
    exact_statements: &[&str],
    ir_queries: &[logos_ir::ir::Query],
    lowered: &LoweredProgram,
    emitted_symbols: &BTreeSet<String>,
) -> Result<Vec<QueryStatementShape>> {
    if exact_statements.len() != ir_queries.len()
        || exact_statements.len() != lowered.statements.len()
    {
        return Err(Error::ProofAgentCommand(format!(
            "cannot build {side} query context: exact SQL, typed IR, and lowered statement counts differ ({}, {}, {})",
            exact_statements.len(),
            ir_queries.len(),
            lowered.statements.len()
        )));
    }
    let singleton = exact_statements.len() == 1;
    exact_statements
        .iter()
        .zip(ir_queries)
        .zip(&lowered.statements)
        .enumerate()
        .map(|(index, ((exact_sql, ir_query), lowered_query))| {
            build_statement_shape(
                side,
                index,
                singleton,
                exact_sql,
                ir_query,
                lowered_query,
                emitted_symbols,
            )
        })
        .collect()
}

fn build_statement_shape(
    side: &str,
    index: usize,
    singleton: bool,
    exact_sql: &str,
    ir_query: &logos_ir::ir::Query,
    lowered: &LoweredQuery,
    emitted_symbols: &BTreeSet<String>,
) -> Result<QueryStatementShape> {
    let query = lowered.query_expr.as_ref().ok_or_else(|| {
        Error::ProofAgentCommand(format!(
            "cannot build {side} query context for statement {}: FormalSQL lowering is incomplete",
            index + 1
        ))
    })?;
    let output_signature = lowered.output_signature.as_deref().ok_or_else(|| {
        Error::ProofAgentCommand(format!(
            "cannot build {side} query context for statement {}: output signature is incomplete",
            index + 1
        ))
    })?;
    let frontend_sql = ir_query.source_sql.as_deref().ok_or_else(|| {
        Error::ProofAgentCommand(format!(
            "cannot build {side} query context for statement {}: typed IR has no source SQL binding",
            index + 1
        ))
    })?;
    let suffix = if singleton {
        String::new()
    } else {
        format!("_{index}")
    };
    let root_symbol = format!("{side}_query_expr{suffix}");
    let output_signature_symbol = format!("{side}_output_signature{suffix}");
    for required in [&root_symbol, &output_signature_symbol] {
        if !emitted_symbols.contains(required) {
            return Err(Error::ProofAgentCommand(format!(
                "query context drift: emitted Queries.v is missing required symbol {required}"
            )));
        }
    }
    let typed_frontend_tree = compact_operator_tree(compact_surface_query(&ir_query.rel));

    Ok(QueryStatementShape {
        statement_index: index + 1,
        exact_sql_sha256: sha256_hex(exact_sql.as_bytes()),
        frontend_sql_sha256: sha256_hex(frontend_sql.as_bytes()),
        exact_frontend_bytes_equal: exact_sql == frontend_sql,
        emitted_rocq_root_symbol: root_symbol,
        emitted_rocq_output_signature_symbol: output_signature_symbol,
        final_output_canonicalization: final_output_is_canonicalized(query),
        output_signature: compact_formal_attributes(output_signature),
        typed_frontend_tree,
    })
}

fn graph_tree_references(tree: &str) -> Vec<String> {
    tree.split(|character: char| {
        !(character.is_ascii_alphanumeric() || matches!(character, '_' | '@'))
    })
    .filter_map(|token| token.strip_prefix('@'))
    .filter(|symbol| !symbol.is_empty())
    .map(str::to_owned)
    .collect()
}

fn definition_graph_has_cycle(edges: &BTreeMap<String, Vec<String>>) -> bool {
    fn visit(
        symbol: &str,
        edges: &BTreeMap<String, Vec<String>>,
        visiting: &mut BTreeSet<String>,
        visited: &mut BTreeSet<String>,
    ) -> bool {
        if visited.contains(symbol) {
            return false;
        }
        if !visiting.insert(symbol.to_owned()) {
            return true;
        }
        if edges.get(symbol).is_some_and(|targets| {
            targets
                .iter()
                .any(|target| visit(target, edges, visiting, visited))
        }) {
            return true;
        }
        visiting.remove(symbol);
        visited.insert(symbol.to_owned());
        false
    }

    let mut visiting = BTreeSet::new();
    let mut visited = BTreeSet::new();
    edges
        .keys()
        .any(|symbol| visit(symbol, edges, &mut visiting, &mut visited))
}

fn validate_graph_statement_bindings(
    side: &str,
    bindings: &[FormalQueryStatementSymbols],
    statements: &[QueryStatementShape],
    graph_definitions: &BTreeSet<String>,
    emitted_symbols: &BTreeSet<String>,
) -> Result<()> {
    if bindings.len() != statements.len() {
        return Err(Error::ProofAgentCommand(format!(
            "query context drift: emitter graph has {} {side} statement bindings for {} lowered statements",
            bindings.len(),
            statements.len()
        )));
    }
    for (index, (binding, statement)) in bindings.iter().zip(statements).enumerate() {
        let position = index + 1;
        if binding.statement_index != position
            || statement.statement_index != position
            || binding.root_symbol != statement.emitted_rocq_root_symbol
            || binding.output_signature_symbol != statement.emitted_rocq_output_signature_symbol
        {
            return Err(Error::ProofAgentCommand(format!(
                "query context drift: emitter-owned {side} statement binding {position} disagrees with the typed lowering or emitted symbol contract"
            )));
        }
        if !graph_definitions.contains(&binding.root_symbol)
            || !emitted_symbols.contains(&binding.output_signature_symbol)
        {
            return Err(Error::ProofAgentCommand(format!(
                "query context drift: emitter-owned {side} statement binding {position} does not resolve to its generated Rocq definitions"
            )));
        }
    }
    Ok(())
}

fn validate_emitted_definition_graph(
    graph: &FormalQueryDefinitionGraph,
    source_program: &[QueryStatementShape],
    target_program: &[QueryStatementShape],
    emitted_symbols: &BTreeSet<String>,
) -> Result<()> {
    if graph.schema_version != 2 || graph.notation.trim().is_empty() {
        return Err(Error::ProofAgentCommand(
            "query context drift: emitter definition graph has an unsupported schema or empty notation"
                .to_owned(),
        ));
    }
    let mut resolvable = BTreeSet::new();
    let mut graph_definitions = BTreeSet::new();
    for helper in &graph.opaque_helper_symbols {
        if helper.is_empty()
            || !resolvable.insert(helper.clone())
            || !emitted_symbols.contains(helper)
        {
            return Err(Error::ProofAgentCommand(format!(
                "query context drift: emitter graph helper {helper:?} is duplicate, empty, or absent from Queries.v"
            )));
        }
    }
    for definition in &graph.definitions {
        if definition.symbol.is_empty()
            || definition.tree.trim().is_empty()
            || !resolvable.insert(definition.symbol.clone())
            || !graph_definitions.insert(definition.symbol.clone())
            || !emitted_symbols.contains(&definition.symbol)
        {
            return Err(Error::ProofAgentCommand(format!(
                "query context drift: emitter graph definition {:?} is duplicate, empty, or absent from Queries.v",
                definition.symbol
            )));
        }
    }
    let mut edges = BTreeMap::new();
    for definition in &graph.definitions {
        let references = graph_tree_references(&definition.tree);
        for reference in &references {
            if !resolvable.contains(reference) || !emitted_symbols.contains(reference) {
                return Err(Error::ProofAgentCommand(format!(
                    "query context drift: emitter graph definition {} has unresolved Rocq reference @{reference}",
                    definition.symbol
                )));
            }
        }
        edges.insert(
            definition.symbol.clone(),
            references
                .into_iter()
                .filter(|reference| graph_definitions.contains(reference))
                .collect(),
        );
    }
    if definition_graph_has_cycle(&edges) {
        return Err(Error::ProofAgentCommand(
            "query context drift: emitter definition graph contains a reference cycle".to_owned(),
        ));
    }
    validate_graph_statement_bindings(
        "source",
        &graph.source_statements,
        source_program,
        &graph_definitions,
        emitted_symbols,
    )?;
    validate_graph_statement_bindings(
        "target",
        &graph.target_statements,
        target_program,
        &graph_definitions,
        emitted_symbols,
    )?;
    Ok(())
}

fn build_query_shape(
    input: &VerificationInput,
    ir_input: &VerificationIr,
    lowering: &ProofLoweringReport,
    schema_module: &str,
    queries_module: &str,
) -> Result<BuiltQueryShape> {
    let emitted_rocq_symbols = emitted_rocq_symbols(queries_module);
    let emitted_symbol_set = emitted_rocq_symbols
        .iter()
        .cloned()
        .collect::<BTreeSet<_>>();
    let has_query_bindings = lowering_programs_have_query_bindings(lowering);
    let required_program_symbols = if has_query_bindings {
        ["source_bound_query_program", "target_bound_query_program"]
    } else {
        ["source_query_program", "target_query_program"]
    };
    for required in required_program_symbols.into_iter().chain([
        "source_program_output_signatures",
        "target_program_output_signatures",
    ]) {
        if !emitted_symbol_set.contains(required) {
            return Err(Error::ProofAgentCommand(format!(
                "query context drift: emitted Queries.v is missing required program symbol {required}"
            )));
        }
    }
    let emitted_query_module = lowering.query_module.as_ref().ok_or_else(|| {
        Error::ProofAgentCommand(
            "cannot build query context: FormalSQL emitter produced no query module".to_owned(),
        )
    })?;
    if emitted_query_module.rocq_module != queries_module {
        return Err(Error::ProofAgentCommand(format!(
            "query context drift: lowering query module digest {} differs from emitted Queries.v digest {}",
            sha256_hex(emitted_query_module.rocq_module.as_bytes()),
            sha256_hex(queries_module.as_bytes())
        )));
    }
    let source_exact = input.source_sql_program()?;
    let target_exact = input.target_sql_program()?;
    let source_program = build_program_shape(
        "source",
        &source_exact,
        ir_input.source_program_ir(),
        &lowering.source,
        &emitted_symbol_set,
    )?;
    let target_program = build_program_shape(
        "target",
        &target_exact,
        ir_input.target_program_ir(),
        &lowering.target,
        &emitted_symbol_set,
    )?;
    validate_emitted_definition_graph(
        &emitted_query_module.definition_graph,
        &source_program,
        &target_program,
        &emitted_symbol_set,
    )?;
    let ordered_signatures_text = build_ordered_signatures(&lowering.source, &lowering.target)?;
    let emitted_definition_graph =
        compact_definition_graph(&emitted_query_module.definition_graph)?;
    let (typed_frontend_skeleton, source_program, target_program) =
        compact_frontend_programs(&source_program, &target_program)?;
    let artifact = QueryShapeArtifact {
        schema_version: 3,
        authority: "navigation_only; exact SQL is pipeline input and Schema.v, Queries.v, Goal.v, FormalSQL, and the Rocq kernel are authoritative",
        frontend_sql_role: "Calcite-normalized source spelling attached to the typed IR; its digest and exact-byte comparison are informational, never a replacement for exact source.sql or target.sql",
        operator_tree_notation: "typed frontend and emitted-definition trees use lossless shared structural DAGs; node heads retain the previous preorder Operator{k=v,...} spelling, with nonnumeric frontend values encoded as UTF-8 bytes (%HH). Root mappings and ordered children reconstruct every previous tree byte-for-byte; DAG sharing is navigation-only and proves no equality",
        source_sql_sha256: sha256_hex(input.source_sql().as_bytes()),
        target_sql_sha256: sha256_hex(input.target_sql().as_bytes()),
        schema_module_sha256: sha256_hex(schema_module.as_bytes()),
        queries_module_sha256: sha256_hex(queries_module.as_bytes()),
        emitted_rocq_symbols,
        emitted_definition_graph,
        typed_frontend_skeleton,
        source_program,
        target_program,
    };
    let mut bytes = serde_json::to_vec(&artifact)?;
    bytes.push(b'\n');
    let text = String::from_utf8(bytes).map_err(|source| {
        Error::ProofAgentCommand(format!(
            "serialized query-shape artifact was not UTF-8: {source}"
        ))
    })?;
    Ok(BuiltQueryShape {
        text,
        ordered_signatures_text,
    })
}

fn proof_agent_instruction_body() -> String {
    FORMAL_SQL_PROOF_AGENT_PROMPT.trim_end().to_owned() + "\n"
}

fn static_prompt_and_primer_bytes() -> Result<usize> {
    Ok(proof_agent_instruction_body().len() + FORMAL_SQL_SEMANTIC_PRIMER.len())
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
        enabled: options.run_proof_agent,
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
        static_prompt_and_primer_bytes: static_prompt_and_primer_bytes()?,
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

fn write_proof_agent_context(
    artifacts: &ArtifactWriter,
    input: &VerificationInput,
    verification_mode: VerificationMode,
    query_shape: &str,
    ordered_signatures: &str,
    observation_certificates: &str,
    schema_module: &str,
    queries_module: &str,
    witness_module: &str,
    problem_module: &str,
    goal_module: &str,
) -> Result<PreparedProofAgentContext> {
    let context_root = "proof-stage/formal-sql";
    let legacy_catalog_path = artifacts.root().join(context_root).join("lemma-catalog");
    if legacy_catalog_path.exists() {
        return Err(Error::ProofAgentCommand(format!(
            "proof-agent context contains an obsolete routed lemma catalog at {}",
            legacy_catalog_path.display()
        )));
    }
    artifacts.write_text(format!("{context_root}/source.sql"), input.source_sql())?;
    artifacts.write_text(format!("{context_root}/target.sql"), input.target_sql())?;
    artifacts.write_text(format!("{context_root}/query-shape.json"), query_shape)?;
    artifacts.write_text(
        format!("{context_root}/ordered-signatures.json"),
        ordered_signatures,
    )?;
    artifacts.write_text(
        format!("{context_root}/observation-certificates.json"),
        observation_certificates,
    )?;
    artifacts.write_text(
        format!("{context_root}/semantic-primer.md"),
        FORMAL_SQL_SEMANTIC_PRIMER,
    )?;
    artifacts.write_text(
        format!("{context_root}/search-rocq-declarations.py"),
        FORMAL_SQL_DECLARATION_SEARCH_SCRIPT,
    )?;

    let static_bytes = static_prompt_and_primer_bytes()?;
    let manifest = ProofAgentContextManifest {
        schema_version: 8,
        authority: "navigation context only; exact SQL is pipeline input and generated Rocq plus FormalSQL and the Rocq kernel remain authoritative",
        verification_mode,
        static_prompt_and_primer_bytes: static_bytes,
        source_sql: context_binding("source.sql", input.source_sql().as_bytes()),
        target_sql: context_binding("target.sql", input.target_sql().as_bytes()),
        query_shape: context_binding("query-shape.json", query_shape.as_bytes()),
        ordered_signatures: context_binding(
            "ordered-signatures.json",
            ordered_signatures.as_bytes(),
        ),
        observation_certificates: context_binding(
            "observation-certificates.json",
            observation_certificates.as_bytes(),
        ),
        semantic_primer: context_binding(
            "semantic-primer.md",
            FORMAL_SQL_SEMANTIC_PRIMER.as_bytes(),
        ),
        declaration_search: context_binding(
            "search-rocq-declarations.py",
            FORMAL_SQL_DECLARATION_SEARCH_SCRIPT.as_bytes(),
        ),
        schema_module: context_binding("Schema.v", schema_module.as_bytes()),
        queries_module: context_binding("Queries.v", queries_module.as_bytes()),
        witness_module: context_binding("Witness.v", witness_module.as_bytes()),
        goal_module: context_binding("Goal.v", goal_module.as_bytes()),
    };
    let manifest_text = serde_json::to_string_pretty(&manifest)? + "\n";
    artifacts.write_text(
        format!("{context_root}/context-manifest.json"),
        &manifest_text,
    )?;
    let generated_context_bytes = manifest.source_sql.bytes
        + manifest.target_sql.bytes
        + manifest.query_shape.bytes
        + manifest.ordered_signatures.bytes
        + manifest.observation_certificates.bytes
        + manifest.semantic_primer.bytes
        + manifest.declaration_search.bytes
        + manifest.schema_module.bytes
        + manifest.queries_module.bytes
        + manifest.witness_module.bytes
        + problem_module.len()
        + manifest.goal_module.bytes
        + manifest_text.len()
        // The primer is already counted through its context file above.
        + proof_agent_instruction_body().len();
    let report = ProofAgentContext {
        manifest_path: format!("{context_root}/context-manifest.json"),
        manifest_sha256: sha256_hex(manifest_text.as_bytes()),
        manifest_bytes: manifest_text.len(),
        source_sql_sha256: manifest.source_sql.sha256.clone(),
        source_sql_bytes: manifest.source_sql.bytes,
        target_sql_sha256: manifest.target_sql.sha256.clone(),
        target_sql_bytes: manifest.target_sql.bytes,
        query_shape_sha256: manifest.query_shape.sha256.clone(),
        query_shape_bytes: manifest.query_shape.bytes,
        ordered_signatures_sha256: manifest.ordered_signatures.sha256.clone(),
        ordered_signatures_bytes: manifest.ordered_signatures.bytes,
        observation_certificates_sha256: manifest.observation_certificates.sha256.clone(),
        observation_certificates_bytes: manifest.observation_certificates.bytes,
        schema_module_sha256: manifest.schema_module.sha256.clone(),
        schema_module_bytes: manifest.schema_module.bytes,
        queries_module_sha256: manifest.queries_module.sha256.clone(),
        queries_module_bytes: manifest.queries_module.bytes,
        witness_module_sha256: manifest.witness_module.sha256.clone(),
        witness_module_bytes: manifest.witness_module.bytes,
        problem_module_bytes: problem_module.len(),
        goal_module_bytes: manifest.goal_module.bytes,
        semantic_primer_bytes: manifest.semantic_primer.bytes,
        declaration_search_sha256: manifest.declaration_search.sha256.clone(),
        declaration_search_bytes: manifest.declaration_search.bytes,
        generated_context_bytes,
    };
    let prepared = PreparedProofAgentContext {
        manifest,
        manifest_text,
        report,
    };
    validate_proof_agent_context(artifacts, &prepared)?;
    Ok(prepared)
}
fn validate_context_binding(root: &Path, binding: &ContextFileBinding) -> Result<()> {
    let path = root.join(&binding.path);
    let metadata = std::fs::symlink_metadata(&path).map_err(|source| Error::Read {
        path: path.clone(),
        source,
    })?;
    if !metadata.file_type().is_file() {
        return Err(Error::ProofAgentCommand(format!(
            "proof-agent context drift: {} is not a regular file",
            path.display()
        )));
    }
    let bytes = std::fs::read(&path).map_err(|source| Error::Read {
        path: path.clone(),
        source,
    })?;
    let observed_digest = sha256_hex(&bytes);
    if bytes.len() != binding.bytes || observed_digest != binding.sha256 {
        return Err(Error::ProofAgentCommand(format!(
            "proof-agent context drift: {} expected {} bytes with SHA-256 {}, observed {} bytes with SHA-256 {}",
            path.display(),
            binding.bytes,
            binding.sha256,
            bytes.len(),
            observed_digest
        )));
    }
    Ok(())
}

fn validate_proof_agent_context(
    artifacts: &ArtifactWriter,
    prepared: &PreparedProofAgentContext,
) -> Result<()> {
    let root = artifacts.root().join("proof-stage/formal-sql");
    for binding in [
        &prepared.manifest.source_sql,
        &prepared.manifest.target_sql,
        &prepared.manifest.query_shape,
        &prepared.manifest.ordered_signatures,
        &prepared.manifest.observation_certificates,
        &prepared.manifest.semantic_primer,
        &prepared.manifest.declaration_search,
        &prepared.manifest.schema_module,
        &prepared.manifest.queries_module,
        &prepared.manifest.witness_module,
        &prepared.manifest.goal_module,
    ] {
        validate_context_binding(&root, binding)?;
    }
    let manifest_path = root.join("context-manifest.json");
    let manifest_text = std::fs::read_to_string(&manifest_path).map_err(|source| Error::Read {
        path: manifest_path.clone(),
        source,
    })?;
    if manifest_text != prepared.manifest_text {
        return Err(Error::ProofAgentCommand(format!(
            "proof-agent context drift: {} differs from the host-generated manifest",
            manifest_path.display()
        )));
    }

    let legacy_catalog_path = root.join("lemma-catalog");
    if legacy_catalog_path.exists() {
        return Err(Error::ProofAgentCommand(format!(
            "proof-agent context unexpectedly contains obsolete routed lemma catalog {}",
            legacy_catalog_path.display()
        )));
    }
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
    let schema_ir_path = artifacts.root().join("input/schema-ir.json");
    let source_ir_path = artifacts.root().join("input/source-ir.json");
    let target_ir_path = artifacts.root().join("input/target-ir.json");
    artifacts.write_json("input/sql-environment.json", &ir_input.sql_environment())?;
    artifacts.write_json("input/schema-ir.json", ir_input.schema_ir())?;
    artifacts.write_json("input/source-ir.json", &ir_input.source_program_ir())?;
    artifacts.write_json("input/target-ir.json", &ir_input.target_program_ir())?;

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
        schema_ir_sha256: sha256_file_hex(&schema_ir_path)?,
        source_ir_sha256: sha256_file_hex(&source_ir_path)?,
        target_ir_sha256: sha256_file_hex(&target_ir_path)?,
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
    PreparedProofAgentContext,
    TrustedProofSources,
    TrustedCheckInvocation,
    ProblemCompileCheckpoint,
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
    artifacts.write_text("proof-stage/formal-sql/Schema.v", &schema.rocq_module)?;
    artifacts.write_text(
        "proof-stage/formal-sql/Queries.v",
        &query_module.rocq_module,
    )?;
    artifacts.write_text(
        "proof-stage/formal-sql/Problem.v",
        &proof_module.rocq_module,
    )?;
    write_formal_sql_witness_modules(artifacts, &witness_modules)?;
    let (workspace, context) = write_proof_workspace(
        artifacts,
        input,
        ir_input,
        lowering_report,
        observation_certificates,
        &schema.rocq_module,
        &query_module.rocq_module,
        &witness_modules.witness,
        &proof_module.rocq_module,
        &goal_module.rocq_module,
        options,
    )?;
    validate_proof_agent_context(artifacts, &context)?;
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
) -> Result<ProofStageResult> {
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
            artifacts.write_text("proof-stage/formal-sql/Schema.v", &schema.rocq_module)?;
            artifacts.write_text(
                "proof-stage/formal-sql/Queries.v",
                &query_module.rocq_module,
            )?;
            artifacts.write_text(
                "proof-stage/formal-sql/Problem.v",
                &proof_module.rocq_module,
            )?;
            write_formal_sql_witness_modules(artifacts, &witness_modules)?;
            let (workspace, context) = write_proof_workspace(
                artifacts,
                input,
                &ir_input,
                &lowering_report,
                &observation_certificates,
                &schema.rocq_module,
                &query_module.rocq_module,
                &witness_modules.witness,
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
    let mut trusted_sources = if options.run_proof_agent && proof_workspace.is_some() {
        Some(capture_trusted_proof_sources(artifacts)?)
    } else {
        None
    };
    let mut proof_workspace_generation = 1usize;
    let mut initial_problem_compile_checkpoint = None;
    if trusted_sources.is_some() {
        validate_proof_agent_context(
            artifacts,
            proof_agent_context
                .as_ref()
                .expect("a trusted proof workspace always has proof-agent context"),
        )?;
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

            if round_success {
                break;
            }

            // A typed fixed witness deliberately creates a fresh generation
            // and therefore does not need the failed Codex session. Resolve
            // the materialized handoff before deciding whether missing resume
            // telemetry is fatal.
            if let Some(handoff) = handoff {
                match handoff_handler.as_deref_mut() {
                    Some(handler) => match handler(&handoff)? {
                        ProofHandoffResolution::Continue(feedback) => {
                            repair_feedback = Some(format!(
                                "The counterexample handoff from proof round {round} was not validated. Resume the proof and account for this feedback:\n{feedback}"
                            ));
                        }
                        ProofHandoffResolution::NeedsManualReview(reason) => {
                            proof_manual_review_reason = Some(reason);
                            break;
                        }
                        ProofHandoffResolution::RestartWithFormalWitness { feedback, snapshot } => {
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
                            let triggering_handoff_sha256 = canonical_json_sha256(&handoff)?;
                            let from_trusted_diagnostic_cache = archive_trusted_diagnostic_cache(
                                artifacts,
                                from_workspace_generation,
                            )?;
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
                            let checkpoint_evidence =
                                restarted_checkpoint.report_evidence(artifacts)?;
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
                            proof_agent_configuration.context =
                                Some(restarted_context.report.clone());
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
                            next_checkpoint_transition =
                                ProofCheckpointTransition::NewWorkspaceInitial;
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
                    },
                    None => {
                        repair_feedback = Some(
                            "The proof agent requested counterexample investigation, but counterexample search is disabled. Continue proof analysis; do not treat the unvalidated suspicion as a result."
                                .to_owned(),
                        );
                    }
                }
            }

            if !session_resumable {
                proof_resume_unavailable = true;
                break;
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
            "FormalSQL/Rocq proof search stopped without accepting an EQ or NEQ certificate after proof-directed counterexample synthesis requested manual review: {}",
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
    Ok(ProofStageResult::Finished(Box::new(report)))
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

fn diagnostic_evidence_error(message: impl Into<String>) -> Error {
    Error::ProofAgentCommand(format!(
        "diagnostic broker evidence integrity failure: {}",
        message.into()
    ))
}

fn diagnostic_artifact_relative_path(artifacts_root: &Path, path: &Path) -> Result<String> {
    let relative = path.strip_prefix(artifacts_root).map_err(|_| {
        diagnostic_evidence_error(format!(
            "{} escapes artifact root {}",
            path.display(),
            artifacts_root.display()
        ))
    })?;
    if relative.as_os_str().is_empty()
        || relative
            .components()
            .any(|component| !matches!(component, std::path::Component::Normal(_)))
    {
        return Err(diagnostic_evidence_error(format!(
            "{} is not a normalized artifact-relative path",
            relative.display()
        )));
    }
    relative
        .to_str()
        .map(str::to_owned)
        .ok_or_else(|| diagnostic_evidence_error("diagnostic artifact path is not UTF-8"))
}

fn diagnostic_artifact_binding(
    artifacts_root: &Path,
    path: &Path,
) -> Result<DiagnosticArtifactBinding> {
    let relative = diagnostic_artifact_relative_path(artifacts_root, path)?;
    let metadata = std::fs::symlink_metadata(path).map_err(|source| {
        diagnostic_evidence_error(format!("cannot stat {}: {source}", path.display()))
    })?;
    if !metadata.file_type().is_file() || metadata.file_type().is_symlink() {
        return Err(diagnostic_evidence_error(format!(
            "{} is not a regular non-symlink file",
            path.display()
        )));
    }
    let canonical_root = std::fs::canonicalize(artifacts_root).map_err(|source| {
        diagnostic_evidence_error(format!(
            "cannot canonicalize artifact root {}: {source}",
            artifacts_root.display()
        ))
    })?;
    let canonical_path = std::fs::canonicalize(path).map_err(|source| {
        diagnostic_evidence_error(format!("cannot canonicalize {}: {source}", path.display()))
    })?;
    if !canonical_path.starts_with(&canonical_root) {
        return Err(diagnostic_evidence_error(format!(
            "{} resolves outside artifact root {}",
            path.display(),
            artifacts_root.display()
        )));
    }
    let bytes = std::fs::read(path).map_err(|source| {
        diagnostic_evidence_error(format!("cannot read {}: {source}", path.display()))
    })?;
    Ok(DiagnosticArtifactBinding {
        path: relative,
        sha256: sha256_hex(&bytes),
        bytes: bytes.len(),
    })
}

fn read_bound_diagnostic_artifact(
    artifacts_root: &Path,
    binding: &DiagnosticArtifactBinding,
) -> Result<Vec<u8>> {
    let relative = Path::new(&binding.path);
    if relative.is_absolute()
        || relative.as_os_str().is_empty()
        || relative
            .components()
            .any(|component| !matches!(component, std::path::Component::Normal(_)))
    {
        return Err(diagnostic_evidence_error(format!(
            "reported path {:?} is not artifact-relative",
            binding.path
        )));
    }
    let path = artifacts_root.join(relative);
    let observed = diagnostic_artifact_binding(artifacts_root, &path)?;
    if observed != *binding {
        return Err(diagnostic_evidence_error(format!(
            "binding for {} drifted: expected {} bytes/{}, observed {} bytes/{}",
            binding.path, binding.bytes, binding.sha256, observed.bytes, observed.sha256
        )));
    }
    std::fs::read(&path).map_err(|source| {
        diagnostic_evidence_error(format!("cannot read bound {}: {source}", path.display()))
    })
}

fn validate_scratch_relative_path(path: &Path) -> std::result::Result<(), String> {
    if path.is_absolute() || path.as_os_str().is_empty() {
        return Err("scratch path must be a nonempty relative path".to_owned());
    }
    let components = path.components().collect::<Vec<_>>();
    if components
        .iter()
        .any(|component| !matches!(component, std::path::Component::Normal(_)))
    {
        return Err("scratch path must contain only normalized components".to_owned());
    }
    let text = path
        .to_str()
        .ok_or_else(|| "scratch path must be UTF-8".to_owned())?;
    if text.contains('\\') || text.chars().any(char::is_control) {
        return Err("scratch path contains unsupported characters".to_owned());
    }
    Ok(())
}

fn validate_scratch_child_path(path: &Path) -> std::result::Result<(), String> {
    validate_scratch_relative_path(path)?;
    let extension = path
        .extension()
        .and_then(|extension| extension.to_str())
        .ok_or_else(|| "scratch file must have an allowed extension".to_owned())?;
    if !SCRATCH_ALLOWED_EXTENSIONS.contains(&extension) {
        return Err(format!(
            "scratch files must use one of the extensions {:?}",
            SCRATCH_ALLOWED_EXTENSIONS
        ));
    }
    Ok(())
}

fn open_directory_nofollow(path: &Path) -> Result<File> {
    let file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC)
        .open(path)
        .map_err(|source| Error::Read {
            path: path.to_owned(),
            source,
        })?;
    let metadata = file.metadata().map_err(|source| Error::Read {
        path: path.to_owned(),
        source,
    })?;
    if !metadata.file_type().is_dir() {
        return Err(Error::ProofAgentCommand(format!(
            "{} must be a regular non-symlink directory",
            path.display()
        )));
    }
    Ok(file)
}

fn openat_nofollow(
    parent: &File,
    component: &OsStr,
    display_path: &Path,
    directory: bool,
) -> Result<File> {
    let component = CString::new(component.as_bytes()).map_err(|_| {
        Error::ProofAgentCommand(format!(
            "path component in {} contains a NUL byte",
            display_path.display()
        ))
    })?;
    let type_flags = if directory {
        libc::O_DIRECTORY
    } else {
        // Opening a FIFO nonblocking prevents an attacker-controlled entry from
        // stalling the broker before fstat rejects it as non-regular.
        libc::O_NONBLOCK
    };
    // SAFETY: parent is a live owned directory descriptor, component is a
    // NUL-terminated single normalized component, and a successful descriptor
    // is transferred exactly once into File below.
    let descriptor = unsafe {
        libc::openat(
            parent.as_raw_fd(),
            component.as_ptr(),
            libc::O_RDONLY | libc::O_CLOEXEC | libc::O_NOFOLLOW | type_flags,
        )
    };
    if descriptor < 0 {
        return Err(Error::Read {
            path: display_path.to_owned(),
            source: std::io::Error::last_os_error(),
        });
    }
    // SAFETY: openat returned a fresh descriptor owned by this call, and no
    // other File is constructed from it.
    Ok(unsafe { File::from_raw_fd(descriptor) })
}

fn read_regular_file_beneath(root: &File, root_path: &Path, relative: &Path) -> Result<Vec<u8>> {
    if relative.is_absolute() || relative.as_os_str().is_empty() {
        return Err(Error::ProofAgentCommand(format!(
            "candidate path {} must be a nonempty relative path",
            relative.display()
        )));
    }
    let components = relative.components().collect::<Vec<_>>();
    if components
        .iter()
        .any(|component| !matches!(component, std::path::Component::Normal(_)))
    {
        return Err(Error::ProofAgentCommand(format!(
            "candidate path {} is not normalized",
            relative.display()
        )));
    }
    let mut directory = root.try_clone().map_err(|source| Error::Read {
        path: root_path.to_owned(),
        source,
    })?;
    let mut display_path = root_path.to_owned();
    for component in &components[..components.len() - 1] {
        let std::path::Component::Normal(component) = component else {
            unreachable!("candidate components were validated above")
        };
        display_path.push(component);
        directory = openat_nofollow(&directory, component, &display_path, true)?;
    }
    let std::path::Component::Normal(file_name) = components[components.len() - 1] else {
        unreachable!("candidate components were validated above")
    };
    display_path.push(file_name);
    let mut file = openat_nofollow(&directory, file_name, &display_path, false)?;
    let metadata = file.metadata().map_err(|source| Error::Read {
        path: display_path.clone(),
        source,
    })?;
    if !metadata.file_type().is_file() {
        return Err(Error::ProofAgentCommand(format!(
            "{} is not a regular non-symlink file",
            display_path.display()
        )));
    }
    let mut bytes = Vec::new();
    file.read_to_end(&mut bytes).map_err(|source| Error::Read {
        path: display_path.clone(),
        source,
    })?;
    Ok(bytes)
}

fn validate_diagnostic_candidate_path(
    mode: DiagnosticCandidateMode,
    candidate_path: &str,
) -> std::result::Result<PathBuf, String> {
    match mode {
        DiagnosticCandidateMode::Problem if candidate_path == "Problem.v" => {
            Ok(PathBuf::from(candidate_path))
        }
        DiagnosticCandidateMode::Problem => {
            Err("problem diagnostics require candidatePath Problem.v".to_owned())
        }
        DiagnosticCandidateMode::Module => validate_proof_module_candidate_path(candidate_path),
        DiagnosticCandidateMode::Scratch => {
            let path = Path::new(candidate_path);
            let mut components = path.components();
            if components.next()
                != Some(std::path::Component::Normal(std::ffi::OsStr::new(
                    "scratch",
                )))
            {
                return Err("scratch diagnostics require candidatePath scratch/*.v".to_owned());
            }
            let child = components.collect::<PathBuf>();
            validate_scratch_child_path(&child)?;
            if is_checked_scratch_snapshot(&child) {
                return Err(
                    "scratch diagnostics cannot target the reserved scratch/checked/ namespace"
                        .to_owned(),
                );
            }
            if child.extension().and_then(|extension| extension.to_str()) != Some("v") {
                return Err("scratch diagnostics require a .v candidate".to_owned());
            }
            let normalized = Path::new("scratch").join(&child);
            if normalized.to_str() != Some(candidate_path) {
                return Err("candidatePath must be normalized".to_owned());
            }
            Ok(normalized)
        }
    }
}

fn valid_proof_module_stem(stem: &str) -> bool {
    let mut characters = stem.chars();
    matches!(characters.next(), Some(first) if first.is_ascii_uppercase())
        && characters.all(|character| character.is_ascii_alphanumeric() || character == '_')
}

fn validate_proof_module_candidate_path(
    candidate_path: &str,
) -> std::result::Result<PathBuf, String> {
    let path = Path::new(candidate_path);
    let mut components = path.components();
    if components.next()
        != Some(std::path::Component::Normal(std::ffi::OsStr::new(
            PROOF_MODULE_DIRECTORY,
        )))
    {
        return Err(format!(
            "module diagnostics require candidatePath {PROOF_MODULE_DIRECTORY}/<UppercaseRocqIdentifier>.v"
        ));
    }
    let Some(std::path::Component::Normal(file_name)) = components.next() else {
        return Err("module candidate is missing its file name".to_owned());
    };
    if components.next().is_some() {
        return Err("proof modules must be direct children of ProofModules/".to_owned());
    }
    let file_name = file_name
        .to_str()
        .ok_or_else(|| "proof module file name must be UTF-8".to_owned())?;
    let stem = file_name
        .strip_suffix(".v")
        .ok_or_else(|| "proof module candidate must have a .v extension".to_owned())?;
    if !valid_proof_module_stem(stem) {
        return Err(
            "proof module file stem must be an uppercase Rocq identifier containing only ASCII letters, digits, and underscores"
                .to_owned(),
        );
    }
    let normalized = Path::new(PROOF_MODULE_DIRECTORY).join(file_name);
    if normalized.to_str() != Some(candidate_path) {
        return Err("candidatePath must be normalized".to_owned());
    }
    Ok(normalized)
}

fn validated_scratch_tree_with_policy(
    root: &Path,
    unsupported_file_policy: UnsupportedScratchFilePolicy,
) -> Result<ValidatedScratchTree> {
    let metadata = match std::fs::symlink_metadata(root) {
        Ok(metadata) => metadata,
        Err(source) if source.kind() == std::io::ErrorKind::NotFound => {
            return Ok(ValidatedScratchTree::default());
        }
        Err(source) => {
            return Err(Error::Read {
                path: root.to_owned(),
                source,
            });
        }
    };
    if !metadata.file_type().is_dir() || metadata.file_type().is_symlink() {
        return Err(Error::ProofAgentCommand(format!(
            "scratch root {} must be a regular non-symlink directory",
            root.display()
        )));
    }

    let root_descriptor = open_directory_nofollow(root)?;
    let mut pending_directories = vec![(root.to_owned(), PathBuf::new())];
    let mut directory_paths = BTreeSet::from([PathBuf::new()]);
    let mut snapshots = Vec::new();
    let mut dropped_unsupported_files = Vec::new();
    while let Some((directory, directory_relative)) = pending_directories.pop() {
        let entries = std::fs::read_dir(&directory).map_err(|source| Error::Read {
            path: directory.clone(),
            source,
        })?;
        for entry in entries {
            let entry = entry.map_err(|source| Error::Read {
                path: directory.clone(),
                source,
            })?;
            let path = entry.path();
            let relative = if directory_relative.as_os_str().is_empty() {
                PathBuf::from(entry.file_name())
            } else {
                directory_relative.join(entry.file_name())
            };
            let metadata = std::fs::symlink_metadata(&path).map_err(|source| Error::Read {
                path: path.clone(),
                source,
            })?;
            if metadata.file_type().is_symlink() {
                return Err(Error::ProofAgentCommand(format!(
                    "scratch tree contains a symlink: {}",
                    path.display()
                )));
            }
            if metadata.file_type().is_dir() {
                validate_scratch_relative_path(&relative).map_err(Error::ProofAgentCommand)?;
                directory_paths.insert(relative.clone());
                pending_directories.push((path, relative));
                continue;
            }
            if !metadata.file_type().is_file() {
                return Err(Error::ProofAgentCommand(format!(
                    "scratch tree contains a non-regular entry: {}",
                    path.display()
                )));
            }
            validate_scratch_relative_path(&relative).map_err(|reason| {
                Error::ProofAgentCommand(format!(
                    "scratch file {} has an invalid path: {reason}",
                    relative.display()
                ))
            })?;
            if let Err(reason) = validate_scratch_child_path(&relative) {
                match unsupported_file_policy {
                    UnsupportedScratchFilePolicy::Reject => {
                        return Err(Error::ProofAgentCommand(format!(
                            "scratch file {} is not persistable: {reason}",
                            relative.display()
                        )));
                    }
                    UnsupportedScratchFilePolicy::Drop => {
                        dropped_unsupported_files.push(relative);
                        continue;
                    }
                }
            }
            let bytes = read_regular_file_beneath(&root_descriptor, root, &relative)?;
            std::str::from_utf8(&bytes).map_err(|source| {
                Error::ProofAgentCommand(format!(
                    "scratch file {} is not UTF-8: {source}",
                    path.display()
                ))
            })?;
            snapshots.push(ScratchFileSnapshot {
                relative_path: relative,
                bytes,
            });
        }
    }
    snapshots.sort_by(|left, right| left.relative_path.cmp(&right.relative_path));
    dropped_unsupported_files.sort();
    Ok(ValidatedScratchTree {
        files: snapshots,
        directories: directory_paths,
        dropped_unsupported_files,
    })
}

fn validated_scratch_tree(root: &Path) -> Result<ValidatedScratchTree> {
    validated_scratch_tree_with_policy(root, UnsupportedScratchFilePolicy::Reject)
}

fn validated_scratch_files(root: &Path) -> Result<Vec<ScratchFileSnapshot>> {
    Ok(validated_scratch_tree(root)?.files)
}

fn validated_staged_scratch_files(root: &Path) -> Result<Vec<ScratchFileSnapshot>> {
    let tree = validated_scratch_tree_with_policy(root, UnsupportedScratchFilePolicy::Drop)?;
    for relative in &tree.dropped_unsupported_files {
        eprintln!(
            "warning: dropping scratch/{} at the proof-agent round boundary because its extension is not persistable; only {:?} are retained between rounds",
            relative.display(),
            SCRATCH_ALLOWED_EXTENSIONS
        );
    }
    Ok(tree.files)
}

fn scratch_workspace_state(root: &Path) -> Result<ScratchWorkspaceState> {
    let files = validated_scratch_tree(root)?.files;
    Ok(ScratchWorkspaceState {
        file_count: files.len(),
        total_bytes: files.iter().map(|file| file.bytes.len()).sum(),
    })
}

fn ensure_scratch_directory(path: &Path) -> Result<()> {
    match std::fs::symlink_metadata(path) {
        Ok(metadata) if metadata.file_type().is_dir() && !metadata.file_type().is_symlink() => {}
        Ok(_) => {
            return Err(Error::ProofAgentCommand(format!(
                "scratch directory component {} is not a regular directory",
                path.display()
            )));
        }
        Err(source) if source.kind() == std::io::ErrorKind::NotFound => {
            std::fs::create_dir(path).map_err(|source| Error::CreateDir {
                path: path.to_owned(),
                source,
            })?;
            std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o700)).map_err(
                |source| {
                    Error::ProofAgentCommand(format!(
                        "failed to secure scratch directory {}: {source}",
                        path.display()
                    ))
                },
            )?;
        }
        Err(source) => {
            return Err(Error::Read {
                path: path.to_owned(),
                source,
            });
        }
    }
    Ok(())
}

fn validate_projected_scratch_directories<'a>(
    existing: &BTreeSet<PathBuf>,
    file_paths: impl IntoIterator<Item = &'a Path>,
) -> Result<()> {
    projected_scratch_directories(existing, file_paths).map(|_| ())
}

fn projected_scratch_directories<'a>(
    existing: &BTreeSet<PathBuf>,
    file_paths: impl IntoIterator<Item = &'a Path>,
) -> Result<BTreeSet<PathBuf>> {
    let mut projected = existing.clone();
    // All merge and promotion paths materialize the scratch root, including an
    // otherwise empty workspace, so count it before any filesystem mutation.
    projected.insert(PathBuf::new());
    for file_path in file_paths {
        validate_scratch_child_path(file_path).map_err(Error::ProofAgentCommand)?;
        let mut relative_parent = PathBuf::new();
        if let Some(parent) = file_path.parent() {
            for component in parent.components() {
                let std::path::Component::Normal(component) = component else {
                    return Err(Error::ProofAgentCommand(
                        "scratch snapshot parent is not normalized".to_owned(),
                    ));
                };
                relative_parent.push(component);
                projected.insert(relative_parent.clone());
            }
        }
    }
    Ok(projected)
}

fn write_scratch_snapshot(root: &Path, snapshot: &ScratchFileSnapshot) -> Result<()> {
    validate_scratch_child_path(&snapshot.relative_path).map_err(Error::ProofAgentCommand)?;
    ensure_scratch_directory(root)?;
    let mut parent = root.to_owned();
    if let Some(relative_parent) = snapshot.relative_path.parent() {
        for component in relative_parent.components() {
            let std::path::Component::Normal(component) = component else {
                return Err(Error::ProofAgentCommand(
                    "scratch snapshot parent is not normalized".to_owned(),
                ));
            };
            parent.push(component);
            ensure_scratch_directory(&parent)?;
        }
    }
    let destination = root.join(&snapshot.relative_path);
    if let Ok(metadata) = std::fs::symlink_metadata(&destination)
        && (!metadata.file_type().is_file() || metadata.file_type().is_symlink())
    {
        return Err(Error::ProofAgentCommand(format!(
            "scratch destination {} is not a regular non-symlink file",
            destination.display()
        )));
    }
    let temporary = parent.join(format!(
        ".scratch-write-{}-{}",
        std::process::id(),
        now_ms_since_epoch()
    ));
    let result = (|| {
        std::fs::write(&temporary, &snapshot.bytes).map_err(|source| Error::Write {
            path: temporary.clone(),
            source,
        })?;
        std::fs::set_permissions(&temporary, std::fs::Permissions::from_mode(0o600)).map_err(
            |source| Error::Write {
                path: temporary.clone(),
                source,
            },
        )?;
        std::fs::rename(&temporary, &destination).map_err(|source| Error::Write {
            path: destination.clone(),
            source,
        })?;
        Ok(())
    })();
    if result.is_err() {
        let _ = std::fs::remove_file(&temporary);
    }
    result
}

fn merge_scratch_snapshots(
    root: &Path,
    additions: Vec<ScratchFileSnapshot>,
) -> Result<ScratchWorkspaceState> {
    let existing_tree = validated_scratch_tree(root)?;
    let existing = existing_tree
        .files
        .into_iter()
        .map(|snapshot| (snapshot.relative_path.clone(), snapshot))
        .collect::<BTreeMap<_, _>>();
    let mut merged = existing
        .values()
        .cloned()
        .map(|snapshot| (snapshot.relative_path.clone(), snapshot))
        .collect::<BTreeMap<_, _>>();
    for snapshot in additions {
        validate_scratch_child_path(&snapshot.relative_path).map_err(Error::ProofAgentCommand)?;
        std::str::from_utf8(&snapshot.bytes).map_err(|source| {
            Error::ProofAgentCommand(format!(
                "scratch file {} is not UTF-8: {source}",
                snapshot.relative_path.display()
            ))
        })?;
        merged.insert(snapshot.relative_path.clone(), snapshot);
    }
    validate_projected_scratch_directories(
        &existing_tree.directories,
        merged.keys().map(PathBuf::as_path),
    )?;
    let changed = merged.values().filter(|snapshot| {
        existing
            .get(&snapshot.relative_path)
            .is_none_or(|prior| prior.bytes != snapshot.bytes)
    });
    ensure_scratch_directory(root)?;
    for snapshot in changed {
        write_scratch_snapshot(root, snapshot)?;
    }
    scratch_workspace_state(root)
}

fn scratch_snapshot_state(
    snapshots: &BTreeMap<PathBuf, ScratchFileSnapshot>,
) -> Result<ScratchWorkspaceState> {
    let total_bytes = snapshots
        .values()
        .try_fold(0usize, |total, snapshot| {
            total.checked_add(snapshot.bytes.len())
        })
        .ok_or_else(|| Error::ProofAgentCommand("scratch byte total overflowed".to_owned()))?;
    Ok(ScratchWorkspaceState {
        file_count: snapshots.len(),
        total_bytes,
    })
}

fn scratch_snapshot_layout(
    snapshots: &BTreeMap<PathBuf, ScratchFileSnapshot>,
) -> Result<(ScratchWorkspaceState, BTreeSet<PathBuf>)> {
    let state = scratch_snapshot_state(snapshots)?;
    let directories =
        projected_scratch_directories(&BTreeSet::new(), snapshots.keys().map(PathBuf::as_path))?;
    Ok((state, directories))
}

fn is_exact_checked_duplicate(
    snapshot: &ScratchFileSnapshot,
    checked: &BTreeMap<PathBuf, ScratchFileSnapshot>,
) -> bool {
    !is_checked_scratch_snapshot(&snapshot.relative_path)
        && checked
            .get(&checked_scratch_relative_path(
                &snapshot.relative_path,
                &snapshot.bytes,
            ))
            .is_some_and(|checked_snapshot| checked_snapshot.bytes == snapshot.bytes)
}

fn select_scratch_snapshots(
    mut checked: BTreeMap<PathBuf, ScratchFileSnapshot>,
    untrusted: Vec<ScratchFileSnapshot>,
) -> BTreeMap<PathBuf, ScratchFileSnapshot> {
    for snapshot in untrusted {
        if !is_checked_scratch_snapshot(&snapshot.relative_path)
            && !is_exact_checked_duplicate(&snapshot, &checked)
        {
            checked.insert(snapshot.relative_path.clone(), snapshot);
        }
    }
    checked
}

const SCRATCH_TRANSACTION_PREFIX: &str = ".scratch-transaction-";

fn remove_stale_scratch_transactions(parent: &Path) -> Result<()> {
    let entries = std::fs::read_dir(parent).map_err(|source| Error::Read {
        path: parent.to_owned(),
        source,
    })?;
    for entry in entries {
        let entry = entry.map_err(|source| Error::Read {
            path: parent.to_owned(),
            source,
        })?;
        let name = entry.file_name();
        let Some(name) = name.to_str() else {
            continue;
        };
        if !name.starts_with(SCRATCH_TRANSACTION_PREFIX) {
            continue;
        }
        let path = entry.path();
        let metadata = std::fs::symlink_metadata(&path).map_err(|source| Error::Read {
            path: path.clone(),
            source,
        })?;
        if metadata.file_type().is_symlink() || !metadata.file_type().is_dir() {
            return Err(Error::ProofAgentCommand(format!(
                "stale scratch transaction {} is not a real directory",
                path.display()
            )));
        }
        std::fs::remove_dir_all(&path).map_err(|source| Error::Write { path, source })?;
    }
    Ok(())
}

fn atomic_exchange_scratch_directories(returned: &Path, live: &Path) -> Result<()> {
    for path in [returned, live] {
        let metadata = std::fs::symlink_metadata(path).map_err(|source| Error::Read {
            path: path.to_owned(),
            source,
        })?;
        if metadata.file_type().is_symlink() || !metadata.file_type().is_dir() {
            return Err(Error::ProofAgentCommand(format!(
                "scratch transaction path {} is not a real directory",
                path.display()
            )));
        }
    }
    let returned_c = CString::new(returned.as_os_str().as_bytes()).map_err(|_| {
        Error::ProofAgentCommand("scratch transaction path contains a NUL byte".to_owned())
    })?;
    let live_c = CString::new(live.as_os_str().as_bytes()).map_err(|_| {
        Error::ProofAgentCommand("live scratch path contains a NUL byte".to_owned())
    })?;
    // SAFETY: both C strings are NUL-terminated paths to host-validated real
    // directories. RENAME_EXCHANGE changes the two directory entries in one
    // atomic namespace operation and does not retain either pointer.
    let status = unsafe {
        libc::syscall(
            libc::SYS_renameat2,
            libc::AT_FDCWD,
            returned_c.as_ptr(),
            libc::AT_FDCWD,
            live_c.as_ptr(),
            libc::RENAME_EXCHANGE,
        )
    };
    if status != 0 {
        return Err(Error::Write {
            path: live.to_owned(),
            source: std::io::Error::last_os_error(),
        });
    }
    let mut parents = BTreeSet::new();
    if let Some(parent) = returned.parent() {
        parents.insert(parent.to_owned());
    }
    if let Some(parent) = live.parent() {
        parents.insert(parent.to_owned());
    }
    for parent in parents {
        File::open(&parent)
            .and_then(|directory| directory.sync_all())
            .map_err(|source| Error::Write {
                path: parent,
                source,
            })?;
    }
    Ok(())
}

fn sync_scratch_transaction_tree(
    root: &Path,
    snapshots: &BTreeMap<PathBuf, ScratchFileSnapshot>,
    directories: &BTreeSet<PathBuf>,
) -> Result<()> {
    for relative in snapshots.keys() {
        let path = root.join(relative);
        File::open(&path)
            .and_then(|file| file.sync_all())
            .map_err(|source| Error::Write { path, source })?;
    }
    let mut directory_paths = directories
        .iter()
        .map(|relative| root.join(relative))
        .collect::<Vec<_>>();
    directory_paths.sort_by_key(|path| std::cmp::Reverse(path.components().count()));
    for path in directory_paths {
        File::open(&path)
            .and_then(|directory| directory.sync_all())
            .map_err(|source| Error::Write { path, source })?;
    }
    Ok(())
}

fn replace_scratch_snapshots_with_pre_exchange_hook<F>(
    root: &Path,
    existing_tree: ValidatedScratchTree,
    selected: BTreeMap<PathBuf, ScratchFileSnapshot>,
    pre_exchange_hook: F,
) -> Result<ScratchWorkspaceState>
where
    F: FnOnce(&Path) -> Result<()>,
{
    let (expected_state, selected_directories) = scratch_snapshot_layout(&selected)?;
    let parent = root.parent().ok_or_else(|| {
        Error::ProofAgentCommand(format!(
            "live scratch path {} has no parent directory",
            root.display()
        ))
    })?;
    remove_stale_scratch_transactions(parent)?;
    let current_tree = validated_scratch_tree(root)?;
    if current_tree != existing_tree {
        return Err(Error::ProofAgentCommand(
            "live scratch state changed after it was selected for replacement".to_owned(),
        ));
    }
    // A missing live root is the canonical empty tree. Validate that captured
    // state before materializing the directory; otherwise our own mkdir would
    // look like a concurrent state change against ValidatedScratchTree::default().
    ensure_scratch_directory(root)?;
    let transaction = tempfile::Builder::new()
        .prefix(SCRATCH_TRANSACTION_PREFIX)
        .tempdir_in(parent)
        .map_err(|source| Error::CreateDir {
            path: parent.to_owned(),
            source,
        })?;
    std::fs::set_permissions(transaction.path(), std::fs::Permissions::from_mode(0o700)).map_err(
        |source| Error::Write {
            path: transaction.path().to_owned(),
            source,
        },
    )?;
    for snapshot in selected.values() {
        write_scratch_snapshot(transaction.path(), snapshot)?;
    }
    let staged_tree = validated_scratch_tree(transaction.path())?;
    let staged_state = ScratchWorkspaceState {
        file_count: staged_tree.files.len(),
        total_bytes: staged_tree.files.iter().map(|file| file.bytes.len()).sum(),
    };
    if staged_state != expected_state || staged_tree.directories != selected_directories {
        return Err(Error::ProofAgentCommand(format!(
            "staged scratch transaction drifted: expected {} files/{} bytes, observed {} files/{} bytes",
            expected_state.file_count,
            expected_state.total_bytes,
            staged_state.file_count,
            staged_state.total_bytes
        )));
    }
    sync_scratch_transaction_tree(transaction.path(), &selected, &selected_directories)?;
    pre_exchange_hook(transaction.path())?;
    atomic_exchange_scratch_directories(transaction.path(), root)?;
    let observed = scratch_workspace_state(root)?;
    if observed != expected_state {
        return Err(Error::ProofAgentCommand(format!(
            "compacted scratch state drifted: expected {} files/{} bytes, observed {} files/{} bytes",
            expected_state.file_count,
            expected_state.total_bytes,
            observed.file_count,
            observed.total_bytes
        )));
    }
    transaction.close().map_err(|source| Error::Write {
        path: parent.to_owned(),
        source,
    })?;
    Ok(observed)
}

fn replace_scratch_snapshots(
    root: &Path,
    existing_tree: ValidatedScratchTree,
    selected: BTreeMap<PathBuf, ScratchFileSnapshot>,
) -> Result<ScratchWorkspaceState> {
    replace_scratch_snapshots_with_pre_exchange_hook(root, existing_tree, selected, |_| Ok(()))
}

fn persist_round_scratch_snapshots(
    persistent_scratch: &Path,
    existing_tree: ValidatedScratchTree,
    staged: Vec<ScratchFileSnapshot>,
) -> Result<ScratchWorkspaceState> {
    let existing = existing_tree
        .files
        .iter()
        .cloned()
        .map(|snapshot| (snapshot.relative_path.clone(), snapshot))
        .collect::<BTreeMap<_, _>>();
    // Compile-clean, host-owned snapshots form the trusted base. The
    // staged non-checked namespace is the current round's complete view: it
    // began as a hydration of prior WIP, so absence represents deletion and
    // current bytes must win over stale persistent bytes.
    let checked = existing
        .values()
        .filter(|snapshot| is_checked_scratch_snapshot(&snapshot.relative_path))
        .cloned()
        .map(|snapshot| (snapshot.relative_path.clone(), snapshot))
        .collect::<BTreeMap<_, _>>();
    let selected = select_scratch_snapshots(checked, staged);
    replace_scratch_snapshots(persistent_scratch, existing_tree, selected)
}

fn hydrate_round_scratch(proof_workdir: &Path, stage: &Path) -> Result<ScratchWorkspaceState> {
    let retained = validated_scratch_files(&proof_workdir.join("scratch"))?;
    merge_scratch_snapshots(&stage.join("scratch"), retained)
}

fn is_checked_scratch_snapshot(path: &Path) -> bool {
    path.components().next()
        == Some(std::path::Component::Normal(std::ffi::OsStr::new(
            CHECKED_SCRATCH_DIRECTORY,
        )))
}

fn checked_scratch_relative_path(relative: &Path, bytes: &[u8]) -> PathBuf {
    if is_checked_scratch_snapshot(relative) {
        return relative.to_owned();
    }
    let nested = Path::new(CHECKED_SCRATCH_DIRECTORY).join(relative);
    if validate_scratch_child_path(&nested).is_ok() {
        nested
    } else {
        // Preserve exact checked bytes if a source path cannot be represented
        // in the reserved namespace for a structural reason.
        Path::new(CHECKED_SCRATCH_DIRECTORY).join(format!("sha256-{}.v", sha256_hex(bytes)))
    }
}

fn persist_round_scratch(stage: &Path, proof_workdir: &Path) -> Result<ScratchWorkspaceState> {
    // Ordinary scratch .v files are explicitly untrusted work in progress.
    // Preserve them even when the agent never submitted them or their latest
    // diagnostic failed. The reserved checked/ subtree is host-owned: only the
    // digest-bound broker may update those passing snapshots, so an unchecked
    // later edit cannot overwrite the last compile-clean copy. An ordinary .v
    // that is byte-identical to its checked snapshot carries no additional
    // information and is omitted. All other structurally valid WIP is retained;
    // the container-wide writable-storage quota is the only storage bound.
    let persistent_scratch = proof_workdir.join("scratch");
    let retained_tree = validated_scratch_tree(&persistent_scratch)?;
    let retained = retained_tree
        .files
        .iter()
        .cloned()
        .map(|snapshot| (snapshot.relative_path, snapshot.bytes))
        .collect::<BTreeMap<_, _>>();
    let staged_files = validated_staged_scratch_files(&stage.join("scratch"))?;
    let staged = staged_files
        .into_iter()
        .filter(|snapshot| {
            if is_checked_scratch_snapshot(&snapshot.relative_path) {
                return false;
            }
            let extension = snapshot
                .relative_path
                .extension()
                .and_then(|extension| extension.to_str());
            if extension != Some("v") {
                return true;
            }
            let checked = checked_scratch_relative_path(&snapshot.relative_path, &snapshot.bytes);
            match retained.get(&checked) {
                Some(checked_bytes) => checked_bytes != &snapshot.bytes,
                None => true,
            }
        })
        .collect::<Vec<_>>();
    persist_round_scratch_snapshots(&persistent_scratch, retained_tree, staged)
}

fn persist_successful_scratch_candidate(
    proof_workdir: &Path,
    candidate_path: &Path,
    bytes: &[u8],
) -> Result<ScratchWorkspaceState> {
    let relative = candidate_path.strip_prefix("scratch").map_err(|_| {
        Error::ProofAgentCommand("successful scratch candidate escaped scratch/".to_owned())
    })?;
    if is_checked_scratch_snapshot(relative) {
        return Err(Error::ProofAgentCommand(
            "successful scratch candidate used the reserved checked/ namespace".to_owned(),
        ));
    }
    validate_scratch_child_path(relative).map_err(Error::ProofAgentCommand)?;
    std::str::from_utf8(bytes).map_err(|source| {
        Error::ProofAgentCommand(format!(
            "scratch file {} is not UTF-8: {source}",
            relative.display()
        ))
    })?;
    let checked_relative = checked_scratch_relative_path(relative, bytes);
    validate_scratch_child_path(&checked_relative).map_err(Error::ProofAgentCommand)?;
    let persistent_scratch = proof_workdir.join("scratch");
    let existing_tree = validated_scratch_tree(&persistent_scratch)?;
    let existing = existing_tree
        .files
        .iter()
        .cloned()
        .map(|snapshot| (snapshot.relative_path.clone(), snapshot))
        .collect::<BTreeMap<_, _>>();
    let mut checked = existing
        .values()
        .filter(|snapshot| is_checked_scratch_snapshot(&snapshot.relative_path))
        .cloned()
        .map(|snapshot| (snapshot.relative_path.clone(), snapshot))
        .collect::<BTreeMap<_, _>>();
    checked.insert(
        checked_relative.clone(),
        ScratchFileSnapshot {
            relative_path: checked_relative,
            bytes: bytes.to_vec(),
        },
    );
    let untrusted = existing
        .values()
        .filter(|snapshot| !is_checked_scratch_snapshot(&snapshot.relative_path))
        .cloned()
        .collect::<Vec<_>>();
    let selected = select_scratch_snapshots(checked, untrusted);
    replace_scratch_snapshots(&persistent_scratch, existing_tree, selected)
}

#[cfg(test)]
fn persist_successful_proof_module_candidate(
    proof_workdir: &Path,
    candidate_path: &Path,
    bytes: &[u8],
) -> Result<()> {
    PendingProofModulePublication::prepare(proof_workdir, candidate_path, bytes, true)?.commit();
    Ok(())
}

/// A module source is installed in the host workspace immediately before its
/// serialized checker invocation, but remains pending until that exact source
/// has been promoted into the host-only cache. The broker is single-threaded,
/// so no later diagnostic can reuse the pending source; dependency resolution
/// sees only the cache's previously checked `.vo` prefix. On checker failure the
/// newly installed source is removed, while a successful cache publication can
/// never precede durable source installation.
struct PendingProofModulePublication {
    destination: PathBuf,
    remove_on_drop: bool,
}

impl PendingProofModulePublication {
    fn prepare(
        proof_workdir: &Path,
        candidate_path: &Path,
        bytes: &[u8],
        checked_in_cache: bool,
    ) -> Result<Self> {
        let candidate = candidate_path.to_str().ok_or_else(|| {
            Error::ProofAgentCommand("proof module candidate path is not UTF-8".to_owned())
        })?;
        validate_proof_module_candidate_path(candidate).map_err(Error::ProofAgentCommand)?;
        std::str::from_utf8(bytes).map_err(|source| {
            Error::ProofAgentCommand(format!("proof module {candidate} is not UTF-8: {source}"))
        })?;
        let module_root = proof_workdir.join(PROOF_MODULE_DIRECTORY);
        ensure_scratch_directory(&module_root)?;
        let destination = proof_workdir.join(candidate_path);
        match std::fs::symlink_metadata(&destination) {
            Ok(metadata) => {
                if !metadata.file_type().is_file() || metadata.file_type().is_symlink() {
                    return Err(Error::ProofAgentCommand(format!(
                        "proof module destination {} is not a regular non-symlink file",
                        destination.display()
                    )));
                }
                if checked_in_cache {
                    let existing = std::fs::read(&destination).map_err(|source| Error::Read {
                        path: destination.clone(),
                        source,
                    })?;
                    if existing != bytes {
                        return Err(Error::ProofAgentCommand(format!(
                            "checked proof module {candidate} is immutable; create a new module name for a revised theorem"
                        )));
                    }
                    return Ok(Self {
                        destination,
                        remove_on_drop: false,
                    });
                }
                // A source absent from the ordered host cache is an orphan from
                // an interrupted, never-successful promotion, not an immutable
                // checked name. Remove it before staging this new diagnostic so
                // a revision can reuse a name that was never published.
                std::fs::remove_file(&destination).map_err(|source| Error::Write {
                    path: destination.clone(),
                    source,
                })?;
            }
            Err(source) if source.kind() == std::io::ErrorKind::NotFound => {}
            Err(source) => {
                return Err(Error::Read {
                    path: destination,
                    source,
                });
            }
        }
        let temporary = module_root.join(format!(
            ".module-write-{}-{}",
            std::process::id(),
            now_ms_since_epoch()
        ));
        let result = (|| -> Result<()> {
            let mut staged = OpenOptions::new()
                .write(true)
                .create_new(true)
                .mode(0o600)
                .open(&temporary)
                .map_err(|source| Error::Write {
                    path: temporary.clone(),
                    source,
                })?;
            staged.write_all(bytes).map_err(|source| Error::Write {
                path: temporary.clone(),
                source,
            })?;
            staged.flush().map_err(|source| Error::Write {
                path: temporary.clone(),
                source,
            })?;
            drop(staged);
            std::fs::rename(&temporary, &destination).map_err(|source| Error::Write {
                path: destination.clone(),
                source,
            })?;
            Ok(())
        })();
        if result.is_err() {
            let _ = std::fs::remove_file(&temporary);
        }
        result?;
        Ok(Self {
            destination,
            remove_on_drop: !checked_in_cache,
        })
    }

    fn commit(mut self) {
        self.remove_on_drop = false;
    }

    fn rollback(mut self) -> Result<()> {
        if self.remove_on_drop {
            std::fs::remove_file(&self.destination).map_err(|source| Error::Write {
                path: self.destination.clone(),
                source,
            })?;
            self.remove_on_drop = false;
        }
        Ok(())
    }
}

impl Drop for PendingProofModulePublication {
    fn drop(&mut self) {
        if self.remove_on_drop {
            let _ = std::fs::remove_file(&self.destination);
        }
    }
}

fn trusted_diagnostic_cache_directory(trusted_checker_path: &Path) -> PathBuf {
    trusted_checker_path
        .parent()
        .and_then(Path::parent)
        .expect("trusted checker is materialized under proof-agent/trusted-launcher")
        .join("trusted-diagnostic-cache")
}

fn archive_trusted_diagnostic_cache(
    artifacts: &ArtifactWriter,
    workspace_generation: usize,
) -> Result<TrustedDiagnosticCacheEvidence> {
    if workspace_generation == 0 {
        return Err(Error::TrustedRocqEnvironment(
            "proof workspace generation must be positive".to_owned(),
        ));
    }
    let source_root = artifacts
        .root()
        .join("proof-stage/proof-agent/trusted-diagnostic-cache");
    let source_metadata =
        std::fs::symlink_metadata(&source_root).map_err(|source| Error::Read {
            path: source_root.clone(),
            source,
        })?;
    if source_metadata.file_type().is_symlink() || !source_metadata.is_dir() {
        return Err(Error::TrustedRocqEnvironment(format!(
            "trusted diagnostic cache archive source is unsafe: {}",
            source_root.display()
        )));
    }

    let read_regular = |relative: &Path, allow_empty: bool| -> Result<Vec<u8>> {
        let path = source_root.join(relative);
        let metadata = std::fs::symlink_metadata(&path).map_err(|source| Error::Read {
            path: path.clone(),
            source,
        })?;
        if metadata.file_type().is_symlink()
            || !metadata.file_type().is_file()
            || (!allow_empty && metadata.len() == 0)
        {
            return Err(Error::TrustedRocqEnvironment(format!(
                "trusted diagnostic cache archive entry is unsafe: {}",
                path.display()
            )));
        }
        std::fs::read(&path).map_err(|source| Error::Read { path, source })
    };
    let directory_names = |path: &Path| -> Result<BTreeSet<String>> {
        std::fs::read_dir(path)
            .map_err(|source| Error::Read {
                path: path.to_owned(),
                source,
            })?
            .map(|entry| {
                let entry = entry.map_err(|source| Error::Read {
                    path: path.to_owned(),
                    source,
                })?;
                entry.file_name().into_string().map_err(|_| {
                    Error::TrustedRocqEnvironment(format!(
                        "trusted diagnostic cache contains a non-UTF-8 entry under {}",
                        path.display()
                    ))
                })
            })
            .collect()
    };

    let module_root = source_root.join(PROOF_MODULE_DIRECTORY);
    let module_metadata =
        std::fs::symlink_metadata(&module_root).map_err(|source| Error::Read {
            path: module_root.clone(),
            source,
        })?;
    if module_metadata.file_type().is_symlink() || !module_metadata.is_dir() {
        return Err(Error::TrustedRocqEnvironment(format!(
            "trusted diagnostic module cache archive source is unsafe: {}",
            module_root.display()
        )));
    }
    let order_relative = PathBuf::from("ProofModules/ORDER");
    let order_bytes = read_regular(&order_relative, true)?;
    let order = std::str::from_utf8(&order_bytes).map_err(|source| {
        Error::TrustedRocqEnvironment(format!("trusted proof module order is not UTF-8: {source}"))
    })?;
    let module_names = order.lines().map(str::to_owned).collect::<Vec<_>>();
    if order
        != module_names
            .iter()
            .map(|name| format!("{name}\n"))
            .collect::<String>()
    {
        return Err(Error::TrustedRocqEnvironment(
            "trusted proof module order is not canonical newline-delimited text".to_owned(),
        ));
    }
    let mut unique_modules = BTreeSet::new();
    for name in &module_names {
        validate_proof_module_candidate_path(&format!("{PROOF_MODULE_DIRECTORY}/{name}"))
            .map_err(Error::TrustedRocqEnvironment)?;
        if !unique_modules.insert(name.clone()) {
            return Err(Error::TrustedRocqEnvironment(format!(
                "trusted proof module order contains a duplicate entry: {name}"
            )));
        }
    }

    let witness_module_root = source_root.join(WITNESS_MODULE_DIRECTORY);
    let witness_module_metadata =
        std::fs::symlink_metadata(&witness_module_root).map_err(|source| Error::Read {
            path: witness_module_root.clone(),
            source,
        })?;
    if witness_module_metadata.file_type().is_symlink() || !witness_module_metadata.is_dir() {
        return Err(Error::TrustedRocqEnvironment(format!(
            "trusted witness module cache archive source is unsafe: {}",
            witness_module_root.display()
        )));
    }
    let witness_order_relative = PathBuf::from("WitnessModules/ORDER");
    let witness_order_bytes = read_regular(&witness_order_relative, true)?;
    let witness_order = std::str::from_utf8(&witness_order_bytes).map_err(|source| {
        Error::TrustedRocqEnvironment(format!(
            "trusted witness module order is not UTF-8: {source}"
        ))
    })?;
    let witness_module_names = witness_order.lines().map(str::to_owned).collect::<Vec<_>>();
    if witness_order
        != witness_module_names
            .iter()
            .map(|name| format!("{name}\n"))
            .collect::<String>()
    {
        return Err(Error::TrustedRocqEnvironment(
            "trusted witness module order is not canonical newline-delimited text".to_owned(),
        ));
    }
    let mut unique_witness_modules = BTreeSet::new();
    for name in &witness_module_names {
        let valid = name.strip_suffix(".v").is_some_and(|stem| {
            stem.starts_with(|character: char| character.is_ascii_uppercase())
                && stem
                    .bytes()
                    .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
        });
        if !valid || !unique_witness_modules.insert(name.clone()) {
            return Err(Error::TrustedRocqEnvironment(format!(
                "trusted witness module order contains an invalid or duplicate entry: {name}"
            )));
        }
    }

    let mut expected_relative = [
        "Schema.v",
        "Schema.vo",
        "Queries.v",
        "Queries.vo",
        "WitnessData.v",
        "WitnessData.vo",
        "Witness.v",
        "Witness.vo",
        "WitnessModules/ORDER",
        "ProofModules/ORDER",
    ]
    .into_iter()
    .map(PathBuf::from)
    .collect::<Vec<_>>();
    let mut expected_module_names = BTreeSet::from(["ORDER".to_owned()]);
    let mut expected_witness_module_names = BTreeSet::from(["ORDER".to_owned()]);
    for name in &witness_module_names {
        let stem = name
            .strip_suffix(".v")
            .expect("validated witness module has .v suffix");
        expected_relative.push(PathBuf::from(format!("WitnessModules/{name}")));
        expected_relative.push(PathBuf::from(format!("WitnessModules/{stem}.vo")));
        expected_witness_module_names.insert(name.clone());
        expected_witness_module_names.insert(format!("{stem}.vo"));
    }
    for name in &module_names {
        let stem = name
            .strip_suffix(".v")
            .expect("validated proof module has .v suffix");
        expected_relative.push(PathBuf::from(format!("ProofModules/{name}")));
        expected_relative.push(PathBuf::from(format!("ProofModules/{stem}.vo")));
        expected_module_names.insert(name.clone());
        expected_module_names.insert(format!("{stem}.vo"));
    }
    let expected_root_names = BTreeSet::from([
        "Schema.v".to_owned(),
        "Schema.vo".to_owned(),
        "Queries.v".to_owned(),
        "Queries.vo".to_owned(),
        "WitnessData.v".to_owned(),
        "WitnessData.vo".to_owned(),
        "Witness.v".to_owned(),
        "Witness.vo".to_owned(),
        "WitnessModules".to_owned(),
        "ProofModules".to_owned(),
        "SHA256SUMS".to_owned(),
    ]);
    if directory_names(&source_root)? != expected_root_names
        || directory_names(&module_root)? != expected_module_names
        || directory_names(&witness_module_root)? != expected_witness_module_names
    {
        return Err(Error::TrustedRocqEnvironment(
            "trusted diagnostic cache contains unexpected or missing entries".to_owned(),
        ));
    }

    let mut files = Vec::new();
    let mut expected_manifest = String::new();
    for relative in &expected_relative {
        let bytes = read_regular(
            relative,
            relative == &order_relative || relative == &witness_order_relative,
        )?;
        let relative_text = relative.to_str().ok_or_else(|| {
            Error::TrustedRocqEnvironment(
                "trusted diagnostic cache relative path is not UTF-8".to_owned(),
            )
        })?;
        expected_manifest.push_str(&format!("{}  {relative_text}\n", sha256_hex(&bytes)));
        files.push((relative.clone(), bytes));
    }
    let manifest_relative = PathBuf::from("SHA256SUMS");
    let manifest_bytes = read_regular(&manifest_relative, false)?;
    if manifest_bytes != expected_manifest.as_bytes() {
        return Err(Error::TrustedRocqEnvironment(
            "trusted diagnostic cache manifest is not the exact ordered cache digest set"
                .to_owned(),
        ));
    }
    for name in ["Schema.v", "Queries.v", "WitnessData.v", "Witness.v"] {
        let live = artifacts.root().join("proof-stage/formal-sql").join(name);
        let live_bytes =
            std::fs::read(&live).map_err(|source| Error::Read { path: live, source })?;
        let cached = files
            .iter()
            .find(|(relative, _)| relative == Path::new(name))
            .expect("base trusted cache source is in expected entries");
        if cached.1 != live_bytes {
            return Err(Error::TrustedRocqEnvironment(format!(
                "trusted diagnostic cache source binding drifted before archive: {name}"
            )));
        }
    }
    files.push((manifest_relative, manifest_bytes.clone()));

    let destination_root = artifacts.root().join(format!(
        "proof-stage/proof-agent/workspace-generations/{workspace_generation:04}/trusted-diagnostic-cache"
    ));
    let destination_parent = destination_root.parent().ok_or_else(|| {
        Error::TrustedRocqEnvironment("trusted cache archive path has no parent".to_owned())
    })?;
    std::fs::create_dir_all(destination_parent).map_err(|source| Error::CreateDir {
        path: destination_parent.to_owned(),
        source,
    })?;
    std::fs::create_dir(&destination_root).map_err(|source| {
        Error::TrustedRocqEnvironment(format!(
            "refusing to replace create-once trusted cache archive {}: {source}",
            destination_root.display()
        ))
    })?;
    let destination_modules = destination_root.join(PROOF_MODULE_DIRECTORY);
    std::fs::create_dir(&destination_modules).map_err(|source| Error::CreateDir {
        path: destination_modules,
        source,
    })?;
    let destination_witness_modules = destination_root.join(WITNESS_MODULE_DIRECTORY);
    std::fs::create_dir(&destination_witness_modules).map_err(|source| Error::CreateDir {
        path: destination_witness_modules,
        source,
    })?;
    for (relative, bytes) in files {
        let path = destination_root.join(relative);
        std::fs::write(&path, bytes).map_err(|source| Error::Write { path, source })?;
    }
    let manifest_path = format!(
        "proof-stage/proof-agent/workspace-generations/{workspace_generation:04}/trusted-diagnostic-cache/SHA256SUMS"
    );
    Ok(TrustedDiagnosticCacheEvidence {
        workspace_generation,
        manifest_path,
        manifest_sha256: sha256_hex(&manifest_bytes),
    })
}

fn recover_interrupted_trusted_cache_swap(trusted_checker_path: &Path) -> Result<()> {
    let trusted_cache = trusted_diagnostic_cache_directory(trusted_checker_path);
    let cache_parent = trusted_cache
        .parent()
        .expect("trusted diagnostic cache has a parent");
    let parent_metadata =
        std::fs::symlink_metadata(cache_parent).map_err(|source| Error::Read {
            path: cache_parent.to_owned(),
            source,
        })?;
    if parent_metadata.file_type().is_symlink() || !parent_metadata.is_dir() {
        return Err(Error::TrustedRocqEnvironment(format!(
            "trusted diagnostic cache parent is unsafe: {}",
            cache_parent.display()
        )));
    }
    let mut old_candidates = Vec::new();
    let mut stage_candidates = Vec::new();
    for entry in std::fs::read_dir(cache_parent).map_err(|source| Error::Read {
        path: cache_parent.to_owned(),
        source,
    })? {
        let entry = entry.map_err(|source| Error::Read {
            path: cache_parent.to_owned(),
            source,
        })?;
        let name = entry.file_name();
        let name = name.to_string_lossy();
        let target = if name.starts_with(".logos-trusted-diagnostic-cache-old.") {
            &mut old_candidates
        } else if name.starts_with(".logos-trusted-diagnostic-cache.") {
            &mut stage_candidates
        } else {
            continue;
        };
        let path = entry.path();
        let metadata = std::fs::symlink_metadata(&path).map_err(|source| Error::Read {
            path: path.clone(),
            source,
        })?;
        if metadata.file_type().is_symlink() || !metadata.is_dir() {
            return Err(Error::TrustedRocqEnvironment(format!(
                "interrupted trusted-cache artifact is unsafe: {}",
                path.display()
            )));
        }
        target.push(path);
    }
    match std::fs::symlink_metadata(&trusted_cache) {
        Ok(metadata) if metadata.file_type().is_symlink() || !metadata.is_dir() => {
            return Err(Error::TrustedRocqEnvironment(format!(
                "trusted diagnostic cache is unsafe: {}",
                trusted_cache.display()
            )));
        }
        Ok(_) => {}
        Err(source) if source.kind() == std::io::ErrorKind::NotFound => {
            if old_candidates.len() != 1 {
                return Err(Error::TrustedRocqEnvironment(format!(
                    "trusted diagnostic cache is missing with {} recoverable prior caches",
                    old_candidates.len()
                )));
            }
            std::fs::rename(&old_candidates[0], &trusted_cache).map_err(|source| Error::Write {
                path: trusted_cache.clone(),
                source,
            })?;
        }
        Err(source) => {
            return Err(Error::Read {
                path: trusted_cache,
                source,
            });
        }
    }
    for stage in stage_candidates {
        std::fs::remove_dir_all(&stage).map_err(|source| Error::Write {
            path: stage,
            source,
        })?;
    }
    Ok(())
}

/// Return the host-cache source for `candidate_path` only when the ordered
/// module registry says the name is checked and its source/object pair is safe.
/// Absence from ORDER means a same-named workspace file is merely an orphaned
/// pre-publication source and must not acquire append-only status.
fn checked_proof_module_cache_source(
    trusted_checker_path: &Path,
    candidate_path: &Path,
) -> Result<Option<Vec<u8>>> {
    let candidate = candidate_path.to_str().ok_or_else(|| {
        Error::TrustedRocqEnvironment("proof module candidate path is not UTF-8".to_owned())
    })?;
    validate_proof_module_candidate_path(candidate).map_err(Error::TrustedRocqEnvironment)?;
    let file_name = candidate_path
        .file_name()
        .and_then(|name| name.to_str())
        .expect("validated proof module path has a UTF-8 file name");
    let stem = file_name
        .strip_suffix(".v")
        .expect("validated proof module source has a .v suffix");
    let cache_root = trusted_diagnostic_cache_directory(trusted_checker_path);
    let module_root = cache_root.join(PROOF_MODULE_DIRECTORY);
    let root_metadata = std::fs::symlink_metadata(&module_root).map_err(|source| Error::Read {
        path: module_root.clone(),
        source,
    })?;
    if root_metadata.file_type().is_symlink() || !root_metadata.is_dir() {
        return Err(Error::TrustedRocqEnvironment(format!(
            "trusted proof module cache is not a regular directory: {}",
            module_root.display()
        )));
    }
    let order_path = module_root.join("ORDER");
    let order_metadata = std::fs::symlink_metadata(&order_path).map_err(|source| Error::Read {
        path: order_path.clone(),
        source,
    })?;
    if order_metadata.file_type().is_symlink() || !order_metadata.file_type().is_file() {
        return Err(Error::TrustedRocqEnvironment(format!(
            "trusted proof module order is not a regular file: {}",
            order_path.display()
        )));
    }
    let order = std::fs::read_to_string(&order_path).map_err(|source| Error::Read {
        path: order_path.clone(),
        source,
    })?;
    let manifest_path = cache_root.join("SHA256SUMS");
    let manifest_metadata =
        std::fs::symlink_metadata(&manifest_path).map_err(|source| Error::Read {
            path: manifest_path.clone(),
            source,
        })?;
    if manifest_metadata.file_type().is_symlink()
        || !manifest_metadata.file_type().is_file()
        || manifest_metadata.len() == 0
    {
        return Err(Error::TrustedRocqEnvironment(format!(
            "trusted diagnostic cache manifest is unsafe or empty: {}",
            manifest_path.display()
        )));
    }
    let manifest = std::fs::read_to_string(&manifest_path).map_err(|source| Error::Read {
        path: manifest_path.clone(),
        source,
    })?;
    let mut manifest_digests = BTreeMap::new();
    for line in manifest.lines() {
        let Some((digest, relative)) = line.split_once("  ") else {
            return Err(Error::TrustedRocqEnvironment(format!(
                "trusted diagnostic cache manifest contains a malformed line: {line:?}"
            )));
        };
        if digest.len() != 64
            || !digest
                .bytes()
                .all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase())
            || relative.is_empty()
            || manifest_digests
                .insert(relative.to_owned(), digest.to_owned())
                .is_some()
        {
            return Err(Error::TrustedRocqEnvironment(format!(
                "trusted diagnostic cache manifest contains an invalid or duplicate entry: {line:?}"
            )));
        }
    }
    let expected_order_digest = sha256_hex(order.as_bytes());
    if manifest_digests
        .get("ProofModules/ORDER")
        .map(String::as_str)
        != Some(expected_order_digest.as_str())
    {
        return Err(Error::TrustedRocqEnvironment(
            "trusted proof module order digest is not bound by the cache manifest".to_owned(),
        ));
    }
    let mut names = BTreeSet::new();
    for entry in order.lines().filter(|entry| !entry.is_empty()) {
        validate_proof_module_candidate_path(&format!("{PROOF_MODULE_DIRECTORY}/{entry}"))
            .map_err(|error| {
                Error::TrustedRocqEnvironment(format!(
                    "trusted proof module order contains an invalid entry {entry:?}: {error}"
                ))
            })?;
        if !names.insert(entry.to_owned()) {
            return Err(Error::TrustedRocqEnvironment(format!(
                "trusted proof module order contains a duplicate entry: {entry}"
            )));
        }
    }
    let source_path = module_root.join(file_name);
    let object_path = module_root.join(format!("{stem}.vo"));
    let source_relative = format!("ProofModules/{file_name}");
    let object_relative = format!("ProofModules/{stem}.vo");
    if !names.contains(file_name) {
        if source_path.exists()
            || std::fs::symlink_metadata(&source_path).is_ok()
            || object_path.exists()
            || std::fs::symlink_metadata(&object_path).is_ok()
        {
            return Err(Error::TrustedRocqEnvironment(format!(
                "trusted proof module cache contains an unordered entry for {file_name}"
            )));
        }
        if manifest_digests.contains_key(&source_relative)
            || manifest_digests.contains_key(&object_relative)
        {
            return Err(Error::TrustedRocqEnvironment(format!(
                "trusted diagnostic cache manifest contains an unordered entry for {file_name}"
            )));
        }
        return Ok(None);
    }
    for path in [&source_path, &object_path] {
        let metadata = std::fs::symlink_metadata(path).map_err(|source| Error::Read {
            path: path.clone(),
            source,
        })?;
        if metadata.file_type().is_symlink()
            || !metadata.file_type().is_file()
            || metadata.len() == 0
        {
            return Err(Error::TrustedRocqEnvironment(format!(
                "trusted proof module cache entry is unsafe or empty: {}",
                path.display()
            )));
        }
    }
    let source = std::fs::read(&source_path).map_err(|source| Error::Read {
        path: source_path,
        source,
    })?;
    let object = std::fs::read(&object_path).map_err(|source| Error::Read {
        path: object_path,
        source,
    })?;
    let source_digest = sha256_hex(&source);
    let object_digest = sha256_hex(&object);
    if manifest_digests.get(&source_relative).map(String::as_str) != Some(source_digest.as_str())
        || manifest_digests.get(&object_relative).map(String::as_str)
            != Some(object_digest.as_str())
    {
        return Err(Error::TrustedRocqEnvironment(format!(
            "trusted cache source/object digest binding is invalid for {file_name}"
        )));
    }
    Ok(Some(source))
}

fn record_diagnostic_environment_error(state: &Arc<Mutex<DiagnosticBrokerState>>, message: String) {
    if let Ok(mut locked) = state.lock() {
        locked.trusted_environment_error.get_or_insert(message);
    }
}

fn validate_diagnostic_broker_outcome(
    artifacts_root: &Path,
    round: usize,
    outcome: &DiagnosticBrokerOutcome,
) -> Result<()> {
    if outcome.accepted_count != outcome.invocations.len()
        || outcome.accepted_count != outcome.accepted_source_audits.len()
    {
        return Err(diagnostic_evidence_error(format!(
            "accepted count {} disagrees with {} checker invocations and {} accepted audits",
            outcome.accepted_count,
            outcome.invocations.len(),
            outcome.accepted_source_audits.len()
        )));
    }
    if outcome.rejected_source_audit_count != outcome.rejected_source_audits.len() {
        return Err(diagnostic_evidence_error(format!(
            "rejected source-audit count {} disagrees with {} records",
            outcome.rejected_source_audit_count,
            outcome.rejected_source_audits.len()
        )));
    }
    let classified_count = outcome
        .accepted_count
        .checked_add(outcome.rejected_source_audit_count)
        .ok_or_else(|| diagnostic_evidence_error("classified request count overflowed"))?;
    if classified_count > outcome.requests_seen
        || outcome.other_rejected_request_count != outcome.requests_seen - classified_count
    {
        return Err(diagnostic_evidence_error(format!(
            "request totals do not reconcile: seen {}, accepted {}, source-audit rejected {}, other rejected {}",
            outcome.requests_seen,
            outcome.accepted_count,
            outcome.rejected_source_audit_count,
            outcome.other_rejected_request_count
        )));
    }
    let mut request_ordinals = BTreeSet::new();
    let mut classified_requested_timeout_seconds = 0u64;
    let mut previous_accepted_request_ordinal = 0usize;
    for (index, (invocation, accepted)) in outcome
        .invocations
        .iter()
        .zip(&outcome.accepted_source_audits)
        .enumerate()
    {
        let sequence = index + 1;
        if invocation.sequence != Some(sequence)
            || invocation.mode.as_deref() != Some(accepted.mode.as_str())
            || invocation.candidate_path.as_deref() != Some(accepted.candidate_path.as_str())
            || invocation.purpose.as_deref() != Some(accepted.purpose.as_str())
            || accepted.sequence != sequence
            || invocation.candidate_sha256.as_deref() != Some(accepted.candidate_sha256.as_str())
            || invocation.requested_timeout_seconds != accepted.requested_timeout_seconds
            || invocation.problem_compile_passed
                != Some(accepted.mode == "problem" && invocation.compile_passed == Some(true))
            || invocation.compile_checkpoint_advanced
                != Some(accepted.mode == "problem" && invocation.compile_passed == Some(true))
        {
            return Err(diagnostic_evidence_error(format!(
                "accepted diagnostic identity drifted at checker sequence {sequence}"
            )));
        }
        if accepted.request_ordinal <= previous_accepted_request_ordinal
            || accepted.request_ordinal > outcome.requests_seen
            || !request_ordinals.insert(accepted.request_ordinal)
        {
            return Err(diagnostic_evidence_error(format!(
                "accepted diagnostic has invalid request ordinal {}",
                accepted.request_ordinal
            )));
        }
        previous_accepted_request_ordinal = accepted.request_ordinal;
        let stored_candidate = if accepted.mode == "module" {
            validate_proof_module_candidate_path(&accepted.candidate_path)
                .map_err(diagnostic_evidence_error)?
        } else {
            PathBuf::from("Problem.v")
        };
        let expected_candidate_path = format!(
            "proof-stage/proof-agent/rounds/{round:02}/interactive-diagnostics/{sequence:02}/checked-workspace/{}",
            stored_candidate.display()
        );
        if accepted.candidate.path != expected_candidate_path {
            return Err(diagnostic_evidence_error(format!(
                "accepted diagnostic candidate path {:?} does not equal {:?}",
                accepted.candidate.path, expected_candidate_path
            )));
        }
        let candidate = read_bound_diagnostic_artifact(artifacts_root, &accepted.candidate)?;
        if sha256_hex(&candidate) != accepted.candidate_sha256 {
            return Err(diagnostic_evidence_error(format!(
                "accepted candidate digest disagrees at checker sequence {sequence}"
            )));
        }
        let expected_audit_path = format!(
            "proof-stage/proof-agent/rounds/{round:02}/interactive-diagnostics/{sequence:02}/audit.json"
        );
        if accepted.audit.path != expected_audit_path {
            return Err(diagnostic_evidence_error(format!(
                "accepted diagnostic audit path {:?} does not equal {:?}",
                accepted.audit.path, expected_audit_path
            )));
        }
        let audit_bytes = read_bound_diagnostic_artifact(artifacts_root, &accepted.audit)?;
        let audit: AgentAudit = serde_json::from_slice(&audit_bytes).map_err(|source| {
            diagnostic_evidence_error(format!(
                "cannot parse accepted audit {}: {source}",
                accepted.audit.path
            ))
        })?;
        if !audit.passed || !audit.findings.is_empty() {
            return Err(diagnostic_evidence_error(format!(
                "accepted diagnostic audit {} is not clean",
                accepted.audit.path
            )));
        }
        classified_requested_timeout_seconds = classified_requested_timeout_seconds
            .checked_add(accepted.requested_timeout_seconds)
            .ok_or_else(|| diagnostic_evidence_error("accepted timeout total overflowed"))?;
    }

    let mut previous_rejected_request_ordinal = 0usize;
    for rejected in &outcome.rejected_source_audits {
        if rejected.request_ordinal <= previous_rejected_request_ordinal
            || rejected.request_ordinal > outcome.requests_seen
            || !request_ordinals.insert(rejected.request_ordinal)
        {
            return Err(diagnostic_evidence_error(format!(
                "source-audit rejection has invalid request ordinal {}",
                rejected.request_ordinal
            )));
        }
        previous_rejected_request_ordinal = rejected.request_ordinal;
        let root = format!(
            "proof-stage/proof-agent/rounds/{round:02}/rejected-diagnostic-source-audits/{:02}",
            rejected.request_ordinal
        );
        for (binding, name) in [
            (&rejected.problem, "Problem.v"),
            (&rejected.request, "request.json"),
            (&rejected.audit, "audit.json"),
            (&rejected.feedback, "feedback.txt"),
        ] {
            let expected_path = format!("{root}/{name}");
            if binding.path != expected_path {
                return Err(diagnostic_evidence_error(format!(
                    "rejected diagnostic binding path {:?} does not equal {:?}",
                    binding.path, expected_path
                )));
            }
        }
        let problem = read_bound_diagnostic_artifact(artifacts_root, &rejected.problem)?;
        if sha256_hex(&problem) != rejected.candidate_sha256 {
            return Err(diagnostic_evidence_error(format!(
                "rejected Problem.v digest disagrees with request ordinal {}",
                rejected.request_ordinal
            )));
        }
        let request_bytes = read_bound_diagnostic_artifact(artifacts_root, &rejected.request)?;
        let request: DiagnosticBrokerRequest =
            serde_json::from_slice(&request_bytes).map_err(|source| {
                diagnostic_evidence_error(format!(
                    "cannot parse rejected request {}: {source}",
                    rejected.request.path
                ))
            })?;
        if request.schema_version != 2
            || request.mode.as_str() != rejected.mode
            || request.candidate_path != rejected.candidate_path
            || request.purpose.as_str() != rejected.purpose
            || request.candidate_sha256 != rejected.candidate_sha256
            || request.candidate_bytes != problem.len() as u64
            || request.requested_timeout_seconds != rejected.requested_timeout_seconds
        {
            return Err(diagnostic_evidence_error(format!(
                "rejected request identity drifted at ordinal {}",
                rejected.request_ordinal
            )));
        }
        let audit_bytes = read_bound_diagnostic_artifact(artifacts_root, &rejected.audit)?;
        let audit: AgentAudit = serde_json::from_slice(&audit_bytes).map_err(|source| {
            diagnostic_evidence_error(format!(
                "cannot parse rejected audit {}: {source}",
                rejected.audit.path
            ))
        })?;
        if audit.passed || audit.findings.is_empty() {
            return Err(diagnostic_evidence_error(format!(
                "rejected diagnostic audit {} does not contain a rejection finding",
                rejected.audit.path
            )));
        }
        let feedback_bytes = read_bound_diagnostic_artifact(artifacts_root, &rejected.feedback)?;
        let feedback = std::str::from_utf8(&feedback_bytes).map_err(|source| {
            diagnostic_evidence_error(format!(
                "rejected feedback {} is not UTF-8: {source}",
                rejected.feedback.path
            ))
        })?;
        if !feedback.contains(&rejected.candidate_sha256)
            || !feedback.contains("checker was not executed")
        {
            return Err(diagnostic_evidence_error(format!(
                "rejected feedback identity drifted at ordinal {}",
                rejected.request_ordinal
            )));
        }
        classified_requested_timeout_seconds = classified_requested_timeout_seconds
            .checked_add(rejected.requested_timeout_seconds)
            .ok_or_else(|| diagnostic_evidence_error("rejected timeout total overflowed"))?;
    }
    if classified_requested_timeout_seconds > outcome.requested_timeout_seconds_reserved {
        return Err(diagnostic_evidence_error(format!(
            "classified requests reserve {classified_requested_timeout_seconds} seconds but broker recorded only {}",
            outcome.requested_timeout_seconds_reserved
        )));
    }
    Ok(())
}

impl DiagnosticBroker {
    fn start(
        artifacts_root: &Path,
        round: usize,
        workspace_generation: usize,
        trusted_checker_path: &Path,
        proof_workdir: &Path,
        logos_repo_root: &Path,
        rocq_opam_switch: Option<&Path>,
        active_problem_compile_checkpoint_sha256: Option<&str>,
        writable_storage_limit_bytes: u64,
        deadline: Instant,
    ) -> Result<Self> {
        let socket_directory = ProofDiagnosticSocketDirectory::create(artifacts_root, round)?;
        let socket_path = socket_directory.socket_path();
        let listener = UnixListener::bind(&socket_path).map_err(|source| {
            Error::ProofAgentCommand(format!(
                "failed to bind proof diagnostic broker socket {}: {source}",
                socket_path.display()
            ))
        })?;
        std::fs::set_permissions(&socket_path, std::fs::Permissions::from_mode(0o600)).map_err(
            |source| {
                Error::ProofAgentCommand(format!(
                    "failed to secure proof diagnostic broker socket {}: {source}",
                    socket_path.display()
                ))
            },
        )?;
        listener.set_nonblocking(true).map_err(|source| {
            Error::ProofAgentCommand(format!(
                "failed to configure proof diagnostic broker socket {}: {source}",
                socket_path.display()
            ))
        })?;

        let nonce_seed = format!(
            "{}:{}:{}:{}",
            std::process::id(),
            now_ms_since_epoch(),
            PROOF_AGENT_SESSION_HOME_COUNTER.fetch_add(1, Ordering::Relaxed),
            socket_path.display()
        );
        let nonce = sha256_hex(nonce_seed.as_bytes());
        let stop = Arc::new(AtomicBool::new(false));
        let state = Arc::new(Mutex::new(DiagnosticBrokerState {
            workspace_generation,
            active_problem_compile_checkpoint_sha256: active_problem_compile_checkpoint_sha256
                .map(str::to_owned),
            ..DiagnosticBrokerState::default()
        }));
        let thread_stop = Arc::clone(&stop);
        let thread_state = Arc::clone(&state);
        let artifacts_root = artifacts_root.to_owned();
        let outcome_artifacts_root = artifacts_root.clone();
        let trusted_checker_path = trusted_checker_path.to_owned();
        let proof_workdir = proof_workdir.to_owned();
        let logos_repo_root = logos_repo_root.to_owned();
        let rocq_opam_switch = rocq_opam_switch.map(Path::to_owned);
        let expected_nonce = nonce.clone();
        let handle = thread::Builder::new()
            .name(format!("logos-proof-diagnostic-{round}"))
            .spawn(move || {
                while !thread_stop.load(Ordering::Acquire) {
                    match listener.accept() {
                        Ok((stream, _)) => {
                            if thread_stop.load(Ordering::Acquire) {
                                break;
                            }
                            handle_diagnostic_broker_connection(
                                stream,
                                &expected_nonce,
                                &artifacts_root,
                                round,
                                &trusted_checker_path,
                                &proof_workdir,
                                &logos_repo_root,
                                rocq_opam_switch.as_deref(),
                                writable_storage_limit_bytes,
                                deadline,
                                &thread_state,
                            );
                        }
                        Err(source) if source.kind() == std::io::ErrorKind::WouldBlock => {
                            thread::sleep(Duration::from_millis(10));
                        }
                        Err(source) => {
                            if let Ok(mut locked) = thread_state.lock() {
                                locked.trusted_environment_error = Some(format!(
                                    "proof diagnostic broker accept failed: {source}"
                                ));
                            }
                            break;
                        }
                    }
                }
            })
            .map_err(|source| {
                Error::ProofAgentCommand(format!(
                    "failed to start proof diagnostic broker thread: {source}"
                ))
            })?;
        Ok(Self {
            socket_path,
            _socket_directory: socket_directory,
            nonce,
            artifacts_root: outcome_artifacts_root,
            round,
            stop,
            state,
            handle: Some(handle),
        })
    }

    fn nonce(&self) -> &str {
        &self.nonce
    }

    fn socket_path(&self) -> &Path {
        &self.socket_path
    }

    fn finish(mut self) -> Result<DiagnosticBrokerOutcome> {
        self.stop.store(true, Ordering::Release);
        let _ = UnixStream::connect(&self.socket_path);
        if let Some(handle) = self.handle.take() {
            handle.join().map_err(|_| {
                Error::ProofAgentCommand("proof diagnostic broker thread panicked".to_owned())
            })?;
        }
        let mut state = self.state.lock().map_err(|_| {
            Error::ProofAgentCommand("proof diagnostic broker state was poisoned".to_owned())
        })?;
        let accepted_count = state.accepted_source_audits.len();
        let rejected_source_audit_count = state.rejected_source_audits.len();
        let classified_count = accepted_count
            .checked_add(rejected_source_audit_count)
            .ok_or_else(|| diagnostic_evidence_error("classified request count overflowed"))?;
        let other_rejected_request_count = state
            .requests_seen
            .checked_sub(classified_count)
            .ok_or_else(|| {
                diagnostic_evidence_error(
                    "accepted plus rejected source-audit records exceed requests seen",
                )
            })?;
        let outcome = DiagnosticBrokerOutcome {
            requests_seen: state.requests_seen,
            requested_timeout_seconds_reserved: state.timeout_seconds_reserved,
            accepted_count,
            rejected_source_audit_count,
            other_rejected_request_count,
            invocations: std::mem::take(&mut state.invocations),
            accepted_source_audits: std::mem::take(&mut state.accepted_source_audits),
            rejected_source_audits: std::mem::take(&mut state.rejected_source_audits),
            latest_checkpoint: state.latest_checkpoint.take(),
            latest_feedback: state.latest_feedback.take(),
            trusted_environment_error: state.trusted_environment_error.take(),
        };
        validate_diagnostic_broker_outcome(&self.artifacts_root, self.round, &outcome)?;
        Ok(outcome)
    }
}

#[allow(clippy::too_many_arguments)]
fn handle_diagnostic_broker_connection(
    mut stream: UnixStream,
    expected_nonce: &str,
    artifacts_root: &Path,
    round: usize,
    trusted_checker_path: &Path,
    proof_workdir: &Path,
    logos_repo_root: &Path,
    rocq_opam_switch: Option<&Path>,
    writable_storage_limit_bytes: u64,
    deadline: Instant,
    state: &Arc<Mutex<DiagnosticBrokerState>>,
) {
    let transport_timeout = deadline
        .saturating_duration_since(Instant::now())
        .max(Duration::from_secs(1));
    let _ = stream.set_read_timeout(Some(transport_timeout));
    let _ = stream.set_write_timeout(Some(transport_timeout));
    let response = run_diagnostic_broker_request(
        &mut stream,
        expected_nonce,
        artifacts_root,
        round,
        trusted_checker_path,
        proof_workdir,
        logos_repo_root,
        rocq_opam_switch,
        writable_storage_limit_bytes,
        deadline,
        state,
    );
    let mut bytes = serde_json::to_vec(&response).unwrap_or_else(|source| {
        format!(
            "{{\"schemaVersion\":2,\"compilePassed\":false,\"problemCompilePassed\":false,\"error\":{}}}",
            serde_json::to_string(&source.to_string()).expect("serialize broker error")
        )
        .into_bytes()
    });
    bytes.push(b'\n');
    let _ = stream.write_all(&bytes);
    let _ = stream.flush();
}

#[allow(clippy::too_many_arguments)]
fn run_diagnostic_broker_request(
    stream: &mut UnixStream,
    expected_nonce: &str,
    artifacts_root: &Path,
    round: usize,
    trusted_checker_path: &Path,
    proof_workdir: &Path,
    logos_repo_root: &Path,
    rocq_opam_switch: Option<&Path>,
    writable_storage_limit_bytes: u64,
    deadline: Instant,
    state: &Arc<Mutex<DiagnosticBrokerState>>,
) -> DiagnosticBrokerResponse {
    let rejected = |error: String| DiagnosticBrokerResponse {
        schema_version: 2,
        sequence: None,
        mode: None,
        candidate_path: None,
        purpose: None,
        candidate_sha256: None,
        compile_passed: false,
        problem_compile_passed: false,
        compile_checkpoint_advanced: false,
        exit_code: None,
        timed_out: false,
        elapsed_ms: 0,
        stdout: String::new(),
        stderr: String::new(),
        error: Some(error),
    };

    let request_ordinal = {
        let mut locked = match state.lock() {
            Ok(locked) => locked,
            Err(_) => return rejected("diagnostic broker state was poisoned".to_owned()),
        };
        locked.requests_seen = locked.requests_seen.saturating_add(1);
        locked.requests_seen
    };

    let mut request_bytes = Vec::new();
    let mut block = [0u8; 512];
    loop {
        let count = match stream.read(&mut block) {
            Ok(0) => return rejected("diagnostic broker request ended before newline".to_owned()),
            Ok(count) => count,
            Err(source) => {
                return rejected(format!(
                    "failed to read diagnostic broker request: {source}"
                ));
            }
        };
        request_bytes.extend_from_slice(&block[..count]);
        if request_bytes.contains(&b'\n') {
            break;
        }
        if request_bytes.len() > DIAGNOSTIC_BROKER_HEADER_MAX_BYTES {
            return rejected(
                "diagnostic broker JSON header exceeds its protocol envelope".to_owned(),
            );
        }
    }
    let Some(newline) = request_bytes.iter().position(|byte| *byte == b'\n') else {
        return rejected("diagnostic broker request has no newline".to_owned());
    };
    if newline > DIAGNOSTIC_BROKER_HEADER_MAX_BYTES {
        return rejected("diagnostic broker JSON header exceeds its protocol envelope".to_owned());
    }
    let request = match serde_json::from_slice::<DiagnosticBrokerRequest>(&request_bytes[..newline])
    {
        Ok(request) => request,
        Err(source) => return rejected(format!("invalid diagnostic broker request: {source}")),
    };
    if request.schema_version != 2 {
        return rejected("diagnostic broker schemaVersion must equal 2".to_owned());
    }
    if request.nonce != expected_nonce {
        return rejected("diagnostic broker nonce mismatch".to_owned());
    }
    let candidate_path =
        match validate_diagnostic_candidate_path(request.mode, &request.candidate_path) {
            Ok(path) => path,
            Err(error) => return rejected(error),
        };
    if request.candidate_sha256.len() != 64
        || !request
            .candidate_sha256
            .bytes()
            .all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase())
    {
        return rejected("candidateSha256 must be 64 lowercase hexadecimal characters".to_owned());
    }
    if request.requested_timeout_seconds == 0 {
        return rejected("requestedTimeoutSeconds must be positive".to_owned());
    }
    if request.candidate_bytes > writable_storage_limit_bytes {
        return rejected(format!(
            "candidateBytes exceeds the proof-agent aggregate writable-storage quota of {writable_storage_limit_bytes} bytes"
        ));
    }

    let candidate_len = match usize::try_from(request.candidate_bytes) {
        Ok(candidate_len) => candidate_len,
        Err(_) => return rejected("candidateBytes cannot be represented on this host".to_owned()),
    };
    let upload_dir = artifacts_root.join(format!(
        "proof-stage/proof-agent/rounds/{round:02}/diagnostic-uploads"
    ));
    if let Err(source) = std::fs::create_dir_all(&upload_dir) {
        return rejected(format!(
            "failed to create diagnostic upload directory: {source}"
        ));
    }
    let pending_upload = PendingDiagnosticUpload::new(upload_dir.join(format!(
        ".request-{request_ordinal:08}-{}-{}.tmp",
        std::process::id(),
        now_ms_since_epoch()
    )));
    let mut upload = match OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(pending_upload.path())
    {
        Ok(upload) => upload,
        Err(source) => {
            return rejected(format!("failed to create diagnostic upload file: {source}"));
        }
    };
    let mut uploaded_digest = Sha256::new();
    let mut uploaded_len = 0usize;
    let buffered_candidate = &request_bytes[newline + 1..];
    if buffered_candidate.len() > candidate_len {
        return rejected("diagnostic request contains bytes beyond candidateBytes".to_owned());
    }
    if let Err(source) = upload.write_all(buffered_candidate) {
        return rejected(format!("failed to write diagnostic candidate: {source}"));
    }
    uploaded_digest.update(buffered_candidate);
    uploaded_len += buffered_candidate.len();
    let mut candidate_block = [0u8; 64 * 1024];
    while uploaded_len < candidate_len {
        let remaining = candidate_len - uploaded_len;
        let block_len = remaining.min(candidate_block.len());
        let count = match stream.read(&mut candidate_block[..block_len]) {
            Ok(0) => {
                return rejected("diagnostic candidate ended before candidateBytes".to_owned());
            }
            Ok(count) => count,
            Err(source) => {
                return rejected(format!("failed to read diagnostic candidate: {source}"));
            }
        };
        if let Err(source) = upload.write_all(&candidate_block[..count]) {
            return rejected(format!("failed to write diagnostic candidate: {source}"));
        }
        uploaded_digest.update(&candidate_block[..count]);
        uploaded_len += count;
    }
    if let Err(source) = upload.flush() {
        return rejected(format!("failed to flush diagnostic candidate: {source}"));
    }
    drop(upload);
    let uploaded_sha256 = format!("{:x}", uploaded_digest.finalize());
    if uploaded_sha256 != request.candidate_sha256 {
        return rejected(format!(
            "uploaded candidate digest differs from candidateSha256: expected {}, observed {uploaded_sha256}",
            request.candidate_sha256
        ));
    }
    if let Some(error) = state
        .lock()
        .ok()
        .and_then(|locked| locked.trusted_environment_error.clone())
    {
        return rejected(format!(
            "diagnostic broker is unavailable after a trusted environment failure: {error}"
        ));
    }

    let sequence = {
        let mut locked = match state.lock() {
            Ok(locked) => locked,
            Err(_) => return rejected("diagnostic broker state was poisoned".to_owned()),
        };
        if request.mode == DiagnosticCandidateMode::Problem
            && (locked.active_problem_compile_checkpoint_sha256.as_deref()
                == Some(request.candidate_sha256.as_str())
                || locked
                    .latest_checkpoint
                    .as_ref()
                    .is_some_and(|checkpoint| checkpoint.sha256 == request.candidate_sha256))
        {
            return rejected(format!(
                "Problem.v digest {} is already the active compile-clean checkpoint; an unchanged candidate is not recompiled or counted as progress",
                request.candidate_sha256
            ));
        }
        locked.timeout_seconds_reserved = locked
            .timeout_seconds_reserved
            .saturating_add(request.requested_timeout_seconds);
        locked.invocations.len() + 1
    };

    let (checked_workspace, diagnostic_problem_path, actual_sha256) =
        match snapshot_interactive_diagnostic_candidate(
            artifacts_root,
            proof_workdir,
            round,
            sequence,
            request.mode,
            &candidate_path,
            pending_upload.path(),
            &uploaded_sha256,
        ) {
            Ok(value) => value,
            Err(error) => return rejected(error.to_string()),
        };
    if actual_sha256 != request.candidate_sha256 {
        return rejected(format!(
            "candidate {} digest changed before the host snapshot: requested {}, observed {actual_sha256}",
            request.candidate_path, request.candidate_sha256
        ));
    }

    let effective_timeout_seconds = request
        .requested_timeout_seconds
        .min(deadline.saturating_duration_since(Instant::now()).as_secs());
    if effective_timeout_seconds == 0 {
        return rejected(
            "no time remains in this proof-agent turn for a host diagnostic".to_owned(),
        );
    }
    let diagnostic_dir = checked_workspace
        .parent()
        .expect("interactive checked workspace has a parent");
    let diagnostic_problem_relative = diagnostic_problem_path
        .strip_prefix(artifacts_root)
        .unwrap_or(&diagnostic_problem_path)
        .display()
        .to_string();
    let mapped_problem = match ReadOnlyMappedFile::open_utf8(&diagnostic_problem_path) {
        Ok(mapped) => mapped,
        Err(error) => return rejected(error.to_string()),
    };
    let problem_text = mapped_problem.as_str();
    let audit_started = Instant::now();
    let audit_findings = match request.mode {
        DiagnosticCandidateMode::Problem => {
            audit_rocq_text(&diagnostic_problem_relative, problem_text)
        }
        DiagnosticCandidateMode::Module => {
            audit_proof_module_rocq_text(&diagnostic_problem_relative, problem_text)
        }
        DiagnosticCandidateMode::Scratch => {
            audit_scratch_rocq_text(&diagnostic_problem_relative, problem_text)
        }
    };
    let candidate_audit = AgentAudit {
        passed: audit_findings.is_empty(),
        scanned_files: vec![diagnostic_problem_relative],
        findings: audit_findings,
    };
    if !candidate_audit.passed {
        let findings = candidate_audit
            .findings
            .iter()
            .take(4)
            .map(|finding| format!("{} at line {}", finding.token, finding.line))
            .collect::<Vec<_>>()
            .join(", ");
        let error = format!(
            "deterministic transient {} audit rejected diagnostic candidate before checker execution ({} finding(s): {findings})",
            request.mode.as_str(),
            candidate_audit.findings.len()
        );
        let feedback = format!(
            "interactive {} compile #{sequence} for {} ({actual_sha256}, purpose {}) was rejected by the host deterministic source audit; the checker was not executed: {findings}",
            request.mode.as_str(),
            request.candidate_path,
            request.purpose.as_str()
        );
        let rejection_dir = artifacts_root.join(format!(
            "proof-stage/proof-agent/rounds/{round:02}/rejected-diagnostic-source-audits/{request_ordinal:02}"
        ));
        if let Err(source) = std::fs::create_dir_all(&rejection_dir)
            .and_then(|()| {
                std::fs::rename(&diagnostic_problem_path, rejection_dir.join("Problem.v"))
            })
            .and_then(|()| write_pretty_json_file(rejection_dir.join("request.json"), &request))
            .and_then(|()| {
                write_pretty_json_file(rejection_dir.join("audit.json"), &candidate_audit)
            })
            .and_then(|()| std::fs::write(rejection_dir.join("feedback.txt"), &feedback))
            .and_then(|()| std::fs::remove_dir_all(diagnostic_dir))
        {
            let message =
                format!("failed to persist rejected diagnostic source-audit evidence: {source}");
            record_diagnostic_environment_error(state, message.clone());
            return rejected(message);
        }
        let rejected_source_audit = match (|| -> Result<RejectedDiagnosticSourceAudit> {
            Ok(RejectedDiagnosticSourceAudit {
                request_ordinal,
                mode: request.mode.as_str().to_owned(),
                candidate_path: request.candidate_path.clone(),
                purpose: request.purpose.as_str().to_owned(),
                candidate_sha256: actual_sha256.clone(),
                requested_timeout_seconds: request.requested_timeout_seconds,
                problem: diagnostic_artifact_binding(
                    artifacts_root,
                    &rejection_dir.join("Problem.v"),
                )?,
                request: diagnostic_artifact_binding(
                    artifacts_root,
                    &rejection_dir.join("request.json"),
                )?,
                audit: diagnostic_artifact_binding(
                    artifacts_root,
                    &rejection_dir.join("audit.json"),
                )?,
                feedback: diagnostic_artifact_binding(
                    artifacts_root,
                    &rejection_dir.join("feedback.txt"),
                )?,
            })
        })() {
            Ok(record) => record,
            Err(error) => {
                let message = error.to_string();
                record_diagnostic_environment_error(state, message.clone());
                return rejected(message);
            }
        };
        let mut locked = match state.lock() {
            Ok(locked) => locked,
            Err(_) => return rejected("diagnostic broker state was poisoned".to_owned()),
        };
        locked.latest_feedback = Some(feedback);
        locked.rejected_source_audits.push(rejected_source_audit);
        drop(locked);
        return DiagnosticBrokerResponse {
            schema_version: 2,
            sequence: None,
            mode: Some(request.mode),
            candidate_path: Some(request.candidate_path),
            purpose: Some(request.purpose),
            candidate_sha256: Some(actual_sha256),
            compile_passed: false,
            problem_compile_passed: false,
            compile_checkpoint_advanced: false,
            exit_code: None,
            timed_out: false,
            elapsed_ms: audit_started.elapsed().as_millis(),
            stdout: String::new(),
            stderr: String::new(),
            error: Some(error),
        };
    }
    if let Err(source) = write_pretty_json_file(diagnostic_dir.join("audit.json"), &candidate_audit)
    {
        let message = format!(
            "failed to persist the host diagnostic source audit before checker execution: {source}"
        );
        record_diagnostic_environment_error(state, message.clone());
        return rejected(message);
    }
    let accepted_source_audit = match (
        diagnostic_artifact_binding(artifacts_root, &diagnostic_problem_path),
        diagnostic_artifact_binding(artifacts_root, &diagnostic_dir.join("audit.json")),
    ) {
        (Ok(candidate), Ok(audit)) => AcceptedDiagnosticSourceAudit {
            request_ordinal,
            sequence,
            mode: request.mode.as_str().to_owned(),
            candidate_path: request.candidate_path.clone(),
            purpose: request.purpose.as_str().to_owned(),
            candidate_sha256: actual_sha256.clone(),
            requested_timeout_seconds: request.requested_timeout_seconds,
            candidate,
            audit,
        },
        (Err(error), _) | (_, Err(error)) => {
            let message = error.to_string();
            record_diagnostic_environment_error(state, message.clone());
            return rejected(message);
        }
    };

    // The broker handles one connection at a time. Installing the source now
    // closes the cache/source publication gap without making it reusable: the
    // current cache still lacks this logical name until the checker succeeds.
    let mut module_was_checked_before = false;
    let mut pending_module_publication = if request.mode == DiagnosticCandidateMode::Module {
        if let Err(error) = recover_interrupted_trusted_cache_swap(trusted_checker_path) {
            let message = error.to_string();
            record_diagnostic_environment_error(state, message.clone());
            return rejected(message);
        }
        let checked_source =
            match checked_proof_module_cache_source(trusted_checker_path, &candidate_path) {
                Ok(source) => source,
                Err(error) => {
                    let message = error.to_string();
                    record_diagnostic_environment_error(state, message.clone());
                    return rejected(message);
                }
            };
        if checked_source
            .as_ref()
            .is_some_and(|source| source.as_slice() != mapped_problem.as_bytes())
        {
            return rejected(format!(
                "checked proof module {} is immutable; create a new module name for revised source",
                request.candidate_path
            ));
        }
        module_was_checked_before = checked_source.is_some();
        match PendingProofModulePublication::prepare(
            proof_workdir,
            &candidate_path,
            mapped_problem.as_bytes(),
            checked_source.is_some(),
        ) {
            Ok(publication) => Some(publication),
            Err(error) => return rejected(error.to_string()),
        }
    } else {
        None
    };

    let (mut invocation, output) = run_host_diagnostic_rocq_check(
        trusted_checker_path,
        &checked_workspace,
        logos_repo_root,
        rocq_opam_switch,
        request.mode,
        &request.candidate_path,
        request.requested_timeout_seconds,
        effective_timeout_seconds,
    );
    let (stdout_bytes, stderr_bytes) = output
        .as_ref()
        .map(|output| (output.stdout.as_slice(), output.stderr.as_slice()))
        .unwrap_or((&[][..], &[][..]));
    let mut compile_passed = output
        .as_ref()
        .is_some_and(|output| output.status.success());
    if request.mode == DiagnosticCandidateMode::Module {
        let publication = pending_module_publication
            .take()
            .expect("module diagnostics prepare one source publication");
        let recovered_cache_source = recover_interrupted_trusted_cache_swap(trusted_checker_path)
            .and_then(|()| {
                checked_proof_module_cache_source(trusted_checker_path, &candidate_path)
            });
        if compile_passed {
            match recovered_cache_source {
                Ok(Some(source)) if source.as_slice() == mapped_problem.as_bytes() => {
                    publication.commit();
                }
                Ok(_) => {
                    let rollback_error = publication.rollback().err();
                    compile_passed = false;
                    let message = format!(
                        "module checker reported success without publishing the exact manifest-bound source/object pair for {}{}",
                        request.candidate_path,
                        rollback_error
                            .as_ref()
                            .map(|error| format!("; rollback also failed: {error}"))
                            .unwrap_or_default()
                    );
                    record_diagnostic_environment_error(state, message.clone());
                    invocation.error = Some(message);
                }
                Err(error) => {
                    let rollback_error = publication.rollback().err();
                    compile_passed = false;
                    let message = format!(
                        "could not validate successful module publication {} against the trusted cache: {error}{}",
                        request.candidate_path,
                        rollback_error
                            .as_ref()
                            .map(|error| format!("; rollback also failed: {error}"))
                            .unwrap_or_default()
                    );
                    record_diagnostic_environment_error(state, message.clone());
                    invocation.error = Some(message);
                }
            }
        } else {
            match recovered_cache_source {
                Ok(Some(source)) if source.as_slice() == mapped_problem.as_bytes() => {
                    // A late signal/timeout may make the wrapper report failure
                    // after the trusted checker atomically published its cache.
                    // Retain the already-installed exact source so no outcome
                    // can expose a cache-only module.
                    publication.commit();
                    if module_was_checked_before {
                        let message = format!(
                            "module checker failed while revalidating already checked source {}; retained the prior checked source and disabled the diagnostic broker",
                            request.candidate_path
                        );
                        record_diagnostic_environment_error(state, message.clone());
                        invocation.error = Some(message);
                    } else {
                        // The compiler-created object, exact source, ORDER, and
                        // all three digests were atomically published. A late
                        // wrapper signal cannot turn that completed diagnostic
                        // into a false response without splitting the durable
                        // reuse predicate from broker telemetry.
                        compile_passed = true;
                        invocation.error = None;
                    }
                }
                Ok(_) => {
                    if let Err(error) = publication.rollback() {
                        let message = format!(
                            "failed to roll back unsuccessful proof module {}: {error}",
                            request.candidate_path
                        );
                        record_diagnostic_environment_error(state, message.clone());
                        invocation.error = Some(message);
                    }
                }
                Err(error) => {
                    let rollback_error = publication.rollback().err();
                    let message = format!(
                        "could not reconcile failed module publication {} with the trusted cache: {error}{}",
                        request.candidate_path,
                        rollback_error
                            .as_ref()
                            .map(|error| format!("; rollback also failed: {error}"))
                            .unwrap_or_default()
                    );
                    record_diagnostic_environment_error(state, message.clone());
                    invocation.error = Some(message);
                }
            }
        }
    }
    if compile_passed
        && request.mode == DiagnosticCandidateMode::Scratch
        && let Err(error) = persist_successful_scratch_candidate(
            proof_workdir,
            &candidate_path,
            mapped_problem.as_bytes(),
        )
    {
        compile_passed = false;
        let message = format!(
            "failed to retain successful scratch candidate {}: {error}",
            request.candidate_path
        );
        record_diagnostic_environment_error(state, message.clone());
        invocation.error = Some(message);
    }
    let problem_compile_passed = compile_passed && request.mode == DiagnosticCandidateMode::Problem;
    let compile_checkpoint_advanced = problem_compile_passed;
    invocation.sequence = Some(sequence);
    invocation.mode = Some(request.mode.as_str().to_owned());
    invocation.candidate_sha256 = Some(actual_sha256.clone());
    invocation.candidate_path = Some(request.candidate_path.clone());
    invocation.purpose = Some(request.purpose.as_str().to_owned());
    invocation.compile_passed = Some(compile_passed);
    invocation.problem_compile_passed = Some(problem_compile_passed);
    invocation.compile_checkpoint_advanced = Some(compile_checkpoint_advanced);
    invocation.stdout_sha256 = Some(sha256_hex(stdout_bytes));
    invocation.stderr_sha256 = Some(sha256_hex(stderr_bytes));

    if let Err(source) = std::fs::write(diagnostic_dir.join("stdout.txt"), stdout_bytes)
        .and_then(|()| std::fs::write(diagnostic_dir.join("stderr.txt"), stderr_bytes))
        .and_then(|()| write_pretty_json_file(diagnostic_dir.join("request.json"), &request))
        .and_then(|()| write_pretty_json_file(diagnostic_dir.join("invocation.json"), &invocation))
    {
        record_diagnostic_environment_error(
            state,
            format!(
                "failed to persist accepted diagnostic checker evidence for sequence {sequence}: {source}"
            ),
        );
    }

    let stdout = String::from_utf8_lossy(stdout_bytes).into_owned();
    let stderr = String::from_utf8_lossy(stderr_bytes).into_owned();
    let feedback = format!(
        "interactive {} compile #{sequence} for {} ({actual_sha256}, purpose {}): exit {:?}, timed out {}, elapsed {} ms, checkpoint advanced {}\n{}",
        request.mode.as_str(),
        request.candidate_path,
        request.purpose.as_str(),
        invocation.exit_code,
        invocation.timed_out,
        invocation.elapsed_ms,
        compile_checkpoint_advanced,
        stderr
    );
    if let Ok(mut locked) = state.lock() {
        if compile_checkpoint_advanced {
            locked.latest_checkpoint = Some(ProblemCompileCheckpoint {
                path: diagnostic_problem_path.clone(),
                sha256: actual_sha256.clone(),
                workspace_generation: locked.workspace_generation,
                round,
                sequence,
            });
        }
        if is_trusted_rocq_environment_failure(invocation.exit_code) {
            locked.trusted_environment_error = Some(format!(
                "interactive host problem compiler reported an invalid trusted environment: {feedback}"
            ));
        }
        locked.latest_feedback = Some(feedback);
        locked.accepted_source_audits.push(accepted_source_audit);
        locked.invocations.push(invocation.clone());
    }

    DiagnosticBrokerResponse {
        schema_version: 2,
        sequence: Some(sequence),
        mode: Some(request.mode),
        candidate_path: Some(request.candidate_path),
        purpose: Some(request.purpose),
        candidate_sha256: Some(actual_sha256),
        compile_passed,
        problem_compile_passed,
        compile_checkpoint_advanced,
        exit_code: invocation.exit_code,
        timed_out: invocation.timed_out,
        elapsed_ms: invocation.elapsed_ms,
        stdout,
        stderr,
        error: invocation.error,
    }
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
    proof_agent_context: &PreparedProofAgentContext,
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
    )?;
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
            let (audit, candidate_claim, precondition_source, precondition_definition) =
                audit_proof_workspace_for_mode(
                    artifacts,
                    &checked_workspace,
                    trusted_sources,
                    options.verification_mode,
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
    let (audit, candidate_claim, precondition_source, precondition_definition) =
        audit_proof_workspace_for_mode(
            artifacts,
            &checked_workspace,
            trusted_sources,
            options.verification_mode,
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
    let (counterexample_handoff, handoff_error) = load_counterexample_handoff(&proof_workdir);
    if let Some(error) = handoff_error.as_ref() {
        append_output_file(&stderr_artifact, "counterexample handoff", error.as_bytes())?;
    }
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

fn validate_authority_closure(
    proof_workdir: &Path,
    logos_repo_root: &Path,
) -> Result<ContextFileBinding> {
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
    for name in PROOF_SOURCE_FILES {
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
    for name in PROOF_CONTEXT_FILES {
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

fn snapshot_interactive_diagnostic_candidate(
    artifacts_root: &Path,
    proof_workdir: &Path,
    round: usize,
    sequence: usize,
    mode: DiagnosticCandidateMode,
    candidate_path: &Path,
    upload_path: &Path,
    problem_sha256: &str,
) -> Result<(PathBuf, PathBuf, String)> {
    let upload_metadata = std::fs::symlink_metadata(upload_path).map_err(|source| Error::Read {
        path: upload_path.to_owned(),
        source,
    })?;
    if !upload_metadata.file_type().is_file() || upload_metadata.file_type().is_symlink() {
        return Err(Error::ProofAgentCommand(format!(
            "interactive {} candidate {} is not a regular upload file",
            mode.as_str(),
            candidate_path.display()
        )));
    }
    let snapshot_dir = artifacts_root.join(format!(
        "proof-stage/proof-agent/rounds/{round:02}/interactive-diagnostics/{sequence:02}/checked-workspace"
    ));
    std::fs::create_dir_all(&snapshot_dir).map_err(|source| Error::CreateDir {
        path: snapshot_dir.clone(),
        source,
    })?;
    for name in [
        "Schema.v",
        "Queries.v",
        "WitnessData.v",
        "Witness.v",
        "Goal.v",
    ] {
        let source_path = proof_workdir.join(name);
        let source_metadata =
            std::fs::symlink_metadata(&source_path).map_err(|source| Error::Read {
                path: source_path.clone(),
                source,
            })?;
        if !source_metadata.file_type().is_file() {
            return Err(Error::ProofAgentCommand(format!(
                "interactive diagnostic trusted input is not a regular file: {}",
                source_path.display()
            )));
        }
        let destination = snapshot_dir.join(name);
        std::fs::copy(&source_path, &destination)
            .map(|_| ())
            .map_err(|source| Error::Write {
                path: destination,
                source,
            })?;
    }
    copy_witness_support_sources(proof_workdir, &snapshot_dir)?;
    let snapshot_candidate = match mode {
        DiagnosticCandidateMode::Problem | DiagnosticCandidateMode::Scratch => {
            snapshot_dir.join("Problem.v")
        }
        DiagnosticCandidateMode::Module => snapshot_dir.join(candidate_path),
    };
    if let Some(parent) = snapshot_candidate.parent() {
        std::fs::create_dir_all(parent).map_err(|source| Error::CreateDir {
            path: parent.to_owned(),
            source,
        })?;
    }
    if mode == DiagnosticCandidateMode::Module {
        let source_problem = proof_workdir.join("Problem.v");
        let destination_problem = snapshot_dir.join("Problem.v");
        std::fs::copy(&source_problem, &destination_problem)
            .map(|_| ())
            .map_err(|source| Error::Write {
                path: destination_problem,
                source,
            })?;
    }
    std::fs::rename(upload_path, &snapshot_candidate).map_err(|source| Error::Write {
        path: snapshot_candidate.clone(),
        source,
    })?;
    Ok((snapshot_dir, snapshot_candidate, problem_sha256.to_owned()))
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

fn run_trusted_rocq_check(
    trusted_checker_path: &Path,
    checked_workspace: &Path,
    logos_repo_root: &Path,
    rocq_opam_switch: Option<&Path>,
    timeout: Duration,
) -> std::io::Result<Output> {
    trusted_rocq_check_command(
        trusted_checker_path,
        checked_workspace,
        logos_repo_root,
        rocq_opam_switch,
        timeout,
        TrustedRocqCheckMode::Full,
    )
    .output()
}

fn run_host_diagnostic_rocq_check(
    trusted_checker_path: &Path,
    checked_workspace: &Path,
    logos_repo_root: &Path,
    rocq_opam_switch: Option<&Path>,
    candidate_mode: DiagnosticCandidateMode,
    candidate_path: &str,
    requested_timeout_seconds: u64,
    effective_timeout_seconds: u64,
) -> (DiagnosticCheckerInvocation, Option<Output>) {
    let started_at_unix_ms = now_ms_since_epoch();
    let started = Instant::now();
    let trusted_mode = match candidate_mode {
        DiagnosticCandidateMode::Module => TrustedRocqCheckMode::ModuleDiagnostic {
            timeout_seconds: effective_timeout_seconds,
            candidate_path: candidate_path.to_owned(),
        },
        DiagnosticCandidateMode::Problem | DiagnosticCandidateMode::Scratch => {
            TrustedRocqCheckMode::ProblemDiagnostic {
                timeout_seconds: effective_timeout_seconds,
            }
        }
    };
    let result = trusted_rocq_check_command(
        trusted_checker_path,
        checked_workspace,
        logos_repo_root,
        rocq_opam_switch,
        Duration::from_secs(effective_timeout_seconds),
        trusted_mode,
    )
    .output();
    match result {
        Ok(output) => {
            let exit_code = output.status.code();
            (
                DiagnosticCheckerInvocation {
                    sequence: None,
                    mode: None,
                    candidate_sha256: None,
                    candidate_path: None,
                    purpose: None,
                    compile_passed: None,
                    problem_compile_passed: None,
                    compile_checkpoint_advanced: None,
                    stdout_sha256: None,
                    stderr_sha256: None,
                    requested_timeout_seconds,
                    effective_timeout_seconds,
                    started_at_unix_ms,
                    elapsed_ms: started.elapsed().as_millis(),
                    exit_code,
                    timed_out: matches!(exit_code, Some(124 | 137)),
                    error: None,
                },
                Some(output),
            )
        }
        Err(source) => (
            DiagnosticCheckerInvocation {
                sequence: None,
                mode: None,
                candidate_sha256: None,
                candidate_path: None,
                purpose: None,
                compile_passed: Some(false),
                problem_compile_passed: Some(false),
                compile_checkpoint_advanced: None,
                stdout_sha256: None,
                stderr_sha256: None,
                requested_timeout_seconds,
                effective_timeout_seconds,
                started_at_unix_ms,
                elapsed_ms: started.elapsed().as_millis(),
                exit_code: None,
                timed_out: source.kind() == std::io::ErrorKind::TimedOut,
                error: Some(format!(
                    "failed to start host problem-only Rocq check: {source}"
                )),
            },
            None,
        ),
    }
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
) -> Result<ProblemCompileCheckpoint> {
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
        DiagnosticCandidateMode::Problem,
        "Problem.v",
        options.proof_check_timeout_seconds,
        options.proof_check_timeout_seconds,
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
        return Ok(ProblemCompileCheckpoint {
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
    checkpoint: &ProblemCompileCheckpoint,
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

fn run_trusted_rocq_environment_preflight(
    trusted_checker_path: &Path,
    proof_workspace: &Path,
    logos_repo_root: &Path,
    rocq_opam_switch: Option<&Path>,
    timeout: Duration,
    witness_only: bool,
) -> std::io::Result<Output> {
    trusted_rocq_check_command(
        trusted_checker_path,
        proof_workspace,
        logos_repo_root,
        rocq_opam_switch,
        timeout,
        if witness_only {
            TrustedRocqCheckMode::WitnessPreflight
        } else {
            TrustedRocqCheckMode::Preflight
        },
    )
    .output()
}

fn trusted_rocq_check_command(
    trusted_checker_path: &Path,
    checked_workspace: &Path,
    logos_repo_root: &Path,
    rocq_opam_switch: Option<&Path>,
    timeout: Duration,
    mode: TrustedRocqCheckMode,
) -> Command {
    let trusted_cache_dir = trusted_diagnostic_cache_directory(trusted_checker_path);
    let mut process = Command::new(TRUSTED_HOST_TIMEOUT);
    process
        .env_clear()
        .env("PATH", TRUSTED_CHECKER_PATH)
        .env("HOME", TRUSTED_CHECKER_HOME)
        .env("LC_ALL", FIXED_HOST_LOCALE)
        .env("LANG", FIXED_HOST_LOCALE)
        .arg("--signal=TERM")
        .arg("--kill-after=5s")
        .arg(format!("{}s", timeout.as_secs().max(1)))
        .arg(TRUSTED_HOST_BASH)
        .arg(trusted_checker_path)
        .env("LOGOS_REPO_ROOT", logos_repo_root)
        .env("LOGOS_PROOF_WORKDIR", checked_workspace)
        .env("LOGOS_TRUSTED_ROCQ_CACHE_DIR", trusted_cache_dir);
    match mode {
        TrustedRocqCheckMode::Full => {}
        TrustedRocqCheckMode::Preflight => {
            process.arg("--preflight");
        }
        TrustedRocqCheckMode::WitnessPreflight => {
            process.arg("--witness-preflight");
        }
        TrustedRocqCheckMode::ProblemDiagnostic { timeout_seconds } => {
            process
                .arg("--problem-diagnostic")
                .arg("--timeout-seconds")
                .arg(timeout_seconds.to_string());
        }
        TrustedRocqCheckMode::ModuleDiagnostic {
            timeout_seconds,
            candidate_path,
        } => {
            process
                .arg("--module-diagnostic")
                .arg("--candidate")
                .arg(candidate_path)
                .arg("--timeout-seconds")
                .arg(timeout_seconds.to_string());
        }
    }
    if let Some(switch) = rocq_opam_switch {
        process.env("LOGOS_ROCQ_OPAM_SWITCH", switch);
    }
    for name in [
        "LOGOS_SHARED_ROCQ_PREFIX_CACHE_DIR",
        "LOGOS_SHARED_ROCQ_CHECKER_RUNTIME_CACHE_DIR",
        "LOGOS_TRUSTED_ROCQ_AUTHORITY_SHA256",
    ] {
        if let Some(value) = std::env::var_os(name) {
            process.env(name, value);
        }
    }
    process
}

fn persist_trusted_environment_preflight_evidence(
    artifacts: &ArtifactWriter,
    workspace_generation: usize,
    stdout: &[u8],
    stderr: &[u8],
    invocation: &TrustedCheckInvocation,
) -> Result<()> {
    if workspace_generation == 0 {
        return Err(Error::ProofAgentCommand(
            "proof workspace generation must be positive".to_owned(),
        ));
    }
    let evidence_root = artifacts.root().join(format!(
        "proof-stage/proof-agent/workspace-generations/{workspace_generation:04}/trusted-environment-preflight"
    ));
    let parent = evidence_root.parent().ok_or_else(|| {
        Error::ProofAgentCommand("trusted preflight evidence path has no parent".to_owned())
    })?;
    std::fs::create_dir_all(parent).map_err(|source| Error::CreateDir {
        path: parent.to_owned(),
        source,
    })?;
    std::fs::create_dir(&evidence_root).map_err(|source| {
        Error::ProofAgentCommand(format!(
            "refusing to replace create-once trusted preflight evidence {}: {source}",
            evidence_root.display()
        ))
    })?;
    for (name, bytes) in [("stdout.txt", stdout), ("stderr.txt", stderr)] {
        let path = evidence_root.join(name);
        std::fs::write(&path, bytes).map_err(|source| Error::Write { path, source })?;
    }
    let invocation_path = evidence_root.join("invocation.json");
    write_pretty_json_file(invocation_path.clone(), invocation).map_err(|source| Error::Write {
        path: invocation_path,
        source,
    })?;
    Ok(())
}

fn validate_trusted_rocq_environment(
    artifacts: &ArtifactWriter,
    options: &Config,
    workspace_generation: usize,
    witness_only: bool,
) -> Result<TrustedCheckInvocation> {
    let trusted_checker_path = write_trusted_rocq_checker(artifacts)?;
    let proof_workspace = artifacts.root().join("proof-stage/formal-sql");
    let logos_repo_root = options
        .logos_repo_root
        .clone()
        .map(Ok)
        .unwrap_or_else(std::env::current_dir)
        .map_err(|source| Error::TrustedRocqEnvironment(source.to_string()))?;
    let timeout_seconds = options.proof_check_timeout_seconds;
    let started = Instant::now();
    let output = match run_trusted_rocq_environment_preflight(
        &trusted_checker_path,
        &proof_workspace,
        &logos_repo_root,
        options.proof_rocq_opam_switch.as_deref(),
        Duration::from_secs(timeout_seconds),
        witness_only,
    ) {
        Ok(output) => output,
        Err(source) => {
            let message = source.to_string();
            let invocation = TrustedCheckInvocation {
                timeout_seconds,
                elapsed_ms: started.elapsed().as_millis(),
                exit_code: None,
                timed_out: source.kind() == std::io::ErrorKind::TimedOut,
                error: Some(message.clone()),
            };
            persist_trusted_environment_preflight_evidence(
                artifacts,
                workspace_generation,
                &[],
                &[],
                &invocation,
            )?;
            return Err(Error::TrustedRocqEnvironment(message));
        }
    };
    let stderr = String::from_utf8_lossy(&output.stderr);
    let exit_code = output.status.code();
    let timed_out = matches!(exit_code, Some(124 | 137));
    let error = (!output.status.success())
        .then(|| format!("preflight exited with status {}: {}", output.status, stderr));
    let invocation = TrustedCheckInvocation {
        timeout_seconds,
        elapsed_ms: started.elapsed().as_millis(),
        exit_code,
        timed_out,
        error: error.clone(),
    };
    persist_trusted_environment_preflight_evidence(
        artifacts,
        workspace_generation,
        &output.stdout,
        &output.stderr,
        &invocation,
    )?;
    if output.status.success() {
        return Ok(invocation);
    }
    Err(Error::TrustedRocqEnvironment(
        error.expect("non-successful preflight has an error message"),
    ))
}

fn is_trusted_rocq_environment_failure(exit_code: Option<i32>) -> bool {
    exit_code == Some(TRUSTED_ROCQ_ENVIRONMENT_FAILURE_EXIT_CODE)
}

#[cfg(test)]
fn audit_proof_workspace(
    artifacts: &ArtifactWriter,
    proof_dir: &Path,
    trusted_sources: &TrustedProofSources,
) -> Result<AgentAudit> {
    audit_proof_workspace_for_mode(
        artifacts,
        proof_dir,
        trusted_sources,
        VerificationMode::SafeUnconditional,
    )
    .map(|(audit, _, _, _)| audit)
}

fn audit_proof_workspace_for_mode(
    artifacts: &ArtifactWriter,
    proof_dir: &Path,
    trusted_sources: &TrustedProofSources,
    verification_mode: VerificationMode,
) -> Result<(
    AgentAudit,
    Option<VerificationClaimKind>,
    Option<PreconditionSource>,
    Option<String>,
)> {
    let mut scanned_files = Vec::new();
    let mut findings = Vec::new();
    let mut problem_text = None;
    let mut problem_path = None;
    for name in PROOF_SOURCE_FILES {
        let path = proof_dir.join(name);
        let relative = path
            .strip_prefix(artifacts.root())
            .unwrap_or(&path)
            .display()
            .to_string();
        scanned_files.push(relative.clone());
        let text = std::fs::read_to_string(&path).map_err(|source| Error::Read {
            path: path.clone(),
            source,
        })?;
        if trusted_sources
            .get(name)
            .is_some_and(|expected| expected != &text)
        {
            findings.push(AuditFinding {
                path: relative.clone(),
                line: 1,
                token: "trusted source modified".to_owned(),
                excerpt: format!("{name} differs from the pre-agent generated source"),
            });
        }
        if *name == "Problem.v" {
            findings.extend(audit_rocq_text(&relative, &text));
            problem_text = Some(text);
            problem_path = Some(relative);
        }
    }
    for (module_relative, module_bytes) in
        validated_proof_module_sources(&proof_dir.join(PROOF_MODULE_DIRECTORY))?
    {
        let path = proof_dir.join(&module_relative);
        let relative = path
            .strip_prefix(artifacts.root())
            .unwrap_or(&path)
            .display()
            .to_string();
        let text = std::str::from_utf8(&module_bytes)
            .expect("validated proof module source remains UTF-8");
        scanned_files.push(relative.clone());
        findings.extend(audit_proof_module_rocq_text(&relative, text));
    }
    let problem_path = problem_path
        .as_deref()
        .expect("proof source registry always contains Problem.v");
    let problem_text = problem_text
        .as_deref()
        .expect("proof source registry always contains Problem.v");
    let (candidate_claim, precondition_source, precondition_definition) =
        if verification_mode == VerificationMode::Conditional {
            let finding = reject_conditional_verification_claim(problem_path, problem_text);
            findings.extend(finding);
            let (source, finding) = classify_precondition_source(problem_path, problem_text);
            findings.extend(finding);
            let (definition, finding) = extract_precondition_definition(problem_path, problem_text);
            findings.extend(finding);
            (Some(VerificationClaimKind::Equivalence), source, definition)
        } else {
            let (claim, finding) = classify_verification_claim(problem_path, problem_text);
            findings.extend(finding);
            (claim, None, None)
        };
    let audit = AgentAudit {
        passed: findings.is_empty(),
        scanned_files,
        findings,
    };
    artifacts.write_json("proof-stage/proof-agent/audit.json", &audit)?;
    Ok((
        audit,
        candidate_claim,
        precondition_source,
        precondition_definition,
    ))
}

fn classify_verification_claim(
    path: &str,
    text: &str,
) -> (Option<VerificationClaimKind>, Option<AuditFinding>) {
    const NAME: &str = "generated_verification_claim";
    let uncommented = strip_rocq_comments(text);
    let declarations = rocq_sentences(&uncommented)
        .into_iter()
        .filter(|sentence| {
            let tokens = rocq_identifier_tokens(sentence);
            matches!(tokens.as_slice(), ["Definition", NAME, ..])
        })
        .collect::<Vec<_>>();
    let tokens = declarations
        .first()
        .map(|declaration| rocq_identifier_tokens(declaration));
    let claim = match tokens.as_deref() {
        Some(
            [
                "Definition",
                NAME,
                "Logos",
                "FormalSQL",
                "VerificationConditions",
                "verification_claim_kind",
                "Logos",
                "FormalSQL",
                "VerificationConditions",
                "VerificationEquivalence",
            ],
        ) if declarations.len() == 1 => Some(VerificationClaimKind::Equivalence),
        Some(
            [
                "Definition",
                NAME,
                "Logos",
                "FormalSQL",
                "VerificationConditions",
                "verification_claim_kind",
                "Logos",
                "FormalSQL",
                "VerificationConditions",
                "VerificationCountermodel",
            ],
        ) if declarations.len() == 1 => Some(VerificationClaimKind::FormalCountermodel),
        _ => None,
    };
    if claim.is_some() {
        return (claim, None);
    }

    let line = text
        .find(NAME)
        .map(|offset| text[..offset].lines().count())
        .unwrap_or(1);
    let excerpt = text
        .lines()
        .find(|line| line.contains(NAME))
        .map(str::trim)
        .unwrap_or("missing generated_verification_claim definition")
        .to_owned();
    (
        None,
        Some(AuditFinding {
            path: path.to_owned(),
            line,
            token: NAME.to_owned(),
            excerpt: format!(
                "{excerpt}; unconditional proofs must declare the fully qualified verification_claim_kind type and exactly one direct, fully qualified VerificationEquivalence or VerificationCountermodel constructor"
            ),
        }),
    )
}

fn reject_conditional_verification_claim(path: &str, text: &str) -> Option<AuditFinding> {
    const NAME: &str = "generated_verification_claim";
    let uncommented = strip_rocq_comments(text);
    let declaration = rocq_sentences(&uncommented).into_iter().find(|sentence| {
        let tokens = rocq_identifier_tokens(sentence);
        matches!(tokens.as_slice(), ["Definition", NAME, ..])
    })?;
    let line = text
        .find(NAME)
        .map(|offset| text[..offset].lines().count())
        .unwrap_or(1);
    Some(AuditFinding {
        path: path.to_owned(),
        line,
        token: NAME.to_owned(),
        excerpt: format!(
            "{}; conditional mode has only the precondition-qualified equivalence claim and forbids an unconditional countermodel selector",
            declaration.trim()
        ),
    })
}

fn classify_precondition_source(
    path: &str,
    text: &str,
) -> (Option<PreconditionSource>, Option<AuditFinding>) {
    const NAME: &str = "generated_precondition_source";
    let uncommented = strip_rocq_comments(text);
    let declarations = rocq_sentences(&uncommented)
        .into_iter()
        .filter(|sentence| {
            let tokens = rocq_identifier_tokens(sentence);
            matches!(tokens.as_slice(), ["Definition", NAME, ..])
        })
        .collect::<Vec<_>>();
    let tokens = declarations
        .first()
        .map(|declaration| rocq_identifier_tokens(declaration));
    let source = match tokens.as_deref() {
        Some(
            [
                "Definition",
                NAME,
                "Logos",
                "FormalSQL",
                "VerificationConditions",
                "precondition_source",
                "Logos",
                "FormalSQL",
                "VerificationConditions",
                "PreconditionDerived",
            ],
        ) if declarations.len() == 1 => Some(PreconditionSource::Derived),
        Some(
            [
                "Definition",
                NAME,
                "Logos",
                "FormalSQL",
                "VerificationConditions",
                "precondition_source",
                "Logos",
                "FormalSQL",
                "VerificationConditions",
                "PreconditionExternal",
            ],
        ) if declarations.len() == 1 => Some(PreconditionSource::External),
        _ => None,
    };
    if source.is_some() {
        return (source, None);
    }

    let line = text
        .find(NAME)
        .map(|offset| text[..offset].lines().count())
        .unwrap_or(1);
    let excerpt = text
        .lines()
        .find(|line| line.contains(NAME))
        .map(str::trim)
        .unwrap_or("missing generated_precondition_source definition")
        .to_owned();
    (
        None,
        Some(AuditFinding {
            path: path.to_owned(),
            line,
            token: NAME.to_owned(),
            excerpt: format!(
                "{excerpt}; conditional proofs must declare the fully qualified precondition_source type and exactly one direct, fully qualified PreconditionDerived or PreconditionExternal constructor"
            ),
        }),
    )
}

fn extract_precondition_definition(
    path: &str,
    text: &str,
) -> (Option<String>, Option<AuditFinding>) {
    const NAME: &str = "generated_precondition";
    let uncommented = strip_rocq_comments(text);
    let definitions = rocq_sentences(&uncommented)
        .into_iter()
        .filter(|sentence| {
            let tokens = rocq_identifier_tokens(sentence);
            matches!(
                tokens.as_slice(),
                [
                    "Definition",
                    NAME,
                    "Logos",
                    "FormalSQL",
                    "VerificationConditions",
                    "verification_condition",
                    ..
                ]
            )
        })
        .collect::<Vec<_>>();
    if let [definition] = definitions.as_slice() {
        return (Some(definition.trim().to_owned()), None);
    }

    let line = text
        .lines()
        .position(|line| {
            let tokens = rocq_identifier_tokens(line);
            matches!(tokens.as_slice(), ["Definition", NAME, ..])
        })
        .map(|line| line + 1)
        .unwrap_or(1);
    (
        None,
        Some(AuditFinding {
            path: path.to_owned(),
            line,
            token: NAME.to_owned(),
            excerpt: format!(
                "conditional proofs must contain exactly one direct {NAME} definition; found {}",
                definitions.len()
            ),
        }),
    )
}

fn rocq_identifier_tokens(text: &str) -> Vec<&str> {
    text.split(|character: char| !(character.is_ascii_alphanumeric() || character == '_'))
        .filter(|token| !token.is_empty())
        .collect()
}

fn rocq_sentences(text: &str) -> Vec<&str> {
    let bytes = text.as_bytes();
    let mut sentences = Vec::new();
    let mut start = 0usize;
    let mut index = 0usize;
    let mut in_string = false;
    while index < bytes.len() {
        if bytes[index] == b'"' {
            if in_string && index + 1 < bytes.len() && bytes[index + 1] == b'"' {
                index += 2;
                continue;
            }
            in_string = !in_string;
        } else if !in_string
            && bytes[index] == b'.'
            && bytes
                .get(index + 1)
                .is_none_or(|next| next.is_ascii_whitespace())
        {
            sentences.push(&text[start..=index]);
            start = index + 1;
        }
        index += 1;
    }
    if text[start..]
        .chars()
        .any(|character| !character.is_whitespace())
    {
        sentences.push(&text[start..]);
    }
    sentences
}

fn problem_declares_final_theorem(text: &str, verification_mode: VerificationMode) -> bool {
    let required_name = match verification_mode {
        VerificationMode::SafeUnconditional | VerificationMode::OutcomeUnconditional => {
            "generated_queries_verified"
        }
        VerificationMode::Conditional => "generated_queries_equivalent",
    };
    let uncommented = strip_rocq_comments(text);
    rocq_sentences(&uncommented).into_iter().any(|sentence| {
        let tokens = rocq_identifier_tokens(sentence);
        matches!(tokens.as_slice(), ["Theorem", name, ..] if *name == required_name)
    })
}

fn strip_rocq_comments(text: &str) -> String {
    let bytes = text.as_bytes();
    let mut output = Vec::with_capacity(bytes.len());
    let mut index = 0;
    let mut comment_depth = 0usize;
    let mut in_string = false;
    while index < bytes.len() {
        if comment_depth > 0 {
            if bytes[index..].starts_with(b"(*") {
                comment_depth += 1;
                output.extend_from_slice(b"  ");
                index += 2;
            } else if bytes[index..].starts_with(b"*)") {
                comment_depth -= 1;
                output.extend_from_slice(b"  ");
                index += 2;
            } else {
                output.push(if bytes[index] == b'\n' { b'\n' } else { b' ' });
                index += 1;
            }
            continue;
        }

        if !in_string && bytes[index..].starts_with(b"(*") {
            comment_depth = 1;
            output.extend_from_slice(b"  ");
            index += 2;
        } else if bytes[index] == b'"' {
            output.push(bytes[index]);
            index += 1;
            if in_string && index < bytes.len() && bytes[index] == b'"' {
                output.push(bytes[index]);
                index += 1;
            } else {
                in_string = !in_string;
            }
        } else {
            output.push(bytes[index]);
            index += 1;
        }
    }
    String::from_utf8(output).expect("comment stripping preserves UTF-8 input")
}

fn audit_rocq_text(path: &str, text: &str) -> Vec<AuditFinding> {
    audit_rocq_text_with_mode(path, text, DiagnosticCandidateMode::Problem)
}

fn audit_scratch_rocq_text(path: &str, text: &str) -> Vec<AuditFinding> {
    audit_rocq_text_with_mode(path, text, DiagnosticCandidateMode::Scratch)
}

fn audit_proof_module_rocq_text(path: &str, text: &str) -> Vec<AuditFinding> {
    audit_rocq_text_with_mode(path, text, DiagnosticCandidateMode::Module)
}

fn audit_rocq_text_with_mode(
    path: &str,
    text: &str,
    mode: DiagnosticCandidateMode,
) -> Vec<AuditFinding> {
    const ALWAYS_BANNED_TOKENS: &[&str] = &[
        "Axiom",
        "Axioms",
        "Parameter",
        "Parameters",
        "Hypothesis",
        "Hypotheses",
        "Conjecture",
        "Conjectures",
        "Coercion",
        "Admitted",
        "Admit",
        "admit",
        "sorry",
        "Abort",
        "Fail",
        "Unshelve",
        "Load",
        "LoadPath",
        "Redirect",
        "Print",
        "Write",
        "Chdir",
        "Cd",
        "System",
        "Declare",
        "Unset",
        "bypass_check",
        "exact_no_check",
        "change_no_check",
        "vm_cast_no_check",
        "native_cast_no_check",
        "Notation",
        "Infix",
        "Abbreviation",
        "Reserved",
        "Delimit",
        "Bind",
        "Tactic",
        "Ltac",
        "Ltac2",
    ];
    const FINAL_ONLY_BANNED_TOKENS: &[&str] =
        &["Variable", "Variables", "Context", "Module", "Section"];
    const SCRATCH_ONLY_BANNED_TOKENS: &[&str] = &["Defined"];

    let mut findings = Vec::new();
    for (line_index, line) in text.lines().enumerate() {
        let mode_tokens = match mode {
            DiagnosticCandidateMode::Problem => FINAL_ONLY_BANNED_TOKENS,
            DiagnosticCandidateMode::Module | DiagnosticCandidateMode::Scratch => {
                SCRATCH_ONLY_BANNED_TOKENS
            }
        };
        for token in ALWAYS_BANNED_TOKENS.iter().chain(mode_tokens) {
            if contains_rocq_token(line, token) {
                findings.push(AuditFinding {
                    path: path.to_owned(),
                    line: line_index + 1,
                    token: (*token).to_owned(),
                    excerpt: line.trim().to_owned(),
                });
            }
        }
        if is_untrusted_problem_import(line) {
            findings.push(AuditFinding {
                path: path.to_owned(),
                line: line_index + 1,
                token: "untrusted import".to_owned(),
                excerpt: line.trim().to_owned(),
            });
        }
    }
    let has_opaque_qed = if matches!(
        mode,
        DiagnosticCandidateMode::Module | DiagnosticCandidateMode::Scratch
    ) {
        let uncommented = strip_rocq_comments(text);
        rocq_sentences(&uncommented)
            .into_iter()
            .any(|sentence| rocq_identifier_tokens(sentence).as_slice() == ["Qed"])
    } else {
        true
    };
    if !has_opaque_qed {
        findings.push(AuditFinding {
            path: path.to_owned(),
            line: 1,
            token: "missing Qed".to_owned(),
            excerpt:
                "scratch and proof-module diagnostics must contain at least one opaque Qed subgoal"
                    .to_owned(),
        });
    }
    findings
}

fn is_untrusted_problem_import(line: &str) -> bool {
    let line = line.trim();
    if !["Require", "Import", "Export", "Include"]
        .iter()
        .any(|token| contains_rocq_token(line, token))
    {
        return false;
    }
    if is_agent_proof_module_import(line) {
        return false;
    }
    !TRUSTED_PROBLEM_IMPORT_LINES
        .iter()
        .any(|trusted| trusted == line)
}

fn is_agent_proof_module_import(line: &str) -> bool {
    const PREFIX: &str = "From LogosGenerated.ProofModules Require Import ";
    let Some(body) = line
        .strip_prefix(PREFIX)
        .and_then(|rest| rest.strip_suffix('.'))
    else {
        return false;
    };
    !body.is_empty() && body.split_ascii_whitespace().all(valid_proof_module_stem)
}

fn contains_rocq_token(line: &str, token: &str) -> bool {
    let mut start = 0;
    while let Some(offset) = line[start..].find(token) {
        let token_start = start + offset;
        let token_end = token_start + token.len();
        let before = line[..token_start].chars().next_back();
        let after = line[token_end..].chars().next();
        if before.is_none_or(|c| !is_rocq_ident_char(c))
            && after.is_none_or(|c| !is_rocq_ident_char(c))
        {
            return true;
        }
        start = token_end;
    }
    false
}

fn is_rocq_ident_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_'
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
            "Invocation budget: {} seconds; the trusted final check is reserved separately. Diagnostics are sequential (parallelism {PROOF_AGENT_DIAGNOSTIC_PARALLELISM_MAX}) and share this invocation's wall-clock deadline; there is no completed-check or broker-request quota. End only after exact Problem.v has compile-clean authority (a current problem-mode pass or byte-identity with the active host checkpoint) and contains {final_theorem}, or no coherent progress remains. An unchanged active checkpoint is deliberately not recompiled.\n",
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
    artifacts.write_text("proof-stage/formal-sql/proof-agent-prompt.md", &prompt)
}

fn write_proof_workspace(
    artifacts: &ArtifactWriter,
    input: &VerificationInput,
    ir_input: &VerificationIr,
    lowering: &ProofLoweringReport,
    observation_certificates: &ObservationCertificateReport,
    schema_module: &str,
    queries_module: &str,
    witness_module: &str,
    problem_module: &str,
    goal_module: &str,
    options: &Config,
) -> Result<(ProofWorkspace, PreparedProofAgentContext)> {
    artifacts.write_text("proof-stage/formal-sql/Witness.v", witness_module)?;
    artifacts.write_text("proof-stage/formal-sql/Goal.v", goal_module)?;
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
        &query_shape.text,
        &query_shape.ordered_signatures_text,
        &observation_certificates,
        schema_module,
        queries_module,
        witness_module,
        problem_module,
        goal_module,
    )?;
    let proof_prompt = render_proof_agent_prompt(options.verification_mode, None, None);
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
mod tests {
    use std::collections::{BTreeMap, BTreeSet};
    use std::io::{Read, Write};
    use std::os::unix::ffi::OsStrExt;
    use std::os::unix::fs::{PermissionsExt, symlink};
    use std::os::unix::net::{UnixListener, UnixStream};
    use std::path::{Path, PathBuf};
    use std::process::Command;
    use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

    use logos_ir::ir::SqlStringType;

    use super::{
        AgentRunArtifact, DEFAULT_PROOF_AGENT_COMMAND, DEFAULT_PROOF_AGENT_RESUME_COMMAND,
        DiagnosticBroker, EXPLICITLY_EXCLUDED_HOST_ENVIRONMENT,
        EXPLICITLY_EXCLUDED_HOST_ENVIRONMENT_PREFIXES, FIXED_HOST_LOCALE,
        FORMAL_SQL_DECLARATION_SEARCH_SCRIPT, FORMAL_SQL_DOCKER_AGENT_SCRIPT,
        FORMAL_SQL_GOAL_MODULE, FORMAL_SQL_PROOF_AGENT_PROMPT,
        FORMAL_SQL_ROCQ_CHECK_REQUEST_SCRIPT, FORMAL_SQL_SEMANTIC_PRIMER,
        FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT, PROOF_AGENT_HOST_TMP_DIRECTORY,
        PROOF_AGENT_LAUNCHER_EXPLICIT_ENVIRONMENT, PROOF_AGENT_LAUNCHER_HOST_ENVIRONMENT_ALLOWLIST,
        PROOF_AGENT_LAUNCHER_PATH, PROOF_SOURCE_FILES, ProblemCompileCheckpoint,
        ProofAgentRoundStage, ProofAgentSessionHome, TRUSTED_CHECKER_EXPLICIT_ENVIRONMENT,
        TRUSTED_CHECKER_HOME, TRUSTED_CHECKER_PATH, TRUSTED_PROBLEM_IMPORT_LINES,
        TRUSTED_ROCQ_IMPORT_ROOTS, TRUSTED_ROCQ_IMPORTS, TrustedRocqCheckMode, TrustedRocqImport,
        TrustedRocqRoot, archive_trusted_diagnostic_cache, audit_proof_workspace, audit_rocq_text,
        build_ordered_signatures, canonical_json_sha256, capture_trusted_proof_sources,
        classify_precondition_source, classify_verification_claim, compact_skeleton_forest,
        encode_tree_value, expand_compact_skeleton_node, extract_precondition_definition,
        formal_sql_bound_goal_module, formal_sql_goal_module, is_codex_session_id,
        is_trusted_rocq_environment_failure, load_counterexample_handoff,
        ordered_direct_trusted_rocq_imports, parse_skeleton_tree,
        persist_initial_problem_compile_checkpoint_evidence,
        persist_trusted_environment_preflight_evidence, problem_declares_final_theorem,
        proof_agent_host_tmp_directory, proof_agent_instruction_body, proof_agent_launcher_command,
        proof_agent_launcher_environment_policy, proof_agent_round_budget, proof_backend_status,
        reject_conditional_verification_claim, remove_proof_workspace_for_formal_witness_restart,
        render_proof_agent_prompt, render_proof_agent_resume_command,
        restore_problem_compile_checkpoint, sha256_hex, snapshot_proof_workspace,
        static_prompt_and_primer_bytes, strip_rocq_comments, trusted_checker_environment_policy,
        trusted_rocq_check_command, validate_authority_closure, validate_compacted_skeleton_forest,
        validate_proof_agent_context, write_proof_agent_context,
        write_trusted_proof_agent_launcher, write_trusted_rocq_checker,
    };
    use crate::artifacts::ArtifactWriter;
    use crate::core::{
        FormalAttribute, FormalAttributeType, FormalFunctionTerm, FormalQueryExpr,
        FormalScalarExpr, FormalSchema, FormalTable, FormalTableConstraints,
        FormalUniqueIndexConstraint, LoweredProgram, LoweredQuery, LoweringStatus, SqlEnvironment,
        SqlTimeZone, VerificationInput, VerificationMode,
        emit_rocq_query_expr_proof_module_for_mode, query_expr_output_signature,
    };
    use crate::engine::config::Config;
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
            transform_only: false,
            typed_witness_empty_audit: false,
            disable_counterexample_search: false,
            llm_assessment_only: false,
            reuse_llm_assessment: false,
            force_llm_assessment: false,
            llm_assessment_cache_dir: root.join("assessment-cache"),
            proposal_command: String::new(),
            proposal_resume_command: String::new(),
            max_counterexample_rounds: 1,
            postgres_url: None,
            statement_timeout_ms: 1_000,
            sql_time_zone: SqlTimeZone::utc(),
            sql_environment: SqlEnvironment::default(),
            verification_mode: VerificationMode::OutcomeUnconditional,
            run_proof_agent: true,
            proof_agent_command: String::new(),
            proof_agent_resume_command: String::new(),
            proof_agent_memory_limit_mib: 512,
            proof_agent_storage_limit_mib: 512,
            proof_agent_timeout_seconds: 60,
            proof_check_timeout_seconds: 60,
            proof_docker_image: "test-image".to_owned(),
            proof_rocq_opam_switch: None,
            logos_repo_root: None,
        }
    }

    #[test]
    fn typed_witness_values_render_exact_string_typmods_and_numeric_carriers() {
        assert_eq!(
            super::rocq_witness_string_typmod(SqlStringType::Varchar { length: Some(16) }),
            "StringVarcharN 16"
        );
        assert_eq!(
            super::rocq_witness_value(
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
            super::rocq_witness_value(
                &FormalWitnessValue::NumericNaN,
                FormalAttributeType::Numeric,
            )
            .unwrap(),
            "Value_numeric (Some NumericNaN)"
        );
        assert_eq!(
            super::rocq_witness_value(
                &FormalWitnessValue::Float64Bits((-0.0_f64).to_bits()),
                FormalAttributeType::Double,
            )
            .unwrap(),
            "Value_double (Some (Float64OfBits (9223372036854775808)%Z))"
        );
        assert_eq!(
            super::rocq_witness_value(
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

        let modules = super::formal_sql_witness_modules(&schema, Some(&snapshot)).unwrap();
        let data = modules.data.as_ref().unwrap();
        assert!(data.contains("Lemma generated_witness_instance_cardinal"));
        assert!(!data.contains("generated_witness_table_0_attributes"));
        assert!(data.contains("Definition generated_witness_table_1_attributes"));
        assert!(!data.contains("Definition generated_witness_table_0_rows"));
        assert!(data.contains("Definition generated_witness_table_1_rows"));
        assert!(!data.contains("generated_witness_table_0_instance_cardinal"));
        assert!(data.contains("generated_witness_table_1_instance_cardinal"));
        assert!(data.contains("WitnessTable (Rel (\"nonempty_table\"))"));
        assert!(modules.witness.contains("From Stdlib Require Import List String."));
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
        assert!(modules.constraint_modules.iter().any(|(_, source)| source
            .contains("generated_witness_table_constraint_1_conforms")));
        let table_assembly = modules
            .constraint_modules
            .iter()
            .find(|(name, _)| name == "TableConstraint0001")
            .map(|(_, source)| source)
            .expect("populated table assembly module");
        assert!(
            table_assembly.contains("rewrite Schema.generated_table_constraint_1_unique_indexes")
        );
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
            frontiers.iter().any(|frontier| {
                frontier["statementIndex"] == 1 && frontier["rolePath"] == "root"
            })
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
                name: format!(
                    "wide_ordered_signature_column_{index:04}_with_exact_position_metadata"
                ),
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

        let text =
            build_ordered_signatures(&source, &target).expect("build wide signature navigation");
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
            super::PROOF_AGENT_SCRATCH_PERSISTENCE_POLICY
                .contains("exact_digest_checked_promotion")
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
            latest_problem =
                format!("Definition checkpoint_{sequence} : True := I.\n").into_bytes();
            latest_sha256 = sha256_hex(&latest_problem);
            std::fs::write(stage.join("Problem.v"), &latest_problem)
                .expect("write staged Problem.v");
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
            "#!/usr/bin/env bash\nset -euo pipefail\ncp \"$LOGOS_PROOF_WORKDIR/ProofModules/CoreFacts.v\" \"$LOGOS_TRUSTED_ROCQ_CACHE_DIR/ProofModules/CoreFacts.v\"\nprintf 'host compiler object\\n' >\"$LOGOS_TRUSTED_ROCQ_CACHE_DIR/ProofModules/CoreFacts.vo\"\nprintf 'CoreFacts.v\\n' >\"$LOGOS_TRUSTED_ROCQ_CACHE_DIR/ProofModules/ORDER\"\ncd \"$LOGOS_TRUSTED_ROCQ_CACHE_DIR\"\nsha256sum ProofModules/ORDER ProofModules/CoreFacts.v ProofModules/CoreFacts.vo >SHA256SUMS\n",
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
                "#!/usr/bin/env bash\nset -euo pipefail\nmv -T \"$LOGOS_TRUSTED_ROCQ_CACHE_DIR\" \"{}\"\nmkdir \"{}\"\nexit 137\n",
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
            "#!/usr/bin/env bash\nset -euo pipefail\ncp \"$LOGOS_PROOF_WORKDIR/ProofModules/LateFacts.v\" \"$LOGOS_TRUSTED_ROCQ_CACHE_DIR/ProofModules/LateFacts.v\"\nprintf 'host compiler object\\n' >\"$LOGOS_TRUSTED_ROCQ_CACHE_DIR/ProofModules/LateFacts.vo\"\nprintf 'LateFacts.v\\n' >>\"$LOGOS_TRUSTED_ROCQ_CACHE_DIR/ProofModules/ORDER\"\ncd \"$LOGOS_TRUSTED_ROCQ_CACHE_DIR\"\nsha256sum ProofModules/ORDER ProofModules/CoreFacts.v ProofModules/CoreFacts.vo ProofModules/LateFacts.v ProofModules/LateFacts.vo >SHA256SUMS\nexit 143\n",
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
        assert!(
            !feedback.contains(&"x".repeat(super::TRUSTED_CHECK_REPAIR_FEEDBACK_STREAM_MAX_BYTES))
        );
        assert!(
            !feedback.contains(&"y".repeat(super::TRUSTED_CHECK_REPAIR_FEEDBACK_STREAM_MAX_BYTES))
        );
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

        let hydrated = super::hydrate_round_scratch(&proof, &stage)
            .expect("hydrate an empty scratch workspace");
        assert_eq!(hydrated.file_count, 0);
        assert_eq!(hydrated.total_bytes, 0);
        let stage_metadata = std::fs::symlink_metadata(stage.join("scratch"))
            .expect("inspect materialized stage scratch directory");
        assert!(stage_metadata.file_type().is_dir());
        assert!(!stage_metadata.file_type().is_symlink());
        assert_eq!(stage_metadata.permissions().mode() & 0o777, 0o700);

        let persisted = super::persist_round_scratch(&stage, &proof)
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

        let staged = super::validated_scratch_tree_with_policy(
            &stage.join("scratch"),
            super::UnsupportedScratchFilePolicy::Drop,
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

        let persisted = super::persist_round_scratch(&stage, &proof)
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

        let error = super::persist_round_scratch(&stage, &proof)
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
        super::materialize_agent_output_file(
            &stage,
            "agent-stdout",
            &legacy_destination,
            legacy_bytes,
        )
        .expect("materialize legacy launcher output");
        assert_eq!(
            std::fs::read(&legacy_destination).expect("read legacy output"),
            legacy_bytes
        );

        std::fs::write(stage.join("agent-stdout"), b"")
            .expect("write empty protected staged output");
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

        let hydrated = super::hydrate_round_scratch(&proof, &stage)
            .expect("hydrate the 63-file scratch state");
        assert_eq!(hydrated.file_count, 63);
        std::fs::write(stage.join("scratch/fresh.v"), fresh)
            .expect("write the round-local fresh candidate");

        let core_state =
            super::persist_successful_scratch_candidate(&proof, Path::new("scratch/core.v"), core)
                .expect("promote the matching persistent core");
        assert_eq!(core_state.file_count, 63);
        assert!(!persistent_scratch.join("core.v").exists());
        assert_eq!(
            std::fs::read(persistent_scratch.join("checked/core.v"))
                .expect("read promoted checked core"),
            core
        );

        let fresh_state = super::persist_successful_scratch_candidate(
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

        let persisted = super::persist_round_scratch(&stage, &proof)
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
        std::fs::create_dir_all(&persistent_scratch)
            .expect("create file-pressure persistence root");
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

        let hydrated = super::hydrate_round_scratch(&proof, &stage)
            .expect("hydrate the 63-file pressure state");
        assert_eq!(hydrated.file_count, 63);
        std::fs::write(stage.join("scratch/fresh.v"), fresh)
            .expect("write file-pressure fresh candidate");
        super::persist_successful_scratch_candidate(&proof, Path::new("scratch/core.v"), core)
            .expect("promote the matching file-pressure core");
        let promoted = super::persist_successful_scratch_candidate(
            &proof,
            Path::new("scratch/fresh.v"),
            fresh,
        )
        .expect("persist the file-pressure fresh candidate");
        assert_eq!(promoted.file_count, 64);
        std::fs::write(stage.join("scratch/core.v"), divergent)
            .expect("write divergent file-pressure WIP");

        let persisted = super::persist_round_scratch(&stage, &proof)
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
        std::fs::create_dir_all(&persistent_scratch)
            .expect("create byte-pressure persistence root");
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

        let hydrated =
            super::hydrate_round_scratch(&proof, &stage).expect("hydrate byte-pressure state");
        assert_eq!(hydrated.total_bytes, 9 * 400 * 1024);
        std::fs::write(stage.join("scratch/fresh.v"), &fresh)
            .expect("write byte-pressure fresh candidate");
        super::persist_successful_scratch_candidate(&proof, Path::new("scratch/core.v"), &core)
            .expect("promote the matching byte-pressure core");
        let promoted = super::persist_successful_scratch_candidate(
            &proof,
            Path::new("scratch/fresh.v"),
            &fresh,
        )
        .expect("persist the byte-pressure fresh candidate");
        assert_eq!(promoted.total_bytes, (9 * 400 + 300) * 1024);
        std::fs::write(stage.join("scratch/core.v"), &divergent)
            .expect("write divergent byte-pressure WIP");

        let persisted = super::persist_round_scratch(&stage, &proof)
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

        let hydrated = super::hydrate_round_scratch(&proof, &stage)
            .expect("hydrate the full replacement state");
        assert_eq!(hydrated.file_count, 64);
        std::fs::remove_file(stage.join("scratch/obsolete/deep/old.v"))
            .expect("delete obsolete staged WIP");
        std::fs::create_dir_all(stage.join("scratch/replacement"))
            .expect("create replacement stage directory");
        std::fs::write(stage.join("scratch/replacement/current.v"), replacement)
            .expect("write current replacement WIP");

        let persisted = super::persist_round_scratch(&stage, &proof)
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
        let existing = super::validated_scratch_tree(&scratch).expect("snapshot live scratch");
        let new_checked = b"Lemma checked_new : True. Proof. exact I. Qed.\n";
        let new_wip = b"Lemma wip_new : True. Proof. exact I. Qed.\n";
        let selected = BTreeMap::from([
            (
                PathBuf::from("checked/core.v"),
                super::ScratchFileSnapshot {
                    relative_path: PathBuf::from("checked/core.v"),
                    bytes: new_checked.to_vec(),
                },
            ),
            (
                PathBuf::from("new.v"),
                super::ScratchFileSnapshot {
                    relative_path: PathBuf::from("new.v"),
                    bytes: new_wip.to_vec(),
                },
            ),
        ]);

        let error = super::replace_scratch_snapshots_with_pre_exchange_hook(
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
                    .starts_with(super::SCRATCH_TRANSACTION_PREFIX))
        );

        let existing = super::validated_scratch_tree(&scratch)
            .expect("snapshot retained scratch before retry");
        let published = super::replace_scratch_snapshots(&scratch, existing, selected)
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

        super::hydrate_round_scratch(&proof, &stage)
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
        let staged_tree = super::validated_scratch_tree(&stage.join("scratch"))
            .expect("validate the structurally sound staged directory tree");
        assert_eq!(staged_tree.directories.len(), 64);

        let persisted = super::persist_round_scratch(&stage, &proof)
            .expect("retain the checked-plus-staged directory union");
        assert_eq!(persisted.file_count, 64);
        assert_eq!(
            std::fs::read(persistent_scratch.join("checked/core.v"))
                .expect("read preserved checked directory-pressure snapshot"),
            checked
        );
        let persisted_tree = super::validated_scratch_tree(&persistent_scratch)
            .expect("validate compacted directory-pressure tree");
        assert_eq!(persisted_tree.directories.len(), 65);
        assert_eq!(
            persisted_tree
                .files
                .iter()
                .filter(|snapshot| !super::is_checked_scratch_snapshot(&snapshot.relative_path))
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
        let before = super::scratch_workspace_state(&persistent_scratch)
            .expect("inspect promotion-pressure initial state");
        assert_eq!(before.total_bytes, (300 + 400 + 8 * 400) * 1024);

        let promoted = super::persist_successful_scratch_candidate(
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
        let before = super::scratch_workspace_state(&persistent_scratch)
            .expect("inspect checked-only saturation");
        assert_eq!(before.total_bytes, 4 * 1024 * 1024);

        let retained = super::persist_successful_scratch_candidate(
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
        super::hydrate_round_scratch(&proof, &stage)
            .expect("hydrate stage-overflow checked snapshot");
        for index in 0..64 {
            std::fs::write(stage.join(format!("scratch/overflow-{index}.txt")), b"x")
                .expect("write aggregate stage-overflow file");
        }
        assert_eq!(
            super::validated_scratch_tree(&stage.join("scratch"))
                .expect("validate all staged files")
                .files
                .len(),
            65
        );

        let persisted = super::persist_round_scratch(&stage, &proof)
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

        let persisted = super::persist_round_scratch(&stage, &proof)
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

        let persisted = super::persist_round_scratch(&stage, &proof)
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

        let persisted = super::persist_round_scratch(&stage, &proof)
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
        let persisted = super::persist_round_scratch(&stage, &proof)
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
        super::hydrate_round_scratch(&proof, &next_stage).expect("hydrate retained scratch");
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
        std::fs::write(stage.join("Problem.v"), forbidden_problem)
            .expect("write forbidden Problem.v");
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
        let rejected_dir = artifacts
            .join("proof-stage/proof-agent/rounds/02/rejected-diagnostic-source-audits/01");
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
        let accepted_audit: serde_json::Value =
            serde_json::from_slice(
                &std::fs::read(artifacts.join(
                    "proof-stage/proof-agent/rounds/02/interactive-diagnostics/01/audit.json",
                ))
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
        let accepted_json =
            serde_json::to_value(accepted_record).expect("serialize accepted audit");
        let rejected_json =
            serde_json::to_value(rejected_record).expect("serialize rejected audit");
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
        let root = artifacts.root().join(
            "proof-stage/proof-agent/workspace-generations/0001/trusted-environment-preflight",
        );
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
        let checkpoint = ProblemCompileCheckpoint {
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
            super::parse_case_process_supervisor_pid(std::ffi::OsStr::new("1"))
                .expect("minimum positive pid"),
            1
        );
        assert_eq!(
            super::parse_case_process_supervisor_pid(std::ffi::OsStr::new("4294967295"))
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
                super::parse_case_process_supervisor_pid(std::ffi::OsStr::from_bytes(malformed))
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
        let socket_directory = super::ProofDiagnosticSocketDirectory::create(artifacts.root(), 97)
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
            .push(super::CompactSkeletonNode("Unused".to_owned(), Vec::new()));
        assert!(validate_compacted_skeleton_forest(&unreachable, &trees, "test").is_err());

        let mut wrong_digest = pristine;
        wrong_digest.expanded_trees_sha256 = "0".repeat(64);
        assert!(validate_compacted_skeleton_forest(&wrong_digest, &trees, "test").is_err());
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

    fn ordered_theory_paths(
        order: fn(&TrustedRocqImport) -> Option<usize>,
        ext: &str,
    ) -> Vec<String> {
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
        let source = include_str!("proof_stage.rs");
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
        let manual_review_terminal = source[handoff_resolution..]
            .find("ProofHandoffResolution::NeedsManualReview(reason)")
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
        assert!(handoff_resolution < manual_review_terminal);
        assert!(manual_review_terminal < fatal_resume_break);
    }

    #[test]
    fn codex_session_id_is_validated_and_bound_into_resume_command() {
        let session_id = "019f7ed2-b56c-77a0-8ab5-31d110b90e6b";
        assert!(is_codex_session_id(session_id));
        let command =
            render_proof_agent_resume_command(DEFAULT_PROOF_AGENT_RESUME_COMMAND, session_id)
                .expect("valid resume command");
        assert!(command.starts_with("codex exec resume "));
        assert!(command.contains("--json --model gpt-5.6-sol"));
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
            render_proof_agent_resume_command("codex exec resume {session_id}", "not-a-uuid")
                .is_err()
        );
        assert!(
            render_proof_agent_resume_command(
                "codex exec resume --last",
                "019f7ed2-b56c-77a0-8ab5-31d110b90e6b",
            )
            .is_err()
        );
    }

    #[test]
    fn proof_run_artifact_preserves_cumulative_and_incremental_usage() {
        let incremental = LlmUsage::from_counts(120, 100, 30).unwrap();
        let cumulative = LlmUsage::from_counts(220, 180, 50).unwrap();
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
            audit: binding(
                "proof-stage/proof-agent/rounds/02/interactive-diagnostics/01/audit.json",
            ),
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
        let log = AgentRunLog {
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
            usage: Some(incremental.clone()),
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
        };

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
        let mut configuration =
            super::base_proof_agent_configuration(&proof_test_config(&root), None)
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
            FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT
                .contains("unset LOGOS_TRUSTED_ENVIRONMENT_PREFLIGHT")
        );
        assert!(FORMAL_SQL_TRUSTED_ROCQ_CHECK_SCRIPT.contains(
            "# Every agent-controlled module is compiled in the same empty-root sandbox"
        ));
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
            TrustedRocqCheckMode::ProblemDiagnostic {
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
                        TrustedRocqCheckMode::Full,
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

        let shadowable =
            "Definition generated_precondition : verification_condition := ConditionTrue.";
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
        assert!(
            FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("-v \"$LOGOS_REPO_ROOT\":/workspace/logos:ro")
        );
        assert!(!FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains(
            "\"$LOGOS_REPO_ROOT/vendor/FormalSQL\":/workspace/logos/vendor/FormalSQL:ro"
        ));
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
        assert!(
            !FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("publish_stage_file \"$AGENT_STAGE/scratch")
        );
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
        assert!(
            FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("-v \"$HANDOFF_INCOMING\":/handoff-export:rw")
        );
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
            FORMAL_SQL_DOCKER_AGENT_SCRIPT
                .contains("\"$(stat -c '%s' \"$HANDOFF_INCOMING\")\" -gt")
        );
        assert!(
            FORMAL_SQL_DOCKER_AGENT_SCRIPT
                .contains("\"$(stat -c '%a' \"$HANDOFF_INCOMING\")\" != 600")
        );
        assert!(
            FORMAL_SQL_DOCKER_AGENT_SCRIPT
                .contains("mv -T \"$HANDOFF_INCOMING\" \"$HANDOFF_ARCHIVE\"")
        );
        assert!(
            FORMAL_SQL_DOCKER_AGENT_SCRIPT
                .contains("extract_agent_archive \\\n  \"$HANDOFF_ARCHIVE\"")
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
        assert!(
            FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains("forbidden proof-agent problem export path")
        );
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
        assert!(FORMAL_SQL_DOCKER_AGENT_SCRIPT.contains(
            "rm -rf -- \"$dst/config.toml\" \"$dst/auth.json\" \"$dst/credentials.json\""
        ));
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
            std::fs::read_to_string(trusted_cache.join("VALID"))
                .expect("read restored cache marker"),
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
            std::fs::read_to_string(published_live.join("NEW"))
                .expect("read published cache marker"),
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
        assert!(
            FORMAL_SQL_ROCQ_CHECK_REQUEST_SCRIPT
                .contains("result.get(\"compilePassed\") is True or result.get(key) is not None")
        );
        assert!(
            FORMAL_SQL_ROCQ_CHECK_REQUEST_SCRIPT.contains(
                "f\"{mode} compile was incorrectly classified as a Problem.v checkpoint\""
            )
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
            "--candidate scratch/core-bridge.v",
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
        assert!(
            !FORMAL_SQL_PROOF_AGENT_PROMPT.contains("bash run-rocq-check.sh --timeout-seconds 30")
        );
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
            String::from_utf8_lossy(&incomplete.stderr)
                .contains("response identity mismatch for mode")
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
            static_prompt_and_primer_bytes().unwrap(),
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
            std::fs::read_to_string(
                root.join("proof-stage/formal-sql/search-rocq-declarations.py")
            )
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
        std::fs::create_dir_all(formal_root.join("ProofModules"))
            .expect("create formal module root");
        std::fs::create_dir_all(formal_root.join("WitnessModules"))
            .expect("create formal witness module root");
        std::fs::create_dir_all(cache_root.join("ProofModules"))
            .expect("create trusted module cache");
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
        ] {
            std::fs::write(formal_root.join(name), bytes).expect("write live trusted source");
            std::fs::write(cache_root.join(name), bytes).expect("write cached trusted source");
        }
        for (name, bytes) in [
            ("Schema.vo", b"schema object".as_slice()),
            ("Queries.vo", b"queries object".as_slice()),
            ("WitnessData.vo", b"witness data object".as_slice()),
            ("Witness.vo", b"witness object".as_slice()),
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
        let trusted =
            write_trusted_proof_agent_launcher(&artifacts).expect("write trusted launcher");
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
        assert!(super::audit_scratch_rocq_text("scratch/general.v", &source).is_empty());
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

        let assumption_findings = super::audit_scratch_rocq_text(
            "scratch/assumption.v",
            "Parameter magic : forall P : Prop, P.\nLemma result : True. Proof. exact I. Qed.\n",
        );
        assert!(
            assumption_findings
                .iter()
                .any(|finding| finding.token == "Parameter")
        );
        let missing_qed = super::audit_scratch_rocq_text(
            "scratch/no-result.v",
            "Definition only_a_definition : True := I.\n",
        );
        assert!(
            missing_qed
                .iter()
                .any(|finding| finding.token == "missing Qed")
        );
        let untrusted = super::audit_scratch_rocq_text(
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
                super::validate_proof_module_candidate_path(accepted).is_ok(),
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
                super::validate_proof_module_candidate_path(rejected).is_err(),
                "expected invalid module path {rejected}"
            );
        }

        let source = format!(
            "{}\nFrom LogosGenerated.ProofModules Require Import Core Proof20_GroupLift.\nLemma exported_fact : True. Proof. exact I. Qed.\n",
            TRUSTED_PROBLEM_IMPORT_LINES.join("\n")
        );
        assert!(super::audit_proof_module_rocq_text("ProofModules/Consumer.v", &source).is_empty());
        assert!(audit_rocq_text("Problem.v", &source).is_empty());
        let malformed = super::audit_proof_module_rocq_text(
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
                super::audit_proof_module_rocq_text("ProofModules/BadImport.v", forbidden)
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
        super::persist_successful_proof_module_candidate(
            &root,
            Path::new("ProofModules/Core.v"),
            first,
        )
        .expect("persist first checked module");
        super::persist_successful_proof_module_candidate(
            &root,
            Path::new("ProofModules/Core.v"),
            first,
        )
        .expect("accept byte-identical checked module");
        let replacement = super::persist_successful_proof_module_candidate(
            &root,
            Path::new("ProofModules/Core.v"),
            b"Lemma changed : True. Proof. exact I. Qed.\n",
        )
        .expect_err("checked module names must be immutable")
        .to_string();
        assert!(replacement.contains("immutable"));

        let pending = super::PendingProofModulePublication::prepare(
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
}
