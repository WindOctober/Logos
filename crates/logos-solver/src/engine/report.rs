use serde::{Deserialize, Serialize};
use std::time::Instant;

use crate::core::{SqlEnvironment, VerificationMode};
use crate::proposal::{Candidate, Decision};
use crate::usage::{LlmUsage, UsageError};
use crate::validation::{SchemaMismatch, ValidationWarning, WitnessCheck};

#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SolverReport {
    pub outcome: SolverOutcome,
    pub reason: String,
    pub rounds: Vec<ProposalRound>,
    pub counterexample: Option<Evidence>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub proof: Option<ProofReport>,
    pub log_dir: String,
    pub elapsed_ms: u128,
    pub llm_usage: LlmUsage,
}

impl SolverReport {
    pub fn finished(
        outcome: SolverOutcome,
        reason: String,
        rounds: Vec<ProposalRound>,
        counterexample: Option<Evidence>,
        proof: Option<ProofReport>,
        log_dir: String,
        started: Instant,
    ) -> Result<Self, UsageError> {
        let mut report = Self {
            outcome,
            reason,
            rounds,
            counterexample,
            proof,
            log_dir,
            elapsed_ms: started.elapsed().as_millis(),
            llm_usage: LlmUsage::zero(),
        };
        report.reconcile_llm_usage()?;
        Ok(report)
    }

    pub fn reconcile_llm_usage(&mut self) -> Result<(), UsageError> {
        let counterexample_usage = self.rounds.iter().filter_map(|round| {
            round
                .assessment
                .provider
                .as_ref()
                .and_then(|provider| provider.usage.as_ref())
        });
        let proof_usage = self.proof.iter().flat_map(|proof| {
            proof
                .proof_agent_rounds
                .iter()
                .filter_map(|round| round.usage.as_ref())
        });
        self.llm_usage = LlmUsage::checked_sum(counterexample_usage.chain(proof_usage))?;
        Ok(())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum SolverOutcome {
    SafeUnconditional,
    OutcomeUnconditional,
    ConditionalDerived,
    ConditionalExternal,
    NotEquivalent,
    TransformOnly,
    EquivalenceVerificationIncomplete,
    NeedsManualReview,
    LlmAssessmentOnly,
}

#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SearchReport {
    pub outcome: SearchStatus,
    pub reason: String,
    pub rounds: Vec<ProposalRound>,
    pub counterexample: Option<Evidence>,
    pub elapsed_ms: u128,
    pub llm_usage: LlmUsage,
    /// In-memory typed database captured before the PostgreSQL materialization
    /// transaction rolled back.  The canonical JSON is written as a separate
    /// artifact; reports retain only ordinary validation metadata.
    #[serde(skip)]
    pub formal_witness_snapshot: Option<crate::validation::FormalWitnessSnapshot>,
}

impl SearchReport {
    pub fn finished(
        outcome: SearchStatus,
        reason: String,
        rounds: Vec<ProposalRound>,
        counterexample: Option<Evidence>,
        started: Instant,
    ) -> Result<Self, UsageError> {
        let llm_usage = LlmUsage::checked_sum(rounds.iter().filter_map(|round| {
            round
                .assessment
                .provider
                .as_ref()
                .and_then(|provider| provider.usage.as_ref())
        }))?;
        Ok(Self {
            outcome,
            reason,
            rounds,
            counterexample,
            elapsed_ms: started.elapsed().as_millis(),
            llm_usage,
            formal_witness_snapshot: None,
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum SearchStatus {
    Skipped,
    MaybeEquivalent,
    NotEquivalent,
    NeedsManualReview,
    LlmAssessmentOnly,
}

#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ProposalRound {
    pub round: usize,
    pub assessment: LlmAssessmentLog,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub proposal: Option<Candidate>,
    pub validation: Option<WitnessCheck>,
}

#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct RoundReport {
    pub round: usize,
    pub assessment: LlmAssessmentLog,
    pub validation: Option<ValidationLog>,
    pub outcome: RoundOutcome,
    pub error: Option<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum RoundOutcome {
    AssessmentOnly,
    NoCandidate,
    ManualReview,
    CandidateRejected,
    FormalWitnessPrepared,
}

#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct LlmAssessmentLog {
    pub round: usize,
    pub cache: LlmAssessmentCacheLog,
    pub prompt_path: String,
    pub assessment_path: String,
    pub raw_output_path: String,
    pub proposal_path: String,
    pub candidate_path: String,
    pub prompt_bytes: usize,
    pub raw_output_bytes: usize,
    pub decision: Option<Decision>,
    pub provider: Option<LlmProviderLog>,
    pub parse: LlmParseLog,
}

#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct LlmAssessmentCacheLog {
    pub status: LlmAssessmentCacheStatus,
    pub path: String,
    pub read_elapsed_ms: Option<u128>,
    pub write_elapsed_ms: Option<u128>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum LlmAssessmentCacheStatus {
    Generated,
    Reused,
    NotWritten,
}

#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct LlmProviderLog {
    pub command: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub session_id: Option<String>,
    pub session_resumed: bool,
    pub started_ms_since_epoch: u128,
    pub elapsed_ms: u128,
    pub success: bool,
    pub exit_code: Option<i32>,
    pub stdout_bytes: usize,
    pub stderr_bytes: usize,
    pub stderr_path: String,
    pub events_path: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub usage: Option<LlmUsage>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub usage_error: Option<String>,
}

#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct LlmParseLog {
    pub elapsed_ms: u128,
    pub success: bool,
    pub error: Option<String>,
}

#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ValidationLog {
    pub started_ms_since_epoch: u128,
    pub elapsed_ms: u128,
    pub result: ValidationOutcome,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub warnings: Vec<ValidationWarning>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum ValidationOutcome {
    WitnessMaterialized,
    #[cfg(test)]
    DataDifference,
    #[cfg(test)]
    RowSequenceDifference,
    #[cfg(test)]
    InconclusiveObservation,
    #[cfg(test)]
    OutputSchemaMismatch,
    #[cfg(test)]
    NoDifference,
    ValidationError,
}

#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase", tag = "kind")]
pub enum Evidence {
    OutputSchemaMismatch {
        mismatch: SchemaMismatch,
    },
    FormalSqlCountermodel {
        problem_path: String,
        goal_path: String,
        problem_sha256: String,
        context_manifest_sha256: String,
        authority_closure_sha256: String,
        trusted_check_exit_code: i32,
        theorem: String,
    },
}

#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ProofReport {
    pub backend: Backend,
    pub sql_environment: SqlEnvironment,
    pub verification_mode: VerificationMode,
    pub backend_status: BackendStatus,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub certification: Option<CertificationLevel>,
    pub status_reason: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub proof_workspace: Option<ProofWorkspace>,
    pub proof_agent_configuration: ProofAgentConfiguration,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub proof_agent: Option<AgentRunLog>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub proof_agent_rounds: Vec<AgentRunLog>,
    /// Host-authored replacements of the generated proof workspace.  Session
    /// generations can also change merely to bound transcript growth, so they
    /// are not semantic evidence that Schema/Queries/Witness changed.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub proof_workspace_transitions: Vec<ProofWorkspaceTransition>,
    pub proof_search_timed_out: bool,
    /// Whether the final authoritative cumulative Codex usage snapshot covers
    /// every proof-agent round.  This is accounting metadata and is independent
    /// of trusted Rocq certification.
    pub usage_complete: bool,
    pub elapsed_ms: u128,
    pub llm_usage: LlmUsage,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum ProofWorkspaceTransitionReason {
    FixedWitnessReplacement,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ProblemCompileCheckpointEvidence {
    pub workspace_generation: usize,
    pub path: String,
    pub sha256: String,
    pub round: usize,
    pub sequence: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct TrustedDiagnosticCacheEvidence {
    pub workspace_generation: usize,
    /// Create-once archive manifest under this workspace generation. Archived
    /// caches are report authority only and are never supplied to a later
    /// witness workspace or trusted checker invocation.
    pub manifest_path: String,
    pub manifest_sha256: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ProofWorkspaceTransition {
    pub after_round: usize,
    pub from_workspace_generation: usize,
    pub to_workspace_generation: usize,
    pub reason: ProofWorkspaceTransitionReason,
    pub triggering_handoff_sha256: String,
    pub from_context_manifest_sha256: String,
    pub to_context_manifest_sha256: String,
    pub from_trusted_diagnostic_cache: TrustedDiagnosticCacheEvidence,
    pub new_trusted_environment_preflight: TrustedCheckInvocation,
    pub new_initial_problem_compile_checkpoint: ProblemCompileCheckpointEvidence,
}

#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ProofWorkspace {
    pub generated_module_dir: String,
    pub problem_path: String,
    pub proof_modules_dir: String,
    pub scratch_dir: String,
    pub goal_path: String,
    pub witness_path: String,
    pub source_sql_path: String,
    pub target_sql_path: String,
    pub query_shape_path: String,
    pub ordered_signatures_path: String,
    pub observation_certificates_path: String,
    pub semantic_primer_path: String,
    pub declaration_search_path: String,
    pub context_manifest_path: String,
    pub proof_agent_prompt_path: String,
    pub rocq_check_script_path: String,
    pub docker_agent_script_path: String,
}

#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ProofAgentConfiguration {
    pub enabled: bool,
    pub command: String,
    pub resume_command: String,
    pub timeout_seconds: u64,
    pub trusted_check_timeout_seconds: u64,
    pub memory_limit_mib: u64,
    pub diagnostic_timeout_policy: String,
    pub diagnostic_transport: String,
    pub diagnostic_cache_policy: String,
    pub diagnostic_budget_policy: String,
    pub diagnostic_checker_parallelism_max: usize,
    pub diagnostic_checker_scheduling_policy: String,
    pub compile_checkpoint_policy: String,
    pub scratch_persistence_policy: String,
    pub scratch_allowed_extensions: Vec<String>,
    /// Aggregate writable footprint available to one untrusted proof-agent
    /// container. Individual generated files and navigation artifacts do not
    /// carry smaller framework-defined size limits.
    pub writable_storage_limit_bytes: u64,
    pub writable_storage_policy: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub diagnostic_cache_manifest_path: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub diagnostic_cache_manifest_sha256: Option<String>,
    /// Maximum number of unsuccessful turns retained in one Codex session.
    /// A fresh session then continues from the audited Problem.v snapshot and
    /// bounded host feedback, preventing transcript growth from dominating
    /// proof search.
    pub session_restart_after_failed_rounds: usize,
    /// Host-enforced filesystem policy for Codex session state. Each bounded
    /// session generation receives a distinct CODEX_HOME; earlier generation
    /// homes are never mounted into a later generation.
    pub session_home_policy: String,
    /// Exact host-process environment projection used before the trusted
    /// checker's `/usr/bin/timeout /usr/bin/bash` entry point. Values that may
    /// contain credentials are represented by name only.
    pub trusted_checker_environment_policy: LaunchEnvironmentPolicy,
    /// Exact host-process environment projection used before the proof-agent
    /// Docker launcher's `/usr/bin/bash` entry point.
    pub proof_agent_launcher_environment_policy: LaunchEnvironmentPolicy,
    pub docker_image: String,
    pub static_prompt_and_primer_bytes: usize,
    /// The create-once preflight for workspace generation one. Later
    /// generation preflights are carried by `ProofWorkspaceTransition` so the
    /// initial evidence is never overwritten by a fixed-witness restart.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub trusted_environment_preflight: Option<TrustedCheckInvocation>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub context: Option<ProofAgentContext>,
}

/// Report-facing description of a fail-closed process environment projection.
/// `env_clear` excludes every ambient name first; only the fixed, host-
/// allowlisted, and call-site contract names below can then be restored.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct LaunchEnvironmentPolicy {
    pub schema_version: u32,
    pub inherited_environment_cleared: bool,
    pub fixed_variables: Vec<String>,
    pub host_environment_allowlist: Vec<String>,
    pub explicit_contract_variables: Vec<String>,
    pub unlisted_environment_policy: String,
    pub explicitly_excluded_variables: Vec<String>,
    pub explicitly_excluded_prefixes: Vec<String>,
}

/// Authoritative host-side metadata for the trusted Rocq environment
/// preflight. Unlike diagnostic checker telemetry, this invocation happens
/// outside the proof-agent container and is part of the fail-closed boundary.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct TrustedCheckInvocation {
    pub timeout_seconds: u64,
    pub elapsed_ms: u128,
    pub exit_code: Option<i32>,
    pub timed_out: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ProofAgentContext {
    pub manifest_path: String,
    pub manifest_sha256: String,
    pub manifest_bytes: usize,
    pub source_sql_sha256: String,
    pub source_sql_bytes: usize,
    pub target_sql_sha256: String,
    pub target_sql_bytes: usize,
    pub query_shape_sha256: String,
    pub query_shape_bytes: usize,
    pub ordered_signatures_sha256: String,
    pub ordered_signatures_bytes: usize,
    pub observation_certificates_sha256: String,
    pub observation_certificates_bytes: usize,
    pub schema_module_sha256: String,
    pub schema_module_bytes: usize,
    pub queries_module_sha256: String,
    pub queries_module_bytes: usize,
    pub witness_module_sha256: String,
    pub witness_module_bytes: usize,
    pub problem_module_bytes: usize,
    pub goal_module_bytes: usize,
    pub semantic_primer_bytes: usize,
    pub declaration_search_sha256: String,
    pub declaration_search_bytes: usize,
    pub generated_context_bytes: usize,
}

#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct AgentRunLog {
    pub round: usize,
    /// Generation of Schema/Queries/Witness and their context manifest.  This
    /// changes only when the host accepts a fixed witness and regenerates the
    /// complete FormalSQL workspace.
    pub workspace_generation: usize,
    pub session_generation: usize,
    pub session_restarted: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub session_restart_reason: Option<ProofSessionRestartReason>,
    pub checkpoint_transition: ProofCheckpointTransition,
    pub command: String,
    pub context_manifest_sha256: String,
    pub remaining_proof_search_seconds: u64,
    pub round_budget_seconds: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub session_id: Option<String>,
    pub docker_image: String,
    pub started_ms_since_epoch: u128,
    pub elapsed_ms: u128,
    pub success: bool,
    pub exit_code: Option<i32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub proof_check_exit_code: Option<i32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub proof_check_elapsed_ms: Option<u128>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub proof_check_timeout_seconds: Option<u64>,
    pub proof_check_timed_out: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub authority_closure_path: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub authority_closure_sha256: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub authority_closure_bytes: Option<usize>,
    pub candidate_problem_sha256: String,
    pub candidate_problem_compile_passed: bool,
    pub candidate_has_final_theorem: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub candidate_claim: Option<VerificationClaimKind>,
    pub active_problem_compile_checkpoint_sha256: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub updated_problem_compile_checkpoint_sha256: Option<String>,
    pub compile_checkpoint_restored: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub diagnostic_checker_telemetry_path: Option<String>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub diagnostic_checker_invocations: Vec<DiagnosticCheckerInvocation>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub diagnostic_checker_telemetry_error: Option<String>,
    /// Every broker socket request, including malformed and quota-rejected
    /// requests that never reserve a timeout or reach source auditing.
    pub diagnostic_requests_seen: usize,
    /// Sum of agent-requested timeout seconds reserved after strict request
    /// validation. Source-audit rejections remain charged to this budget.
    pub diagnostic_requested_timeout_seconds_reserved: u64,
    /// Source-audit-clean requests that actually invoked the checker.
    pub diagnostic_accepted_count: usize,
    /// Requests rejected by the transient deterministic Problem.v audit.
    pub diagnostic_rejected_source_audit_count: usize,
    /// Residual requests not represented by either accepted checker telemetry
    /// or a source-audit rejection record. This includes malformed, quota,
    /// digest-drift, snapshot, and deadline rejections.
    pub diagnostic_other_rejected_request_count: usize,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub diagnostic_accepted_source_audits: Vec<AcceptedDiagnosticSourceAudit>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub diagnostic_rejected_source_audits: Vec<RejectedDiagnosticSourceAudit>,
    pub scratch_file_count: usize,
    pub scratch_bytes: usize,
    pub stdout_path: String,
    pub stderr_path: String,
    pub stdout_bytes: usize,
    pub stderr_bytes: usize,
    pub events_path: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub usage: Option<LlmUsage>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub usage_error: Option<String>,
    pub audit: AgentAudit,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub precondition_source: Option<PreconditionSource>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub precondition_definition: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub counterexample_handoff: Option<ProofCounterexampleHandoff>,
    pub error: Option<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum ProofSessionRestartReason {
    FixedWitnessReplacement,
    FailedRoundLimit,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum ProofCheckpointTransition {
    NewWorkspaceInitial,
    Continued,
    RestoredExisting,
}

/// Host-observed diagnostic checker telemetry. The untrusted proof agent may
/// request only the bounded timeout; it cannot execute the official diagnostic
/// checker or write these measurements.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct DiagnosticCheckerInvocation {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub sequence: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub mode: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub candidate_sha256: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub candidate_path: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub purpose: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub compile_passed: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub problem_compile_passed: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub compile_checkpoint_advanced: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub stdout_sha256: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub stderr_sha256: Option<String>,
    pub requested_timeout_seconds: u64,
    pub effective_timeout_seconds: u64,
    pub started_at_unix_ms: u128,
    pub elapsed_ms: u128,
    pub exit_code: Option<i32>,
    pub timed_out: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

/// Digest-bound host evidence for one file produced by the synchronous
/// diagnostic broker. Paths are relative to the case artifact root.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct DiagnosticArtifactBinding {
    pub path: String,
    pub sha256: String,
    pub bytes: usize,
}

/// A source-audit-clean request for which the host actually invoked the
/// problem-only Rocq checker. Its sequence is the checker invocation sequence,
/// not the broader broker request ordinal.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct AcceptedDiagnosticSourceAudit {
    pub request_ordinal: usize,
    pub sequence: usize,
    pub mode: String,
    pub candidate_path: String,
    pub purpose: String,
    pub candidate_sha256: String,
    pub requested_timeout_seconds: u64,
    pub candidate: DiagnosticArtifactBinding,
    pub audit: DiagnosticArtifactBinding,
}

/// A request rejected by the deterministic transient Problem.v source audit.
/// It never receives a checker sequence and never contributes checker elapsed
/// time, but its exact host-authored rejection evidence remains integrity
/// bound to the proof-round report.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct RejectedDiagnosticSourceAudit {
    pub request_ordinal: usize,
    pub mode: String,
    pub candidate_path: String,
    pub purpose: String,
    pub candidate_sha256: String,
    pub requested_timeout_seconds: u64,
    pub problem: DiagnosticArtifactBinding,
    pub request: DiagnosticArtifactBinding,
    pub audit: DiagnosticArtifactBinding,
    pub feedback: DiagnosticArtifactBinding,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ProofCounterexampleHandoff {
    pub decision: ProofAgentDecision,
    pub reason: String,
    pub guidance: String,
}

impl ProofCounterexampleHandoff {
    pub fn counterexample_feedback(&self) -> String {
        format!(
            "The proof agent suspects non-equivalence. Independently synthesize candidate DML for a typed FormalSQL witness and do not treat this claim as evidence. PostgreSQL will materialize the database without executing the query pair; trusted Rocq must decide the result. Reason: {} Guidance: {}",
            self.reason, self.guidance
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ProofAgentDecision {
    CounterexampleCandidate,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum PreconditionSource {
    Derived,
    External,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum VerificationClaimKind {
    Equivalence,
    FormalCountermodel,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "SCREAMING-KEBAB-CASE")]
pub enum CertificationLevel {
    SafeUnconditional,
    OutcomeUnconditional,
    ConditionalDerived,
    ConditionalExternal,
    FormalCountermodel,
}

impl CertificationLevel {
    pub const fn label(self) -> &'static str {
        match self {
            Self::SafeUnconditional => "SAFE-UNCONDITIONAL",
            Self::OutcomeUnconditional => "OUTCOME-UNCONDITIONAL",
            Self::ConditionalDerived => "CONDITIONAL-DERIVED",
            Self::ConditionalExternal => "CONDITIONAL-EXTERNAL",
            Self::FormalCountermodel => "FORMAL-COUNTERMODEL",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AgentAudit {
    pub passed: bool,
    pub scanned_files: Vec<String>,
    pub findings: Vec<AuditFinding>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AuditFinding {
    pub path: String,
    pub line: usize,
    pub token: String,
    pub excerpt: String,
}

#[cfg(test)]
mod tests {
    use super::{CertificationLevel, SolverOutcome};

    #[test]
    fn certification_and_solver_outcomes_keep_distinct_wire_labels() {
        assert_eq!(
            serde_json::to_value(CertificationLevel::SafeUnconditional)
                .expect("serialize certification"),
            serde_json::json!("SAFE-UNCONDITIONAL")
        );
        assert_eq!(
            serde_json::to_value(CertificationLevel::ConditionalExternal)
                .expect("serialize certification"),
            serde_json::json!("CONDITIONAL-EXTERNAL")
        );
        assert_eq!(
            serde_json::to_value(CertificationLevel::FormalCountermodel)
                .expect("serialize countermodel certification"),
            serde_json::json!("FORMAL-COUNTERMODEL")
        );
        assert_eq!(
            serde_json::to_value(SolverOutcome::OutcomeUnconditional)
                .expect("serialize solver outcome"),
            serde_json::json!("outcome_unconditional")
        );
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Backend {
    FormalSqlRocq,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum BackendStatus {
    LoweringBlocked,
    WorkspaceGenerated,
    ProofAgentRunCompleted,
    ProofSearchTimedOut,
    ProofComplete,
    ProofAgentFailed,
}
