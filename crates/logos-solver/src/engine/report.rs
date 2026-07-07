use serde::{Deserialize, Serialize};
use std::time::Instant;

use crate::proposal::{Candidate, Decision};
use crate::validation::{SchemaMismatch, ValidationWarning, WitnessCheck};

#[derive(Debug, Clone, Serialize, Deserialize)]
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
    ) -> Self {
        Self {
            outcome,
            reason,
            rounds,
            counterexample,
            proof,
            log_dir,
            elapsed_ms: started.elapsed().as_millis(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SolverOutcome {
    Equivalent,
    NotEquivalent,
    TransformOnly,
    EquivalenceVerificationIncomplete,
    NeedsManualReview,
    LlmAssessmentOnly,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SearchReport {
    pub outcome: SearchStatus,
    pub reason: String,
    pub rounds: Vec<ProposalRound>,
    pub counterexample: Option<Evidence>,
    pub elapsed_ms: u128,
}

impl SearchReport {
    pub fn finished(
        outcome: SearchStatus,
        reason: String,
        rounds: Vec<ProposalRound>,
        counterexample: Option<Evidence>,
        started: Instant,
    ) -> Self {
        Self {
            outcome,
            reason,
            rounds,
            counterexample,
            elapsed_ms: started.elapsed().as_millis(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SearchStatus {
    Skipped,
    MaybeEquivalent,
    NotEquivalent,
    NeedsManualReview,
    LlmAssessmentOnly,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ProposalRound {
    pub round: usize,
    pub assessment: LlmAssessmentLog,
    pub proposal: Candidate,
    pub validation: Option<WitnessCheck>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RoundReport {
    pub round: usize,
    pub assessment: LlmAssessmentLog,
    pub validation: Option<ValidationLog>,
    pub outcome: RoundOutcome,
    pub error: Option<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum RoundOutcome {
    AssessmentOnly,
    NoCandidate,
    ManualReview,
    CandidateRejected,
    CounterexampleValidated,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
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

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LlmAssessmentCacheLog {
    pub status: LlmAssessmentCacheStatus,
    pub path: String,
    pub read_elapsed_ms: Option<u128>,
    pub write_elapsed_ms: Option<u128>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum LlmAssessmentCacheStatus {
    Generated,
    Reused,
    NotWritten,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LlmProviderLog {
    pub command: Option<String>,
    pub started_ms_since_epoch: u128,
    pub elapsed_ms: u128,
    pub success: bool,
    pub exit_code: Option<i32>,
    pub stdout_bytes: usize,
    pub stderr_bytes: usize,
    pub stderr_path: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LlmParseLog {
    pub elapsed_ms: u128,
    pub success: bool,
    pub error: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ValidationLog {
    pub started_ms_since_epoch: u128,
    pub elapsed_ms: u128,
    pub result: ValidationOutcome,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub warnings: Vec<ValidationWarning>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ValidationOutcome {
    DataDifference,
    OutputSchemaMismatch,
    NoDifference,
    ValidationError,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", tag = "kind")]
pub enum Evidence {
    DataDifference {
        witness_sql: String,
        source_result: String,
        target_result: String,
        diff_sample: String,
    },
    OutputSchemaMismatch {
        witness_sql: String,
        mismatch: SchemaMismatch,
    },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ProofReport {
    pub backend: Backend,
    pub backend_status: BackendStatus,
    pub status_reason: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub proof_workspace: Option<ProofWorkspace>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub proof_agent: Option<AgentRunLog>,
    pub elapsed_ms: u128,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ProofWorkspace {
    pub generated_module_dir: String,
    pub problem_path: String,
    pub lemma_guide_path: String,
    pub proof_agent_prompt_path: String,
    pub rocq_check_script_path: String,
    pub docker_agent_script_path: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AgentRunLog {
    pub command: String,
    pub docker_image: String,
    pub started_ms_since_epoch: u128,
    pub elapsed_ms: u128,
    pub success: bool,
    pub exit_code: Option<i32>,
    pub stdout_path: String,
    pub stderr_path: String,
    pub stdout_bytes: usize,
    pub stderr_bytes: usize,
    pub audit: AgentAudit,
    pub error: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AgentAudit {
    pub passed: bool,
    pub scanned_files: Vec<String>,
    pub findings: Vec<AuditFinding>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AuditFinding {
    pub path: String,
    pub line: usize,
    pub token: String,
    pub excerpt: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Backend {
    FormalSqlRocq,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum BackendStatus {
    WorkspaceGenerated,
    ProofAgentRunCompleted,
    ProofComplete,
    ProofAgentFailed,
}
