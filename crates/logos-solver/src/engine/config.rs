use std::path::PathBuf;

use crate::core::{SqlEnvironment, SqlTimeZone, VerificationMode};

/// Independent availability of pre-proved facts; never changes SQL semantics.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize)]
#[serde(rename_all = "camelCase")]
pub struct LemmaAvailability {
    pub bag: bool,
    pub other: bool,
}

impl Default for LemmaAvailability {
    fn default() -> Self {
        Self {
            bag: true,
            other: true,
        }
    }
}

impl LemmaAvailability {
    pub fn is_full(self) -> bool {
        self.bag && self.other
    }
}

#[derive(Debug, Clone)]
pub struct Config {
    pub calcite_ir_command: String,
    pub execution_mode: ExecutionMode,
    pub disable_counterexample_search: bool,
    pub reuse_llm_assessment: bool,
    pub force_llm_assessment: bool,
    pub llm_assessment_cache_dir: PathBuf,
    pub proposal_command: String,
    pub proposal_resume_command: String,
    pub postgres_url: Option<String>,
    pub statement_timeout_ms: u64,
    pub sql_time_zone: SqlTimeZone,
    pub sql_environment: SqlEnvironment,
    pub verification_mode: VerificationMode,
    pub lemma_availability: LemmaAvailability,
    pub proof_agent_command: String,
    pub proof_agent_resume_command: String,
    pub proof_agent_memory_limit_mib: u64,
    pub proof_agent_storage_limit_mib: u64,
    pub rocq_session_limits: super::rocq_session::SessionLimits,
    pub proof_agent_timeout_seconds: u64,
    pub proof_check_timeout_seconds: u64,
    pub proof_docker_image: String,
    pub proof_rocq_opam_switch: Option<PathBuf>,
    pub logos_repo_root: Option<PathBuf>,
}

/// Pipeline selection is independent of the SQL equivalence contract.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ExecutionMode {
    #[default]
    Verify,
    /// Run input preflight and prepare the proof workspace, without an agent.
    PrepareWorkspace,
    /// Offline lowering/workspace generation, without PostgreSQL preflight.
    TransformOnly,
    AssessmentOnly,
    /// Offline coverage audit with an available, empty typed witness.
    TypedWitnessAudit,
}
