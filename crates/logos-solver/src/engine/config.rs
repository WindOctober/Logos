use std::path::PathBuf;

use crate::core::{SqlEnvironment, SqlTimeZone, VerificationMode};

#[derive(Debug, Clone)]
pub struct Config {
    pub calcite_ir_command: String,
    pub transform_only: bool,
    pub typed_witness_empty_audit: bool,
    pub disable_counterexample_search: bool,
    pub llm_assessment_only: bool,
    pub reuse_llm_assessment: bool,
    pub force_llm_assessment: bool,
    pub llm_assessment_cache_dir: PathBuf,
    pub proposal_command: String,
    pub proposal_resume_command: String,
    pub max_counterexample_rounds: usize,
    pub postgres_url: Option<String>,
    pub statement_timeout_ms: u64,
    pub sql_time_zone: SqlTimeZone,
    pub sql_environment: SqlEnvironment,
    pub verification_mode: VerificationMode,
    pub run_proof_agent: bool,
    pub proof_agent_command: String,
    pub proof_agent_resume_command: String,
    pub proof_agent_memory_limit_mib: u64,
    pub proof_agent_storage_limit_mib: u64,
    pub proof_agent_timeout_seconds: u64,
    pub proof_check_timeout_seconds: u64,
    pub proof_docker_image: String,
    pub proof_rocq_opam_switch: Option<PathBuf>,
    pub logos_repo_root: Option<PathBuf>,
}
