mod artifacts;
mod core;
mod engine;
mod error;

mod proposal;
mod runtime;
mod usage;
mod validation;

use std::path::PathBuf;

use crate::artifacts::ArtifactWriter;
use crate::core::{SqlEnvironment, SqlTimeZone, VerificationInput, VerificationMode};
use crate::engine::{
    BackendStatus, Config, DEFAULT_PROOF_AGENT_COMMAND, DEFAULT_PROOF_AGENT_RESUME_COMMAND,
    Evidence, SolverOutcome, SolverReport, solve,
};
use crate::error::Error;
use crate::error::Result;
use clap::{Parser, Subcommand};
use colored::{ColoredString, Colorize};

const DEFAULT_CODEX_PROPOSAL_COMMAND: &str = "codex exec --disable plugins --disable remote_plugin --disable plugin_hooks --disable skill_mcp_dependency_install --json --model gpt-5.6-sol -c model_reasoning_effort=medium --dangerously-bypass-approvals-and-sandbox --skip-git-repo-check -";
const DEFAULT_CODEX_PROPOSAL_RESUME_COMMAND: &str = "codex exec resume --disable plugins --disable remote_plugin --disable plugin_hooks --disable skill_mcp_dependency_install --json --model gpt-5.6-sol -c model_reasoning_effort=medium --dangerously-bypass-approvals-and-sandbox --skip-git-repo-check {session_id} -";

#[derive(Debug, Parser)]
#[command(version, about = "Logos SQL equivalence solver")]
struct Args {
    #[command(subcommand)]
    command: Command,
}

#[derive(Debug, Subcommand)]
enum Command {
    Check {
        #[arg(long)]
        schema: PathBuf,
        #[arg(long)]
        source: PathBuf,
        #[arg(long)]
        target: PathBuf,
        #[arg(long, env = "LOGOS_CALCITE_IR_COMMAND")]
        calcite_ir_command: Option<String>,
        #[arg(long)]
        disable_counterexample_search: bool,
        #[arg(long, conflicts_with = "llm_assessment_only")]
        transform_only: bool,
        /// Deterministically generate an available typed Witness.v whose
        /// lowered tables are all empty. This is an offline coverage gate,
        /// never an equivalence or counterexample result.
        #[arg(
            long,
            hide = true,
            conflicts_with_all = [
                "transform_only",
                "llm_assessment_only",
                "disable_counterexample_search"
            ]
        )]
        typed_witness_empty_audit: bool,
        #[arg(long, conflicts_with = "disable_counterexample_search")]
        llm_assessment_only: bool,
        #[arg(long, conflicts_with = "force_llm_assessment")]
        reuse_llm_assessment: bool,
        #[arg(long)]
        force_llm_assessment: bool,
        #[arg(long, default_value = "target/logos-solver-llm-assessments")]
        llm_assessment_cache_dir: PathBuf,
        #[arg(
            long,
            env = "LOGOS_PROPOSAL_COMMAND",
            default_value = DEFAULT_CODEX_PROPOSAL_COMMAND
        )]
        proposal_command: String,
        #[arg(
            long,
            env = "LOGOS_PROPOSAL_RESUME_COMMAND",
            hide = true,
            default_value = DEFAULT_CODEX_PROPOSAL_RESUME_COMMAND
        )]
        proposal_resume_command: String,
        #[arg(long, default_value_t = 3)]
        max_counterexample_rounds: usize,
        #[arg(long, env = "LOGOS_POSTGRES_URL")]
        postgres_url: Option<String>,
        #[arg(long)]
        log_dir: Option<PathBuf>,
        #[arg(long, default_value_t = 600_000)]
        statement_timeout_ms: u64,
        #[arg(long, env = "LOGOS_SQL_TIME_ZONE", default_value = "UTC")]
        sql_time_zone: String,
        #[arg(
            long,
            env = "LOGOS_SQL_DEFAULT_COLLATION",
            default_value = "unspecified"
        )]
        sql_default_collation: String,
        #[arg(
            long,
            env = "LOGOS_SQL_CHARACTER_CLASSIFICATION",
            default_value = "unspecified"
        )]
        sql_character_classification: String,
        #[arg(long, env = "LOGOS_SQL_LOCALE_PROVIDER", default_value = "unspecified")]
        sql_locale_provider: String,
        #[arg(long, env = "LOGOS_SQL_SERVER_ENCODING", default_value = "unspecified")]
        sql_server_encoding: String,
        #[arg(long, value_enum, default_value_t = VerificationMode::OutcomeUnconditional)]
        verification_mode: VerificationMode,
        #[arg(long)]
        disable_proof_agent: bool,
        #[arg(
            long,
            env = "LOGOS_PROOF_AGENT_COMMAND",
            hide = true,
            default_value = DEFAULT_PROOF_AGENT_COMMAND
        )]
        proof_agent_command: String,
        #[arg(
            long,
            env = "LOGOS_PROOF_AGENT_RESUME_COMMAND",
            hide = true,
            default_value = DEFAULT_PROOF_AGENT_RESUME_COMMAND
        )]
        proof_agent_resume_command: String,
        #[arg(
            long,
            env = "LOGOS_PROOF_AGENT_MEMORY_LIMIT_MIB",
            default_value_t = 6_144,
            value_parser = clap::value_parser!(u64).range(512..=65_536)
        )]
        proof_agent_memory_limit_mib: u64,
        #[arg(
            long,
            env = "LOGOS_PROOF_AGENT_STORAGE_LIMIT_MIB",
            default_value_t = 2_048
        )]
        proof_agent_storage_limit_mib: u64,
        #[arg(
            long,
            env = "LOGOS_PROOF_AGENT_TIMEOUT",
            default_value_t = 3_600,
            hide = true
        )]
        proof_agent_timeout_seconds: u64,
        #[arg(
            long,
            env = "LOGOS_PROOF_CHECK_TIMEOUT",
            default_value_t = 420,
            hide = true
        )]
        proof_check_timeout_seconds: u64,
        #[arg(
            long,
            env = "LOGOS_SOLVER_IMAGE",
            default_value = "logos-solver:latest"
        )]
        proof_docker_image: String,
        #[arg(long, env = "LOGOS_ROCQ_OPAM_SWITCH")]
        proof_rocq_opam_switch: Option<PathBuf>,
        #[arg(long, env = "LOGOS_REPO_ROOT")]
        logos_repo_root: Option<PathBuf>,
        #[arg(long)]
        quiet: bool,
    },
}

const SOLVER_WORKER_STACK_BYTES: usize = 64 * 1024 * 1024;

fn main() -> Result<()> {
    let worker = std::thread::Builder::new()
        .name("logos-solver".to_owned())
        .stack_size(SOLVER_WORKER_STACK_BYTES)
        .spawn(run)
        .map_err(Error::WorkerThread)?;
    match worker.join() {
        Ok(result) => result,
        Err(payload) => std::panic::resume_unwind(payload),
    }
}

fn run() -> Result<()> {
    let args = Args::parse();
    match args.command {
        Command::Check {
            schema,
            source,
            target,
            calcite_ir_command,
            disable_counterexample_search,
            transform_only,
            typed_witness_empty_audit,
            llm_assessment_only,
            reuse_llm_assessment,
            force_llm_assessment,
            llm_assessment_cache_dir,
            proposal_command,
            proposal_resume_command,
            max_counterexample_rounds,
            postgres_url,
            log_dir,
            statement_timeout_ms,
            sql_time_zone,
            sql_default_collation,
            sql_character_classification,
            sql_locale_provider,
            sql_server_encoding,
            verification_mode,
            disable_proof_agent,
            proof_agent_command,
            proof_agent_resume_command,
            proof_agent_memory_limit_mib,
            proof_agent_storage_limit_mib,
            proof_agent_timeout_seconds,
            proof_check_timeout_seconds,
            proof_docker_image,
            proof_rocq_opam_switch,
            logos_repo_root,
            quiet,
        } => {
            let logos_repo_root = logos_repo_root.unwrap_or_else(runtime::repo_root);
            let calcite_ir_command =
                calcite_ir_command.unwrap_or_else(|| runtime::calcite_ir_command(&logos_repo_root));
            let proof_rocq_opam_switch =
                proof_rocq_opam_switch.or_else(|| runtime::rocq_opam_switch(&logos_repo_root));
            let sql_time_zone =
                SqlTimeZone::try_parse(&sql_time_zone).map_err(Error::InvalidSqlTimeZone)?;
            let sql_environment = SqlEnvironment::try_parse(
                &sql_default_collation,
                &sql_character_classification,
                &sql_locale_provider,
                &sql_server_encoding,
            )
            .map_err(Error::InvalidSqlEnvironment)?;

            let input =
                VerificationInput::read_with_environment(schema, source, target, sql_environment)?;
            let artifacts = ArtifactWriter::new(log_dir)?;
            let report = solve(
                input,
                Config {
                    calcite_ir_command,
                    transform_only,
                    typed_witness_empty_audit,
                    disable_counterexample_search,
                    llm_assessment_only,
                    reuse_llm_assessment: reuse_llm_assessment
                        || (cfg!(debug_assertions) && !force_llm_assessment),
                    force_llm_assessment,
                    llm_assessment_cache_dir,
                    proposal_command,
                    proposal_resume_command,
                    max_counterexample_rounds,
                    postgres_url,
                    statement_timeout_ms,
                    sql_time_zone,
                    sql_environment,
                    verification_mode,
                    run_proof_agent: !disable_proof_agent,
                    proof_agent_command,
                    proof_agent_resume_command,
                    proof_agent_memory_limit_mib,
                    proof_agent_storage_limit_mib,
                    proof_agent_timeout_seconds,
                    proof_check_timeout_seconds,
                    proof_docker_image,
                    proof_rocq_opam_switch,
                    logos_repo_root: Some(logos_repo_root),
                },
                artifacts,
            )?;
            if !quiet {
                print_report(&report);
            }
        }
    }
    Ok(())
}

fn print_report(report: &SolverReport) {
    println!("{}", outcome_label(report));
    println!("Reason: {}", report.reason);

    if let Some(evidence) = report.counterexample.as_ref() {
        print_evidence(evidence);
    }

    if let Some(proof) = report.proof.as_ref() {
        println!("Verification mode: {}", proof.verification_mode.label());
        let proof_label = match proof.backend_status {
            BackendStatus::LoweringBlocked => "proof lowering blocked".bright_yellow().bold(),
            BackendStatus::ProofComplete => "proof complete".bright_green().bold(),
            BackendStatus::ProofAgentRunCompleted => {
                "proof agent completed; proof not marked complete"
                    .bright_yellow()
                    .bold()
            }
            BackendStatus::ProofSearchTimedOut => "proof search timed out".bright_yellow().bold(),
            BackendStatus::NeedsManualReview => "proof search stopped for manual review"
                .bright_yellow()
                .bold(),
            BackendStatus::WorkspaceGenerated => "proof workspace generated".bright_cyan().bold(),
            BackendStatus::ProofAgentFailed => "proof agent failed".bright_red().bold(),
        };
        println!("Proof stage: {proof_label}");
        if let Some(agent) = proof.proof_agent.as_ref() {
            println!(
                "Proof agent: success={} elapsed={}ms",
                agent.success, agent.elapsed_ms
            );
        }
        if let Some(certification) = proof.certification {
            println!("Certification: {}", certification.label());
        }
    }

    println!("Logs: {}", report.log_dir);
    println!("JSON report: {}/report.json", report.log_dir);
    println!("Elapsed: {}ms", report.elapsed_ms);
}

fn outcome_label(report: &SolverReport) -> ColoredString {
    match report.outcome {
        SolverOutcome::SafeUnconditional => "SAFE-UNCONDITIONAL".bright_green().bold(),
        SolverOutcome::OutcomeUnconditional => "OUTCOME-UNCONDITIONAL".bright_green().bold(),
        SolverOutcome::ConditionalDerived => "CONDITIONAL-DERIVED".bright_green().bold(),
        SolverOutcome::ConditionalExternal => "CONDITIONAL-EXTERNAL".bright_green().bold(),
        SolverOutcome::NotEquivalent => "NOT EQUIVALENT".bright_red().bold(),
        SolverOutcome::TransformOnly => "TRANSFORM COMPLETE".bright_cyan().bold(),
        SolverOutcome::EquivalenceVerificationIncomplete => {
            "EQUIVALENCE VERIFICATION INCOMPLETE".bright_yellow().bold()
        }
        SolverOutcome::NeedsManualReview => "MANUAL REVIEW REQUIRED".bright_yellow().bold(),
        SolverOutcome::LlmAssessmentOnly => "LLM ASSESSMENT COMPLETE".bright_cyan().bold(),
    }
}

fn print_evidence(evidence: &Evidence) {
    match evidence {
        Evidence::OutputSchemaMismatch { mismatch } => {
            println!("Evidence: {}", "output schema mismatch".bright_red().bold());
            println!("Mismatch: {}", mismatch.reason());
        }
        Evidence::FormalSqlCountermodel {
            problem_path,
            goal_path,
            problem_sha256,
            theorem,
            ..
        } => {
            println!(
                "Evidence: {}",
                "kernel-checked FormalSQL countermodel".bright_red().bold()
            );
            println!("Problem: {problem_path} ({problem_sha256})");
            println!("Trusted goal: {goal_path}");
            println!("Certificate theorem: {theorem}");
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clap::{CommandFactory, Parser};

    fn check_args(extra: &[&str]) -> Vec<String> {
        [
            "logos-solver",
            "check",
            "--schema",
            "schema.json",
            "--source",
            "source.sql",
            "--target",
            "target.sql",
        ]
        .into_iter()
        .chain(extra.iter().copied())
        .map(str::to_owned)
        .collect()
    }

    #[test]
    fn rejects_conflicting_execution_modes() {
        assert!(
            Args::try_parse_from(check_args(&["--transform-only", "--llm-assessment-only"]))
                .is_err()
        );
        assert!(
            Args::try_parse_from(check_args(&[
                "--disable-counterexample-search",
                "--llm-assessment-only"
            ]))
            .is_err()
        );
        assert!(
            Args::try_parse_from(check_args(&[
                "--typed-witness-empty-audit",
                "--transform-only"
            ]))
            .is_err()
        );
    }

    #[test]
    fn rejects_conflicting_assessment_cache_policies() {
        assert!(
            Args::try_parse_from(check_args(&[
                "--reuse-llm-assessment",
                "--force-llm-assessment"
            ]))
            .is_err()
        );
    }

    #[test]
    fn omitted_server_encoding_remains_unspecified() {
        let command = Args::command();
        let check = command
            .get_subcommands()
            .find(|subcommand| subcommand.get_name() == "check")
            .expect("check subcommand");
        let encoding = check
            .get_arguments()
            .find(|argument| argument.get_id() == "sql_server_encoding")
            .expect("sql-server-encoding argument");
        let defaults = encoding
            .get_default_values()
            .iter()
            .map(|value| value.to_string_lossy().into_owned())
            .collect::<Vec<_>>();

        assert_eq!(defaults, ["unspecified"]);
    }

    #[test]
    fn verification_mode_defaults_to_error_preserving_and_accepts_all_modes() {
        let Args {
            command: Command::Check {
                verification_mode, ..
            },
        } = Args::try_parse_from(check_args(&[])).expect("default check arguments");
        assert_eq!(verification_mode, VerificationMode::OutcomeUnconditional);

        for (value, expected) in [
            ("safe-unconditional", VerificationMode::SafeUnconditional),
            (
                "outcome-unconditional",
                VerificationMode::OutcomeUnconditional,
            ),
            ("conditional", VerificationMode::Conditional),
        ] {
            let Args {
                command:
                    Command::Check {
                        verification_mode, ..
                    },
            } = Args::try_parse_from(check_args(&["--verification-mode", value]))
                .expect("supported verification mode");
            assert_eq!(verification_mode, expected);
        }
    }

    #[test]
    fn codex_defaults_pin_structured_gpt_5_6_sol_invocations() {
        assert!(DEFAULT_CODEX_PROPOSAL_COMMAND.contains("--json"));
        assert!(DEFAULT_CODEX_PROPOSAL_COMMAND.contains("--model gpt-5.6-sol"));
        assert!(DEFAULT_CODEX_PROPOSAL_COMMAND.contains("model_reasoning_effort=medium"));
        assert!(DEFAULT_CODEX_PROPOSAL_RESUME_COMMAND.contains("codex exec resume"));
        assert!(DEFAULT_CODEX_PROPOSAL_RESUME_COMMAND.contains("{session_id}"));
        assert!(DEFAULT_CODEX_PROPOSAL_RESUME_COMMAND.contains("--json"));
        assert!(DEFAULT_CODEX_PROPOSAL_RESUME_COMMAND.contains("--model gpt-5.6-sol"));
        assert!(DEFAULT_CODEX_PROPOSAL_RESUME_COMMAND.contains("model_reasoning_effort=medium"));
        assert!(DEFAULT_PROOF_AGENT_COMMAND.contains("--json"));
        assert!(DEFAULT_PROOF_AGENT_COMMAND.contains("--model gpt-5.6-sol"));
        assert!(DEFAULT_PROOF_AGENT_COMMAND.contains("model_reasoning_effort=medium"));
        for feature in [
            "plugins",
            "remote_plugin",
            "plugin_hooks",
            "skill_mcp_dependency_install",
        ] {
            assert!(
                DEFAULT_CODEX_PROPOSAL_COMMAND.contains(&format!("--disable {feature}")),
                "counterexample command does not disable {feature}"
            );
            assert!(
                DEFAULT_CODEX_PROPOSAL_RESUME_COMMAND.contains(&format!("--disable {feature}")),
                "counterexample resume command does not disable {feature}"
            );
            assert!(
                DEFAULT_PROOF_AGENT_COMMAND.contains(&format!("--disable {feature}")),
                "initial proof command does not disable {feature}"
            );
            assert!(
                DEFAULT_PROOF_AGENT_RESUME_COMMAND.contains(&format!("--disable {feature}")),
                "resume proof command does not disable {feature}"
            );
        }
        assert!(DEFAULT_PROOF_AGENT_RESUME_COMMAND.contains("--json"));
        assert!(DEFAULT_PROOF_AGENT_RESUME_COMMAND.contains("--model gpt-5.6-sol"));
        assert!(DEFAULT_PROOF_AGENT_RESUME_COMMAND.contains("model_reasoning_effort=medium"));
    }
}
