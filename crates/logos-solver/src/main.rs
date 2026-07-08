mod artifacts;
mod core;
mod engine;
mod error;

mod proposal;
mod runtime;
mod validation;

use std::path::PathBuf;

use crate::artifacts::ArtifactWriter;
use crate::core::{SqlTimeZone, VerificationInput};
use crate::engine::{
    BackendStatus, Config, DEFAULT_PROOF_AGENT_COMMAND, Evidence, SolverOutcome, SolverReport,
    solve,
};
use crate::error::Error;
use crate::error::Result;
use clap::{Parser, Subcommand};
use colored::{ColoredString, Colorize};

const DEFAULT_CODEX_PROPOSAL_COMMAND: &str =
    "codex exec --dangerously-bypass-approvals-and-sandbox --skip-git-repo-check -";

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
        #[arg(long, alias = "before")]
        source: PathBuf,
        #[arg(long, alias = "after")]
        target: PathBuf,
        #[arg(long, env = "LOGOS_CALCITE_IR_COMMAND")]
        calcite_ir_command: Option<String>,
        #[arg(long, alias = "disable-llm-counterexample")]
        disable_counterexample_search: bool,
        #[arg(long)]
        transform_only: bool,
        #[arg(long)]
        llm_assessment_only: bool,
        #[arg(long)]
        reuse_llm_assessment: bool,
        #[arg(long)]
        force_llm_assessment: bool,
        #[arg(long, default_value = "target/logos-solver-llm-assessments")]
        llm_assessment_cache_dir: PathBuf,
        #[arg(
            long,
            alias = "agent-command",
            alias = "llm-command",
            env = "LOGOS_PROPOSAL_COMMAND",
            default_value = DEFAULT_CODEX_PROPOSAL_COMMAND
        )]
        proposal_command: String,
        #[arg(long, default_value_t = 3)]
        max_counterexample_rounds: usize,
        #[arg(long, env = "LOGOS_POSTGRES_URL")]
        postgres_url: Option<String>,
        #[arg(long)]
        log_dir: Option<PathBuf>,
        #[arg(long, default_value_t = 10_000)]
        statement_timeout_ms: u64,
        #[arg(long, default_value_t = 20)]
        diff_sample_limit: usize,
        #[arg(long, env = "LOGOS_SQL_TIME_ZONE", default_value = "UTC")]
        sql_time_zone: String,
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

fn main() -> Result<()> {
    let args = Args::parse();
    match args.command {
        Command::Check {
            schema,
            source,
            target,
            calcite_ir_command,
            disable_counterexample_search,
            transform_only,
            llm_assessment_only,
            reuse_llm_assessment,
            force_llm_assessment,
            llm_assessment_cache_dir,
            proposal_command,
            max_counterexample_rounds,
            postgres_url,
            log_dir,
            statement_timeout_ms,
            diff_sample_limit,
            sql_time_zone,
            disable_proof_agent,
            proof_agent_command,
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

            let input = VerificationInput::read(schema, source, target)?;
            let artifacts = ArtifactWriter::new(log_dir)?;
            let report = solve(
                input,
                Config {
                    calcite_ir_command,
                    transform_only,
                    disable_counterexample_search,
                    llm_assessment_only,
                    reuse_llm_assessment: reuse_llm_assessment
                        || (cfg!(debug_assertions) && !force_llm_assessment),
                    force_llm_assessment,
                    llm_assessment_cache_dir,
                    proposal_command,
                    max_counterexample_rounds,
                    postgres_url,
                    statement_timeout_ms,
                    diff_sample_limit,
                    sql_time_zone,
                    run_proof_agent: !disable_proof_agent,
                    proof_agent_command,
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
        let proof_label = match proof.backend_status {
            BackendStatus::ProofComplete => "proof complete".bright_green().bold(),
            BackendStatus::ProofAgentRunCompleted => {
                "proof agent completed; proof not marked complete"
                    .bright_yellow()
                    .bold()
            }
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
    }

    println!("Logs: {}", report.log_dir);
    println!("JSON report: {}/report.json", report.log_dir);
    println!("Elapsed: {}ms", report.elapsed_ms);
}

fn outcome_label(report: &SolverReport) -> ColoredString {
    match report.outcome {
        SolverOutcome::Equivalent => "EQUIVALENCE PROVED".bright_green().bold(),
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
        Evidence::DataDifference {
            witness_sql,
            diff_sample,
            ..
        } => {
            println!("Evidence: {}", "data difference".bright_red().bold());
            println!("Witness SQL: {}", one_line(witness_sql));
            println!("Diff sample: {}", one_line(diff_sample));
        }
        Evidence::OutputSchemaMismatch { witness_sql, .. } => {
            println!("Evidence: {}", "output schema mismatch".bright_red().bold());
            println!("Witness SQL: {}", one_line(witness_sql));
        }
    }
}

fn one_line(value: &str) -> String {
    const LIMIT: usize = 240;
    let compact = value.split_whitespace().collect::<Vec<_>>().join(" ");
    if compact.len() <= LIMIT {
        compact
    } else {
        format!("{}...", compact.chars().take(LIMIT).collect::<String>())
    }
}
