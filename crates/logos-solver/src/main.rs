mod artifacts;
mod core;
mod engine;
mod error;
mod output;

mod proposal;
mod runtime;
mod validation;

use std::path::PathBuf;

use crate::artifacts::ArtifactWriter;
use crate::core::VerificationInput;
use crate::engine::{Config, DEFAULT_PROOF_AGENT_COMMAND, solve};
use crate::error::Result;
use crate::output::print_report;
use clap::{Parser, Subcommand, ValueEnum};

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
        #[arg(long, value_enum, default_value_t = CliOutputFormat::Pretty)]
        output: CliOutputFormat,
    },
}

#[derive(Debug, Clone, Copy, ValueEnum)]
enum CliOutputFormat {
    Pretty,
    Json,
    Both,
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
            disable_proof_agent,
            proof_agent_command,
            proof_docker_image,
            proof_rocq_opam_switch,
            logos_repo_root,
            output,
        } => {
            let logos_repo_root = logos_repo_root.unwrap_or_else(runtime::repo_root);
            let calcite_ir_command =
                calcite_ir_command.unwrap_or_else(|| runtime::calcite_ir_command(&logos_repo_root));
            let proof_rocq_opam_switch =
                proof_rocq_opam_switch.or_else(|| runtime::rocq_opam_switch(&logos_repo_root));

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
                    run_proof_agent: !disable_proof_agent,
                    proof_agent_command,
                    proof_docker_image,
                    proof_rocq_opam_switch,
                    logos_repo_root: Some(logos_repo_root),
                },
                artifacts,
            )?;
            print_report(&report, output.into())?;
        }
    }
    Ok(())
}

impl From<CliOutputFormat> for output::OutputFormat {
    fn from(value: CliOutputFormat) -> Self {
        match value {
            CliOutputFormat::Pretty => output::OutputFormat::Pretty,
            CliOutputFormat::Json => output::OutputFormat::Json,
            CliOutputFormat::Both => output::OutputFormat::Both,
        }
    }
}
