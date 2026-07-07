use std::time::{Instant, SystemTime, UNIX_EPOCH};

mod config;
mod counterexample;
mod proof_stage;
mod report;

use crate::artifacts::ArtifactWriter;
use crate::core::VerificationInput;
use crate::error::Result;
use crate::proposal::CommandProvider;

pub use config::Config;
use counterexample::{CounterexampleStageResult, run_counterexample_search};
pub use proof_stage::DEFAULT_PROOF_AGENT_COMMAND;
use proof_stage::run_proof_stage;
pub use report::{BackendStatus, Evidence, SolverOutcome, SolverReport};
use report::{SearchReport, SearchStatus};

pub fn solve(
    input: VerificationInput,
    options: Config,
    artifacts: ArtifactWriter,
) -> Result<SolverReport> {
    let started = Instant::now();
    artifacts.write_json("input/verification-input.json", &input)?;

    if options.transform_only {
        let transform_options = Config {
            run_proof_agent: false,
            ..options
        };
        let verification_report = run_proof_stage(&artifacts, &input, &transform_options)?;
        let report = SolverReport::finished(
            SolverOutcome::TransformOnly,
            verification_report.status_reason.clone(),
            Vec::new(),
            None,
            Some(verification_report),
            artifacts.root().display().to_string(),
            started,
        );
        artifacts.write_json("report.json", &report)?;
        return Ok(report);
    }

    let counterexample_report = if !options.disable_counterexample_search {
        let command = options.proposal_command.clone();
        let provider = CommandProvider::new(command);
        match run_counterexample_search(&input, &options, &provider, &artifacts, started)? {
            CounterexampleStageResult::Terminal(report) => return Ok(report),
            CounterexampleStageResult::ProceedToProof(report) => report,
        }
    } else {
        let report = SearchReport::finished(
            SearchStatus::Skipped,
            "counterexample search disabled; entering equivalence verification stage".to_owned(),
            Vec::new(),
            None,
            started,
        );
        artifacts.write_json("counterexample-stage/report.json", &report)?;
        report
    };

    let verification_report = run_proof_stage(&artifacts, &input, &options)?;
    let report = SolverReport::finished(
        SolverOutcome::EquivalenceVerificationIncomplete,
        verification_report.status_reason.clone(),
        counterexample_report.rounds,
        None,
        Some(verification_report),
        artifacts.root().display().to_string(),
        started,
    );
    artifacts.write_json("report.json", &report)?;
    Ok(report)
}

pub(super) fn now_ms_since_epoch() -> u128 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|duration| duration.as_millis())
        .unwrap_or(0)
}
