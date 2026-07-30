use std::time::Instant;

use crate::artifacts::ArtifactWriter;
use crate::engine::report::{
    Evidence, LlmAssessmentLog, ProposalRound, RoundOutcome, RoundReport, SearchReport,
    SearchStatus, SolverOutcome, SolverReport, ValidationLog,
};
use crate::error::{Error, Result};
use crate::proposal::Candidate;
use crate::validation::WitnessCheck;

pub(super) struct SearchRun<'a> {
    artifacts: &'a ArtifactWriter,
    started: Instant,
    rounds: Vec<ProposalRound>,
    pub(super) feedback: Vec<String>,
    formal_witness_snapshot: Option<crate::validation::FormalWitnessSnapshot>,
}

pub(super) struct RecordedRound {
    round: usize,
    assessment: LlmAssessmentLog,
    proposal: Candidate,
    validation: Option<WitnessCheck>,
    validation_log: Option<ValidationLog>,
    outcome: RoundOutcome,
    error: Option<String>,
}

pub(in crate::engine) enum CounterexampleStageResult {
    Terminal(Box<SolverReport>),
    ProceedToProof(SearchReport),
}

impl<'a> SearchRun<'a> {
    pub(super) fn new(artifacts: &'a ArtifactWriter, started: Instant) -> Self {
        Self {
            artifacts,
            started,
            rounds: Vec::new(),
            feedback: Vec::new(),
            formal_witness_snapshot: None,
        }
    }

    pub(super) fn resume(
        artifacts: &'a ArtifactWriter,
        started: Instant,
        rounds: Vec<ProposalRound>,
        feedback: Vec<String>,
    ) -> Self {
        Self {
            artifacts,
            started,
            rounds,
            feedback,
            formal_witness_snapshot: None,
        }
    }

    pub(super) fn retain_formal_witness_snapshot(
        &mut self,
        snapshot: crate::validation::FormalWitnessSnapshot,
    ) {
        self.formal_witness_snapshot = Some(snapshot);
    }

    pub(super) fn next_round(&self) -> usize {
        self.rounds
            .last()
            .map_or(1, |round| round.round.saturating_add(1))
    }

    pub(super) fn record_round(&mut self, recorded: RecordedRound) -> Result<()> {
        write_round_report(
            self.artifacts,
            recorded.round,
            recorded.assessment.clone(),
            recorded.validation_log,
            recorded.outcome,
            recorded.error,
        )?;
        self.rounds.push(ProposalRound {
            round: recorded.round,
            assessment: recorded.assessment,
            proposal: Some(recorded.proposal),
            validation: recorded.validation,
        });
        Ok(())
    }

    pub(super) fn record_assessment_failure(
        &mut self,
        round: usize,
        assessment: LlmAssessmentLog,
        outcome: RoundOutcome,
        error: &Error,
    ) -> Result<()> {
        write_round_report(
            self.artifacts,
            round,
            assessment.clone(),
            None,
            outcome,
            Some(error.to_string()),
        )?;
        self.rounds.push(ProposalRound {
            round,
            assessment,
            proposal: None,
            validation: None,
        });
        Ok(())
    }

    pub(super) fn finish_terminal(
        self,
        solver_outcome: SolverOutcome,
        search_status: SearchStatus,
        reason: String,
        counterexample: Option<Evidence>,
    ) -> Result<CounterexampleStageResult> {
        let mut counterexample_report = SearchReport::finished(
            search_status,
            reason.clone(),
            self.rounds.clone(),
            counterexample.clone(),
            self.started,
        )?;
        counterexample_report.formal_witness_snapshot = self.formal_witness_snapshot.clone();
        self.artifacts
            .write_json("counterexample-stage/report.json", &counterexample_report)?;
        let report = SolverReport::finished(
            solver_outcome,
            reason,
            self.rounds,
            counterexample,
            None,
            self.artifacts.root().display().to_string(),
            self.started,
        )?;
        self.artifacts.write_json("report.json", &report)?;
        Ok(CounterexampleStageResult::Terminal(Box::new(report)))
    }

    pub(super) fn finish_without_counterexample(
        self,
        search_status: SearchStatus,
        reason: String,
    ) -> Result<CounterexampleStageResult> {
        let mut report =
            SearchReport::finished(search_status, reason, self.rounds, None, self.started)?;
        report.formal_witness_snapshot = self.formal_witness_snapshot;
        self.artifacts
            .write_json("counterexample-stage/report.json", &report)?;
        Ok(CounterexampleStageResult::ProceedToProof(report))
    }
}

impl RecordedRound {
    pub(super) fn without_validation(
        round: usize,
        assessment: LlmAssessmentLog,
        proposal: Candidate,
        outcome: RoundOutcome,
        error: Option<String>,
    ) -> Self {
        Self {
            round,
            assessment,
            proposal,
            validation: None,
            validation_log: None,
            outcome,
            error,
        }
    }

    pub(super) fn with_validation(
        round: usize,
        assessment: LlmAssessmentLog,
        proposal: Candidate,
        validation: WitnessCheck,
        validation_log: ValidationLog,
        outcome: RoundOutcome,
        error: Option<String>,
    ) -> Self {
        Self {
            round,
            assessment,
            proposal,
            validation: Some(validation),
            validation_log: Some(validation_log),
            outcome,
            error,
        }
    }
}

fn write_round_report(
    artifacts: &ArtifactWriter,
    round: usize,
    assessment: LlmAssessmentLog,
    validation: Option<ValidationLog>,
    outcome: RoundOutcome,
    error: Option<String>,
) -> Result<()> {
    let report = RoundReport {
        round,
        assessment,
        validation,
        outcome,
        error,
    };
    artifacts.write_json(format!("rounds/{round:02}/round-report.json"), &report)
}
