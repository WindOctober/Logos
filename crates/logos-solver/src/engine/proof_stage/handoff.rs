//! Normalize agent requests before the scheduler applies a single disposition.

use super::{AgentRunLog, FormalWitnessSnapshot, ProofAgentDecision, ProofCounterexampleHandoff};
use crate::error::Result;

pub(in crate::engine) enum ProofHandoffResolution {
    Continue(String),
    NeedsManualReview(ManualReviewRequest),
    RestartWithFormalWitness {
        feedback: String,
        snapshot: FormalWitnessSnapshot,
    },
}

/// Different producers supply different evidence, but share one terminal gate.
pub(in crate::engine) enum ManualReviewRequest {
    ProofAgent { reason: String, guidance: String },
    CounterexampleAssessment { reason: String },
}

impl ManualReviewRequest {
    pub(in crate::engine) fn validate(
        &self,
        log: &AgentRunLog,
    ) -> std::result::Result<String, String> {
        let reason = match self {
            Self::ProofAgent { reason, .. } | Self::CounterexampleAssessment { reason } => reason,
        };
        if reason.trim().is_empty() {
            return Err("manual review requires a non-empty reason".to_owned());
        }
        // A successful certificate always wins over a stale review request.
        if log.success || log.proof_check_exit_code == Some(0) {
            return Err("a trusted certificate has already been accepted".to_owned());
        }
        match self {
            Self::CounterexampleAssessment { reason } => Ok(reason.clone()),
            Self::ProofAgent { reason, guidance } => {
                if guidance.trim().is_empty() {
                    return Err("manual review requires non-empty inspection guidance".to_owned());
                }
                if !log.audit.passed || !log.audit.findings.is_empty() {
                    return Err(format!(
                        "source safety audit failed: {:?}",
                        log.audit.findings
                    ));
                }
                if !(log.candidate_problem_compile_passed
                    || log.candidate_problem_sha256 == log.active_problem_compile_checkpoint_sha256)
                {
                    return Err(
                        "exact Problem.v lacks compile-clean checkpoint authority".to_owned()
                    );
                }
                if log.candidate_has_final_theorem {
                    return Err(
                        "remove the final certificate theorem before requesting manual review"
                            .to_owned(),
                    );
                }
                if log.proof_check_timed_out || log.diagnostic_checker_telemetry_error.is_some() {
                    return Err("checker timeout or trusted diagnostic failure is not manual-review evidence".to_owned());
                }
                Ok(format!(
                    "proof agent requested uncertified manual review and supplied this untrusted obstruction rationale: {reason} Guidance: {guidance}"
                ))
            }
        }
    }
}

pub(super) type ProofHandoffHandler<'a> =
    dyn FnMut(&ProofCounterexampleHandoff) -> Result<ProofHandoffResolution> + 'a;

/// A terminal result or a new witness never needs the old agent session.
pub(super) enum ProofRoundDisposition {
    Complete,
    NeedsManualReview(String),
    RestartWithFormalWitness {
        feedback: String,
        snapshot: FormalWitnessSnapshot,
    },
    Continue(Option<String>),
    ResumeUnavailable(Option<String>),
}

pub(super) fn resolve_proof_round(
    log: &AgentRunLog,
    session_resumable: bool,
    handler: Option<&mut ProofHandoffHandler<'_>>,
) -> Result<ProofRoundDisposition> {
    if log.success {
        return Ok(ProofRoundDisposition::Complete);
    }
    let mut feedback = None;
    if let Some(handoff) = &log.counterexample_handoff {
        let round = log.round;
        match resolve_handoff(handoff, handler)? {
            ProofHandoffResolution::Continue(reason) => {
                feedback = Some(format!(
                    "The handoff from proof round {round} did not terminate the search. Resume the proof and account for this feedback:\n{reason}"
                ));
            }
            ProofHandoffResolution::NeedsManualReview(request) => match request.validate(log) {
                Ok(reason) => return Ok(ProofRoundDisposition::NeedsManualReview(reason)),
                Err(reason) => {
                    feedback = Some(format!(
                        "Manual review rejected in round {round}: {reason}. Continue from the trusted checkpoint; address this finding before submitting another request."
                    ))
                }
            },
            ProofHandoffResolution::RestartWithFormalWitness { feedback, snapshot } => {
                return Ok(ProofRoundDisposition::RestartWithFormalWitness { feedback, snapshot });
            }
        }
    }
    Ok(if session_resumable {
        ProofRoundDisposition::Continue(feedback)
    } else {
        ProofRoundDisposition::ResumeUnavailable(feedback)
    })
}

pub(super) fn resolve_handoff(
    handoff: &ProofCounterexampleHandoff,
    handler: Option<&mut ProofHandoffHandler<'_>>,
) -> Result<ProofHandoffResolution> {
    match handoff.decision {
        ProofAgentDecision::NeedsManualReview => Ok(ProofHandoffResolution::NeedsManualReview(
            ManualReviewRequest::ProofAgent {
                reason: handoff.reason.clone(),
                guidance: handoff.guidance.clone(),
            },
        )),
        ProofAgentDecision::CounterexampleCandidate => match handler {
            Some(handler) => handler(handoff),
            None => Ok(ProofHandoffResolution::Continue(
                "Counterexample search is disabled. Continue proof analysis; do not treat the unvalidated suspicion as a result.".to_owned(),
            )),
        },
    }
}
