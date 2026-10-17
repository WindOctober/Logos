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
