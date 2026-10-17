use super::super::audit::{AuditPurpose, audit_proof_workspace_for_mode};
use super::super::handoff::{ManualReviewRequest, ProofHandoffResolution, resolve_handoff};
use super::*;

fn review_log() -> AgentRunLog {
    let mut log = proof_run_log_fixture();
    log.candidate_has_final_theorem = false;
    log.proof_check_exit_code = None;
    log.candidate_claim = None;
    log
}

fn request() -> ProofCounterexampleHandoff {
    ProofCounterexampleHandoff {
        decision: ProofAgentDecision::NeedsManualReview,
        reason: "the trusted demand-safety contract is obstructed".to_owned(),
        guidance: "inspect the checked safety obstruction".to_owned(),
    }
}

fn audit_fixture(
    problem: &str,
    mode: VerificationMode,
    purpose: AuditPurpose,
    tamper: bool,
) -> super::super::audit::WorkspaceAudit {
    let temp = tempfile::tempdir().unwrap();
    let artifacts = ArtifactWriter::new(Some(temp.path().to_owned())).unwrap();
    for name in PROOF_SOURCE_FILES {
        artifacts
            .write_text(
                format!("proof-stage/formal-sql/{name}"),
                "Definition clean := I.\n",
            )
            .unwrap();
    }
    let trusted = capture_trusted_proof_sources(&artifacts).unwrap();
    artifacts
        .write_text("proof-stage/formal-sql/Problem.v", problem)
        .unwrap();
    if tamper {
        artifacts
            .write_text(
                "proof-stage/formal-sql/Goal.v",
                "Definition tampered := I.\n",
            )
            .unwrap();
    }
    audit_proof_workspace_for_mode(
        &artifacts,
        &temp.path().join("proof-stage/formal-sql"),
        &trusted,
        mode,
        purpose,
    )
    .unwrap()
}

#[test]
fn manual_review_checkpoint_without_claim_is_audited_and_accepted() {
    for mode in [
        VerificationMode::SafeUnconditional,
        VerificationMode::OutcomeUnconditional,
        VerificationMode::Conditional,
    ] {
        for selector in [
            "",
            "Definition generated_verification_claim : Logos.FormalSQL.VerificationConditions.verification_claim_kind := Logos.FormalSQL.VerificationConditions.VerificationEquivalence.\n",
        ] {
            let reviewed = audit_fixture(selector, mode, AuditPurpose::ManualReview, false);
            assert!(reviewed.audit.passed, "{:?}", reviewed.audit.findings);
            let mut log = review_log();
            log.audit = reviewed.audit;
            log.candidate_claim = reviewed.candidate_claim;
            // A byte-identical checkpoint is sufficient without recompiling.
            log.candidate_problem_compile_passed = false;
            log.candidate_problem_sha256 = log.active_problem_compile_checkpoint_sha256.clone();
            let ProofHandoffResolution::NeedsManualReview(review) =
                resolve_handoff(&request(), None).unwrap()
            else {
                panic!("review disposition")
            };
            assert!(review.validate(&log).unwrap().contains("uncertified"));
        }
    }
}

#[test]
fn manual_review_does_not_relax_source_safety_or_certificate_audits() {
    let mode = VerificationMode::OutcomeUnconditional;
    for (problem, tamper) in [("Axiom cheat : False.\n", false), ("", true)] {
        let result = audit_fixture(problem, mode, AuditPurpose::ManualReview, tamper);
        assert!(!result.audit.passed);
    }
    let missing = audit_fixture("", mode, AuditPurpose::Certificate, false);
    assert!(!missing.audit.passed);
    // A stale/manual handoff must never bypass claim checks on a final theorem.
    let final_without_claim = audit_fixture(
        "Theorem generated_queries_verified : True. Proof. exact I. Qed.\n",
        mode,
        AuditPurpose::ManualReview,
        false,
    );
    assert!(!final_without_claim.audit.passed);
    assert!(
        final_without_claim
            .audit
            .findings
            .iter()
            .any(|f| f.token == "generated_verification_claim")
    );
    let conditional = audit_fixture(
        "Theorem generated_queries_equivalent : True. Proof. exact I. Qed.\n",
        VerificationMode::Conditional,
        AuditPurpose::ManualReview,
        false,
    );
    assert!(!conditional.audit.passed);
}

#[test]
fn both_review_producers_use_the_same_terminal_validation() {
    let mut called = false;
    let mut handler = |_: &ProofCounterexampleHandoff| {
        called = true;
        Ok(ProofHandoffResolution::NeedsManualReview(
            ManualReviewRequest::CounterexampleAssessment {
                reason: "no materializable witness".to_owned(),
            },
        ))
    };
    let direct = resolve_handoff(&request(), Some(&mut handler)).unwrap();
    assert!(
        !called,
        "direct review must not invoke counterexample synthesis"
    );
    let mut candidate = request();
    candidate.decision = ProofAgentDecision::CounterexampleCandidate;
    let mut handler = |_: &ProofCounterexampleHandoff| {
        Ok(ProofHandoffResolution::NeedsManualReview(
            ManualReviewRequest::CounterexampleAssessment {
                reason: "no materializable witness".to_owned(),
            },
        ))
    };
    let assessed = resolve_handoff(&candidate, Some(&mut handler)).unwrap();
    for resolution in [direct, assessed] {
        let ProofHandoffResolution::NeedsManualReview(review) = resolution else {
            panic!("shared disposition")
        };
        assert!(review.validate(&review_log()).is_ok());
        let mut certified = review_log();
        certified.success = true;
        assert!(
            review
                .validate(&certified)
                .unwrap_err()
                .contains("certificate")
        );
    }
    assert!(matches!(
        resolve_handoff(&candidate, None).unwrap(),
        ProofHandoffResolution::Continue(_)
    ));
}

#[test]
fn manual_review_rejections_identify_the_failed_requirement() {
    let ProofHandoffResolution::NeedsManualReview(review) =
        resolve_handoff(&request(), None).unwrap()
    else {
        panic!("review")
    };
    let mut log = review_log();
    log.candidate_problem_compile_passed = false;
    assert!(
        review
            .validate(&log)
            .unwrap_err()
            .contains("checkpoint authority")
    );
    log = review_log();
    log.audit.passed = false;
    assert!(review.validate(&log).unwrap_err().contains("source safety"));
    log = review_log();
    log.candidate_has_final_theorem = true;
    assert!(
        review
            .validate(&log)
            .unwrap_err()
            .contains("final certificate theorem")
    );
    log = review_log();
    log.proof_check_timed_out = true;
    assert!(review.validate(&log).unwrap_err().contains("timeout"));
    log = review_log();
    log.diagnostic_checker_telemetry_error = Some("runtime failure".to_owned());
    assert!(
        review
            .validate(&log)
            .unwrap_err()
            .contains("diagnostic failure")
    );
    for review in [
        ManualReviewRequest::ProofAgent {
            reason: " ".to_owned(),
            guidance: "inspect".to_owned(),
        },
        ManualReviewRequest::CounterexampleAssessment {
            reason: " ".to_owned(),
        },
    ] {
        assert!(
            review
                .validate(&review_log())
                .unwrap_err()
                .contains("non-empty reason")
        );
    }
}
