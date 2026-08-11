use std::time::{Instant, SystemTime, UNIX_EPOCH};

mod config;
mod counterexample;
mod proof_stage;
mod report;

use crate::artifacts::ArtifactWriter;
use crate::core::VerificationInput;
use crate::error::{Error, Result};
use crate::proposal::CommandProvider;
use crate::validation::{FormalWitnessColumn, FormalWitnessSnapshot, FormalWitnessTable};
use logos_ir::ShellSqlIrFrontend;

pub use config::Config;
use counterexample::{
    CounterexampleStageResult, resume_counterexample_search, run_counterexample_search,
    run_output_schema_preflight,
};
pub use proof_stage::{DEFAULT_PROOF_AGENT_COMMAND, DEFAULT_PROOF_AGENT_RESUME_COMMAND};
use proof_stage::{
    ProofHandoffResolution, ProofStageResult, prepare_formal_input, run_proof_stage,
    write_typed_witness_audit_workspace,
};
pub use report::{BackendStatus, Evidence, SolverOutcome, SolverReport};
use report::{CertificationLevel, SearchReport, SearchStatus};

pub fn solve(
    mut input: VerificationInput,
    options: Config,
    artifacts: ArtifactWriter,
) -> Result<SolverReport> {
    let started = Instant::now();
    if input.integrity_contract().case_id.is_some() {
        let schema_probe_relative = "input/integrity-schema-probe.sql";
        artifacts.write_text(
            schema_probe_relative,
            "SELECT 1 AS logos_integrity_probe;\n",
        )?;
        let ir_frontend = ShellSqlIrFrontend::new(options.calcite_ir_command.clone())
            .with_environment(options.sql_environment);
        input.hydrate_integrity_contract(
            &ir_frontend,
            &artifacts.root().join(schema_probe_relative),
        )?;
    }
    // Keep this explicit at the orchestration boundary: no authoritative
    // input artifact, validator preflight, or agent/search stage may observe
    // a string-valued integrity contract under a weaker SQL environment.
    input.ensure_integrity_environment()?;
    artifacts.write_json("input/verification-input.json", &input)?;
    artifacts.write_json("input/integrity-contract.json", input.integrity_contract())?;
    artifacts.write_text(
        "input/integrity-contract.txt",
        &format!("{}\n", input.integrity_contract_summary()),
    )?;
    artifacts.write_json(
        "input/integrity-validator-checks.json",
        &input.integrity_contract().validation_checks(),
    )?;

    if options.typed_witness_empty_audit {
        let audit_options = Config {
            run_proof_agent: false,
            ..options.clone()
        };
        let prepared = prepare_formal_input(&artifacts, &input, &audit_options)?;
        let schema = prepared
            .lowering_report
            .schema
            .schema
            .as_ref()
            .ok_or_else(|| {
                Error::ProofAgentCommand(
                    "typed Witness.v audit requires a successfully lowered FormalSQL schema"
                        .to_owned(),
                )
            })?;
        let snapshot = FormalWitnessSnapshot {
            schema_version: 1,
            tables: schema
                .tables
                .iter()
                .map(|table| FormalWitnessTable {
                    relation: table.relation.clone(),
                    columns: table
                        .attributes
                        .iter()
                        .map(|attribute| FormalWitnessColumn {
                            name: attribute.name.clone(),
                            ty: attribute.ty,
                        })
                        .collect(),
                    rows: Vec::new(),
                })
                .collect(),
        };
        artifacts.write_json(
            "proof-stage/formal-witness-empty-audit-snapshot.json",
            &snapshot,
        )?;
        write_typed_witness_audit_workspace(&artifacts, schema, &snapshot)?;
        let report = SolverReport::finished(
            SolverOutcome::TransformOnly,
            "generated an available empty typed Witness.v for deterministic coverage auditing"
                .to_owned(),
            Vec::new(),
            None,
            None,
            artifacts.root().display().to_string(),
            started,
        )?;
        artifacts.write_json("report.json", &report)?;
        return Ok(report);
    }

    if options.transform_only {
        let transform_options = Config {
            run_proof_agent: false,
            ..options
        };
        let verification_report = match run_proof_stage(
            &artifacts,
            &input,
            &transform_options,
            None,
            None,
            None,
            None,
        )? {
            ProofStageResult::Finished(report) => *report,
        };
        let report = SolverReport::finished(
            SolverOutcome::TransformOnly,
            verification_report.status_reason.clone(),
            Vec::new(),
            None,
            Some(verification_report),
            artifacts.root().display().to_string(),
            started,
        )?;
        artifacts.write_json("report.json", &report)?;
        return Ok(report);
    }

    // Output shape is independent of witness data and proof strategy. Enforce
    // it once for every verification run, including runs that skip LLM search.
    if let Some(report) = run_output_schema_preflight(&input, &options, &artifacts, started)? {
        return Ok(*report);
    }

    // The exact same lowered syntax feeds proof navigation and the Rocq
    // workspace. The resulting JSON is host-recomputed metadata, not an
    // executor license or an agent assertion.
    let prepared_formal_input = prepare_formal_input(&artifacts, &input, &options)?;
    let observation_certificates = prepared_formal_input.observation_certificates.clone();
    let formal_schema_for_counterexample =
        prepared_formal_input.lowering_report.schema.schema.clone();
    artifacts.write_json(
        "counterexample-stage/observation-certificates.json",
        &observation_certificates,
    )?;

    if options.llm_assessment_only {
        if options.disable_counterexample_search {
            return Err(Error::ProposalCommand(
                "LLM assessment-only mode requires counterexample search".to_owned(),
            ));
        }
        let provider = CommandProvider::with_resume(
            options.proposal_command.clone(),
            options.proposal_resume_command.clone(),
        );
        return match run_counterexample_search(
            &input,
            formal_schema_for_counterexample.as_ref(),
            &observation_certificates,
            &options,
            &provider,
            &artifacts,
            started,
        )? {
            CounterexampleStageResult::Terminal(report) => Ok(*report),
            CounterexampleStageResult::ProceedToProof(_) => Err(Error::ProposalCommand(
                "assessment-only counterexample search unexpectedly requested a proof stage"
                    .to_owned(),
            )),
        };
    }

    let provider = (!options.disable_counterexample_search).then(|| {
        CommandProvider::with_resume(
            options.proposal_command.clone(),
            options.proposal_resume_command.clone(),
        )
    });
    // Normal verification has one authoritative search loop. Start in the
    // FormalSQL proof environment; invoke the counterexample agent only when
    // that same proof agent requests concrete witness synthesis. A returned
    // database is typed and frozen, then fed back to the trusted Rocq selector.
    let mut counterexample_report = if provider.is_some() {
        SearchReport::finished(
            SearchStatus::Skipped,
            "counterexample synthesis is proof-directed; starting unified FormalSQL verification"
                .to_owned(),
            Vec::new(),
            None,
            started,
        )?
    } else {
        SearchReport::finished(
            SearchStatus::Skipped,
            "counterexample synthesis disabled; starting unified FormalSQL verification".to_owned(),
            Vec::new(),
            None,
            started,
        )?
    };
    artifacts.write_json("counterexample-stage/report.json", &counterexample_report)?;

    let proof_stage_result = if let Some(provider) = provider.as_ref() {
        let mut handle_handoff = |handoff: &report::ProofCounterexampleHandoff| {
            match resume_counterexample_search(
                &input,
                formal_schema_for_counterexample.as_ref(),
                &observation_certificates,
                &options,
                provider,
                &artifacts,
                started,
                &counterexample_report,
                handoff.counterexample_feedback(),
            )? {
                CounterexampleStageResult::Terminal(_) => Err(Error::ProposalCommand(
                    "proof-directed counterexample synthesis attempted to terminate verification without the trusted Rocq selector"
                        .to_owned(),
                )),
                CounterexampleStageResult::ProceedToProof(report) => {
                    let resolution = proof_handoff_resolution(&report)?;
                    counterexample_report = report;
                    Ok(resolution)
                }
            }
        };
        run_proof_stage(
            &artifacts,
            &input,
            &options,
            Some(prepared_formal_input),
            None,
            None,
            Some(&mut handle_handoff),
        )?
    } else {
        run_proof_stage(
            &artifacts,
            &input,
            &options,
            Some(prepared_formal_input),
            None,
            None,
            None,
        )?
    };
    let verification_report = match proof_stage_result {
        ProofStageResult::Finished(report) => *report,
    };
    if counterexample_report.outcome == SearchStatus::NeedsManualReview
        && verification_report.certification.is_some()
    {
        return Err(Error::ProofAgentCommand(
            "manual-review proof termination cannot carry a trusted certification".to_owned(),
        ));
    }
    let outcome = final_solver_outcome(
        verification_report.certification,
        counterexample_report.outcome,
    );
    let status_reason = if outcome == SolverOutcome::NeedsManualReview {
        format!(
            "{}; proof-directed FormalSQL verification stopped without accepting EQ or NEQ: {}",
            counterexample_report.reason, verification_report.status_reason
        )
    } else {
        verification_report.status_reason.clone()
    };
    let counterexample = (verification_report.certification
        == Some(CertificationLevel::FormalCountermodel))
    .then(|| {
        let workspace = verification_report
            .proof_workspace
            .as_ref()
            .expect("a completed FormalSQL certificate has a proof workspace");
        let agent = verification_report
            .proof_agent
            .as_ref()
            .expect("a completed FormalSQL certificate has a final agent run");
        Evidence::FormalSqlCountermodel {
            problem_path: workspace.problem_path.clone(),
            goal_path: workspace.goal_path.clone(),
            problem_sha256: agent.candidate_problem_sha256.clone(),
            context_manifest_sha256: agent.context_manifest_sha256.clone(),
            authority_closure_sha256: agent
                .authority_closure_sha256
                .clone()
                .expect("a completed FormalSQL certificate binds its authority closure"),
            trusted_check_exit_code: agent
                .proof_check_exit_code
                .filter(|code| *code == 0)
                .expect("a completed FormalSQL certificate has a successful trusted check"),
            theorem: "generated_verification_certificate".to_owned(),
        }
    });
    let report = SolverReport::finished(
        outcome,
        status_reason,
        counterexample_report.rounds,
        counterexample,
        Some(verification_report),
        artifacts.root().display().to_string(),
        started,
    )?;
    artifacts.write_json("report.json", &report)?;
    Ok(report)
}

fn final_solver_outcome(
    certification: Option<CertificationLevel>,
    counterexample_status: SearchStatus,
) -> SolverOutcome {
    match certification {
        Some(CertificationLevel::SafeUnconditional) => SolverOutcome::SafeUnconditional,
        Some(CertificationLevel::OutcomeUnconditional) => SolverOutcome::OutcomeUnconditional,
        Some(CertificationLevel::ConditionalDerived) => SolverOutcome::ConditionalDerived,
        Some(CertificationLevel::ConditionalExternal) => SolverOutcome::ConditionalExternal,
        Some(CertificationLevel::FormalCountermodel) => SolverOutcome::NotEquivalent,
        None if counterexample_status == SearchStatus::NeedsManualReview => {
            SolverOutcome::NeedsManualReview
        }
        None => SolverOutcome::EquivalenceVerificationIncomplete,
    }
}

fn proof_handoff_resolution(report: &SearchReport) -> Result<ProofHandoffResolution> {
    match (report.outcome, report.formal_witness_snapshot.clone()) {
        (SearchStatus::MaybeEquivalent, Some(snapshot)) => {
            Ok(ProofHandoffResolution::RestartWithFormalWitness {
                feedback: report.reason.clone(),
                snapshot,
            })
        }
        (SearchStatus::NeedsManualReview, None) => Ok(ProofHandoffResolution::NeedsManualReview(
            report.reason.clone(),
        )),
        (SearchStatus::MaybeEquivalent, None) => {
            Ok(ProofHandoffResolution::Continue(report.reason.clone()))
        }
        (status, snapshot) => Err(Error::ProposalCommand(format!(
            "proof-directed counterexample search returned inconsistent host state: status {status:?}, typed snapshot present={} ",
            snapshot.is_some()
        ))),
    }
}

pub(super) fn now_ms_since_epoch() -> u128 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|duration| duration.as_millis())
        .unwrap_or(0)
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use super::{ProofHandoffResolution, final_solver_outcome, proof_handoff_resolution};
    use crate::engine::report::{CertificationLevel, SearchReport, SearchStatus, SolverOutcome};
    use crate::validation::FormalWitnessSnapshot;

    #[test]
    fn proof_handoff_restarts_only_with_a_typed_formal_witness() {
        let mut report = SearchReport::finished(
            SearchStatus::MaybeEquivalent,
            "formal observation required".to_owned(),
            Vec::new(),
            None,
            Instant::now(),
        )
        .expect("search report");

        match proof_handoff_resolution(&report).expect("ordinary no-candidate routing") {
            ProofHandoffResolution::Continue(feedback) => {
                assert_eq!(feedback, "formal observation required")
            }
            _ => panic!("a handoff without a typed snapshot must remain fail-closed"),
        }

        report.outcome = SearchStatus::NeedsManualReview;
        report.reason =
            "the suspected counterexample requires an unavailable symbolic witness".to_owned();
        match proof_handoff_resolution(&report).expect("manual-review routing") {
            ProofHandoffResolution::NeedsManualReview(reason) => assert_eq!(
                reason,
                "the suspected counterexample requires an unavailable symbolic witness"
            ),
            _ => panic!("manual review without a typed snapshot must stop uncertified"),
        }

        let snapshot = FormalWitnessSnapshot {
            schema_version: 1,
            tables: Vec::new(),
        };
        report.outcome = SearchStatus::MaybeEquivalent;
        report.reason = "typed witness materialized".to_owned();
        report.formal_witness_snapshot = Some(snapshot.clone());
        match proof_handoff_resolution(&report).expect("typed-witness routing") {
            ProofHandoffResolution::RestartWithFormalWitness {
                feedback,
                snapshot: observed,
            } => {
                assert_eq!(feedback, "typed witness materialized");
                assert_eq!(observed, snapshot);
            }
            _ => panic!("a typed snapshot must request a fresh fixed-witness proof"),
        }

        report.outcome = SearchStatus::NotEquivalent;
        report.formal_witness_snapshot = None;
        assert!(
            proof_handoff_resolution(&report).is_err(),
            "an untrusted NEQ status without a typed snapshot must fail closed"
        );
    }

    #[test]
    fn unresolved_manual_review_survives_proof_while_certificates_take_priority() {
        assert_eq!(
            final_solver_outcome(None, SearchStatus::NeedsManualReview),
            SolverOutcome::NeedsManualReview
        );
        assert_eq!(
            final_solver_outcome(None, SearchStatus::MaybeEquivalent),
            SolverOutcome::EquivalenceVerificationIncomplete
        );
        assert_eq!(
            final_solver_outcome(None, SearchStatus::NotEquivalent),
            SolverOutcome::EquivalenceVerificationIncomplete,
            "a counterexample-stage status cannot bypass the trusted Rocq selector"
        );
        assert_eq!(
            final_solver_outcome(
                Some(CertificationLevel::OutcomeUnconditional),
                SearchStatus::NeedsManualReview,
            ),
            SolverOutcome::OutcomeUnconditional
        );
        assert_eq!(
            final_solver_outcome(
                Some(CertificationLevel::FormalCountermodel),
                SearchStatus::NeedsManualReview,
            ),
            SolverOutcome::NotEquivalent
        );
    }
}
