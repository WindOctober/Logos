use std::path::{Path, PathBuf};
use std::time::Instant;

mod reporting;

use serde::{Deserialize, Serialize};

use crate::artifacts::ArtifactWriter;
use crate::core::{
    FormalSchema, ObservationCertificateReport, VerificationInput, VerificationMode,
};
use crate::engine::config::Config;
use crate::engine::now_ms_since_epoch;
use crate::engine::report::{
    Evidence, LlmAssessmentCacheLog, LlmAssessmentCacheStatus, LlmAssessmentLog, LlmParseLog,
    LlmProviderLog, RoundOutcome, SearchReport, SearchStatus, SolverOutcome, SolverReport,
    ValidationLog, ValidationOutcome,
};
use crate::error::{Error, Result};
use crate::proposal::{
    Attempt, Candidate, Decision, Provider, build_counterexample_prompt, parse_proposal,
};
use crate::usage::{CodexInvocationUsage, LlmUsage};
use crate::validation::{
    CheckResult, OutputSchemaPreflight, OutputSchemaPreflightResult, PostgresValidator,
    WitnessCheck, witness_uses_only_allowed_dml,
};

pub(super) use reporting::CounterexampleStageResult;
use reporting::{RecordedRound, SearchRun};

const ASSESSMENT_CACHE_VERSION: u32 = 2;
const COUNTEREXAMPLE_CONTRACT_REPAIR_LIMIT: usize = 1;
const COUNTEREXAMPLE_CANDIDATE_CONTRACT: &str = "counterexample_candidate requires a non-empty witnessSql containing only top-level direct INSERT, UPDATE, or DELETE statements; if no finite executable witness can be constructed, return needs_review";

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct AssessmentIdentity {
    task_key: String,
    round: usize,
    semantic_prompt: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct LlmAssessment {
    cache_version: u32,
    request_identity: AssessmentIdentity,
    prompt: String,
    raw_output: String,
    proposal: Candidate,
}

#[derive(Debug, Clone)]
struct AssessmentLoad {
    assessment: LlmAssessment,
    log: LlmAssessmentLog,
    cumulative_usage: Option<CodexInvocationUsage>,
}

#[derive(Debug)]
struct AssessmentLoadFailure {
    log: Box<LlmAssessmentLog>,
    error: Error,
    cumulative_usage: Option<CodexInvocationUsage>,
    recoverable_contract_failure: bool,
}

struct AssessmentRequest<'a> {
    identity: AssessmentIdentity,
    prompt: String,
    prompt_path: &'a str,
    candidate_path: &'a str,
    candidate_abs_path: &'a Path,
    provider: &'a dyn Provider,
    options: &'a Config,
    artifacts: &'a ArtifactWriter,
    previous_cumulative_usage: Option<&'a CodexInvocationUsage>,
}

#[derive(Debug, Clone)]
struct AssessmentLogContext {
    round: usize,
    prompt_path: String,
    candidate_path: String,
    cache_path: PathBuf,
}

#[derive(Debug, Clone, Copy)]
struct AssessmentCacheUse {
    status: LlmAssessmentCacheStatus,
    read_elapsed_ms: Option<u128>,
    write_elapsed_ms: Option<u128>,
}

#[derive(Debug, Clone, Copy)]
struct AssessmentLogStats {
    prompt_bytes: usize,
    raw_output_bytes: usize,
    decision: Option<Decision>,
}

#[derive(Debug, Clone)]
struct ProviderLogStats {
    round: usize,
    command: Option<String>,
    session_id: Option<String>,
    session_resumed: bool,
    started_ms_since_epoch: u128,
    elapsed_ms: u128,
    success: bool,
    exit_code: Option<i32>,
    stdout_bytes: usize,
    stderr_bytes: usize,
    usage: Option<LlmUsage>,
    usage_error: Option<String>,
}

#[derive(Debug, Clone)]
struct AssessmentLogDraft<'a> {
    context: &'a AssessmentLogContext,
    cache: AssessmentCacheUse,
    stats: AssessmentLogStats,
    provider: Option<LlmProviderLog>,
}

pub(super) fn run_counterexample_search(
    input: &VerificationInput,
    formal_schema: Option<&FormalSchema>,
    observation_certificates: &ObservationCertificateReport,
    options: &Config,
    provider: &dyn Provider,
    artifacts: &ArtifactWriter,
    started: Instant,
) -> Result<CounterexampleStageResult> {
    let validator = postgres_validator(options)?;
    run_counterexample_search_with_run(
        input,
        formal_schema,
        observation_certificates,
        options,
        provider,
        &validator,
        artifacts,
        SearchRun::new(artifacts, started),
    )
}

pub(super) fn run_output_schema_preflight(
    input: &VerificationInput,
    options: &Config,
    artifacts: &ArtifactWriter,
    started: Instant,
) -> Result<Option<Box<SolverReport>>> {
    let preflight = postgres_validator(options)?.preflight_output_schema(input);
    artifacts.write_json("validation/output-schema-preflight.json", &preflight)?;
    if let Some((reason, evidence)) =
        output_schema_preflight_evidence(&preflight, options.verification_mode)?
    {
        let result = SearchRun::new(artifacts, started).finish_terminal(
            SolverOutcome::NotEquivalent,
            SearchStatus::NotEquivalent,
            reason,
            Some(evidence),
        )?;
        let CounterexampleStageResult::Terminal(report) = result else {
            unreachable!("terminal output-schema preflight continued to proof")
        };
        return Ok(Some(report));
    }
    Ok(None)
}

pub(super) fn resume_counterexample_search(
    input: &VerificationInput,
    formal_schema: Option<&FormalSchema>,
    observation_certificates: &ObservationCertificateReport,
    options: &Config,
    provider: &dyn Provider,
    artifacts: &ArtifactWriter,
    started: Instant,
    previous: &SearchReport,
    handoff_feedback: String,
) -> Result<CounterexampleStageResult> {
    let validator = postgres_validator(options)?;
    run_counterexample_search_with_run(
        input,
        formal_schema,
        observation_certificates,
        options,
        provider,
        &validator,
        artifacts,
        SearchRun::resume(
            artifacts,
            started,
            previous.rounds.clone(),
            vec![handoff_feedback],
        ),
    )
}

fn run_counterexample_search_with_run(
    input: &VerificationInput,
    formal_schema: Option<&FormalSchema>,
    observation_certificates: &ObservationCertificateReport,
    options: &Config,
    provider: &dyn Provider,
    validator: &PostgresValidator,
    artifacts: &ArtifactWriter,
    mut run: SearchRun<'_>,
) -> Result<CounterexampleStageResult> {
    let round_budget = if options.llm_assessment_only {
        1
    } else {
        options.max_counterexample_rounds.max(1)
    };
    let input_key = input.stable_cache_key();
    let first_round = run.next_round();
    let last_round = first_round.saturating_add(
        round_budget
            .saturating_mul(1 + COUNTEREXAMPLE_CONTRACT_REPAIR_LIMIT)
            .saturating_sub(1),
    );
    let mut round = first_round;
    let mut fresh_rounds_remaining = round_budget;
    let mut pending_contract_resume: Option<CodexInvocationUsage> = None;

    while fresh_rounds_remaining > 0 || pending_contract_resume.is_some() {
        let repairing_current_session = pending_contract_resume.is_some();
        if !repairing_current_session {
            fresh_rounds_remaining = fresh_rounds_remaining.saturating_sub(1);
        }
        let candidate_path = format!("rounds/{round:02}/candidate.json");
        let candidate_abs_path = artifacts.root().join(&candidate_path);
        let built_prompt = build_counterexample_prompt(
            input,
            round,
            last_round,
            round_budget,
            &run.feedback,
            &options.sql_time_zone,
            Some(observation_certificates),
            &candidate_abs_path,
        )?;
        let identity = AssessmentIdentity {
            task_key: input_key.clone(),
            round,
            semantic_prompt: built_prompt.semantic_identity().to_owned(),
        };
        let prompt = built_prompt.into_runtime();
        let prompt_path = format!("rounds/{round:02}/prompt.md");
        artifacts.write_text(&prompt_path, &prompt)?;

        let assessment_load = match load_or_generate_assessment(AssessmentRequest {
            identity,
            prompt,
            prompt_path: &prompt_path,
            candidate_path: &candidate_path,
            candidate_abs_path: &candidate_abs_path,
            provider,
            options,
            artifacts,
            previous_cumulative_usage: pending_contract_resume.as_ref(),
        }) {
            Ok(load) => load,
            Err(failure) => {
                let AssessmentLoadFailure {
                    log,
                    error,
                    cumulative_usage,
                    recoverable_contract_failure,
                } = failure;
                let outcome = if recoverable_contract_failure {
                    RoundOutcome::CandidateRejected
                } else {
                    RoundOutcome::AssessmentOnly
                };
                run.record_assessment_failure(round, *log, outcome, &error)?;
                if recoverable_contract_failure {
                    let reason = error.to_string();
                    if repairing_current_session {
                        return finish_manual_review(
                            run,
                            options.llm_assessment_only,
                            format!(
                                "counterexample agent still violated its output contract after one same-session repair: {reason}"
                            ),
                        );
                    }
                    let Some(cumulative_usage) = cumulative_usage else {
                        return finish_manual_review(
                            run,
                            options.llm_assessment_only,
                            format!(
                                "counterexample agent violated its output contract, but no validated Codex session was available for the required repair: {reason}"
                            ),
                        );
                    };
                    pending_contract_resume = Some(cumulative_usage);
                    run.feedback
                        .push(counterexample_contract_feedback(round, &reason));
                    round = round.saturating_add(1);
                    continue;
                }
                return Err(error);
            }
        };
        let AssessmentLoad {
            assessment,
            log: assessment_log,
            cumulative_usage,
        } = assessment_load;
        pending_contract_resume = None;
        let proposal = assessment.proposal.clone();
        artifacts.write_text(
            format!("rounds/{round:02}/proposal.raw.txt"),
            &assessment.raw_output,
        )?;
        let attempt = Attempt {
            round,
            prompt: assessment.prompt.clone(),
            raw_output: assessment.raw_output.clone(),
            proposal: proposal.clone(),
        };
        artifacts.write_json(format!("rounds/{round:02}/proposal.json"), &attempt)?;
        artifacts.write_json(
            format!("rounds/{round:02}/llm-assessment.json"),
            &assessment,
        )?;

        if let Some(reason) = counterexample_candidate_contract_error(&proposal) {
            run.record_round(RecordedRound::without_validation(
                round,
                assessment_log,
                proposal,
                RoundOutcome::CandidateRejected,
                Some(reason.clone()),
            ))?;
            if repairing_current_session {
                return finish_manual_review(
                    run,
                    options.llm_assessment_only,
                    format!(
                        "counterexample agent still violated its output contract after one same-session repair: {reason}"
                    ),
                );
            }
            let Some(cumulative_usage) = cumulative_usage else {
                return finish_manual_review(
                    run,
                    options.llm_assessment_only,
                    format!(
                        "counterexample agent violated its output contract, but no validated Codex session was available for the required repair: {reason}"
                    ),
                );
            };
            pending_contract_resume = Some(cumulative_usage);
            run.feedback
                .push(counterexample_contract_feedback(round, &reason));
            round = round.saturating_add(1);
            continue;
        }

        match proposal.decision {
            Decision::NoCandidate => {
                let reason = proposal.reason.clone();
                run.record_round(RecordedRound::without_validation(
                    round,
                    assessment_log,
                    proposal,
                    RoundOutcome::NoCandidate,
                    None,
                ))?;
                if options.llm_assessment_only {
                    return run.finish_terminal(
                        SolverOutcome::LlmAssessmentOnly,
                        SearchStatus::LlmAssessmentOnly,
                        format!("LLM assessment produced no counterexample candidate: {reason}"),
                        None,
                    );
                }
                return run.finish_without_counterexample(
                    SearchStatus::MaybeEquivalent,
                    format!(
                        "counterexample search produced no candidate: {reason}; resuming the same FormalSQL proof session for equivalence verification"
                    ),
                );
            }
            Decision::ManualReview => {
                let reason = proposal.reason.clone();
                run.record_round(RecordedRound::without_validation(
                    round,
                    assessment_log,
                    proposal,
                    RoundOutcome::ManualReview,
                    None,
                ))?;
                return finish_manual_review(run, options.llm_assessment_only, reason);
            }
            Decision::CounterexampleCandidate => {
                artifacts.write_text(
                    format!("rounds/{round:02}/witness.sql"),
                    &proposal.witness_sql,
                )?;
                let validation_started_ms = now_ms_since_epoch();
                let validation_started = Instant::now();
                let materialized = match formal_schema {
                    Some(formal_schema) => validator.materialize_formal_witness(
                        input,
                        &proposal.witness_sql,
                        formal_schema,
                    ),
                    None => crate::validation::WitnessValidation {
                        check: WitnessCheck {
                            schema_name: String::new(),
                            warnings: Vec::new(),
                            result: CheckResult::ValidationError {
                                message: "a candidate database cannot enter trusted countermodel verification because FormalSQL schema lowering is unavailable".to_owned(),
                            },
                        },
                        snapshot: None,
                    },
                };
                let validation = materialized.check;
                let mut snapshot_ready = false;
                if let Some(snapshot) = materialized.snapshot {
                    artifacts.write_json(
                        format!("rounds/{round:02}/formal-witness-snapshot.json"),
                        &snapshot,
                    )?;
                    run.retain_formal_witness_snapshot(snapshot);
                    snapshot_ready = true;
                }
                let validation_log = ValidationLog {
                    started_ms_since_epoch: validation_started_ms,
                    elapsed_ms: validation_started.elapsed().as_millis(),
                    result: validation_outcome(&validation),
                    warnings: validation.warnings.clone(),
                };
                artifacts.write_json(format!("rounds/{round:02}/validation.json"), &validation)?;

                if let CheckResult::WitnessMaterialized {
                    table_count,
                    row_count,
                } = &validation.result
                {
                    if !snapshot_ready {
                        return Err(Error::InvalidCandidate(
                            "PostgreSQL reported a materialized witness without returning its complete typed snapshot"
                                .to_owned(),
                        ));
                    }
                    let reason = format!(
                        "PostgreSQL accepted the candidate DML and materialized a typed FormalSQL database with {table_count} tables and {row_count} rows; PostgreSQL did not execute the query pair or decide equivalence"
                    );
                    run.record_round(RecordedRound::with_validation(
                        round,
                        assessment_log,
                        proposal,
                        validation,
                        validation_log,
                        RoundOutcome::FormalWitnessPrepared,
                        None,
                    ))?;
                    if options.llm_assessment_only {
                        return run.finish_terminal(
                            SolverOutcome::LlmAssessmentOnly,
                            SearchStatus::LlmAssessmentOnly,
                            format!(
                                "{reason}; assessment-only mode does not run the trusted Rocq selector and therefore reports no EQ/NEQ verdict"
                            ),
                            None,
                        );
                    }
                    return run.finish_without_counterexample(
                        SearchStatus::MaybeEquivalent,
                        format!(
                            "{reason}; restarting unified trusted FormalSQL verification on exactly this fixed database"
                        ),
                    );
                }

                let reason = failed_check_reason(&validation);
                run.feedback.push(format!(
                    "Round {round} failed typed witness materialization: {reason}"
                ));
                run.record_round(RecordedRound::with_validation(
                    round,
                    assessment_log,
                    proposal,
                    validation,
                    validation_log,
                    RoundOutcome::CandidateRejected,
                    Some(reason.clone()),
                ))?;
            }
        }
        round = round.saturating_add(1);
    }

    if options.llm_assessment_only {
        return run.finish_terminal(
            SolverOutcome::LlmAssessmentOnly,
            SearchStatus::LlmAssessmentOnly,
            "LLM assessment produced a candidate, but PostgreSQL could not materialize it as a complete typed FormalSQL database"
                .to_owned(),
            None,
        );
    }

    run.finish_without_counterexample(
        SearchStatus::MaybeEquivalent,
        "no complete typed witness was materialized within the counterexample round budget; resuming unified FormalSQL verification"
            .to_owned(),
    )
}

fn counterexample_candidate_contract_error(proposal: &Candidate) -> Option<String> {
    (proposal.decision == Decision::CounterexampleCandidate
        && !witness_uses_only_allowed_dml(&proposal.witness_sql))
    .then(|| COUNTEREXAMPLE_CANDIDATE_CONTRACT.to_owned())
}

fn counterexample_contract_feedback(round: usize, reason: &str) -> String {
    format!(
        "Round {round} violated the counterexample-agent output contract: {reason}. Repair candidate.json in this same Codex session. Return counterexample_candidate only with a non-empty witnessSql made exclusively of top-level direct INSERT, UPDATE, or DELETE statements. If no finite executable witness can be constructed, return needs_review."
    )
}

fn finish_manual_review(
    run: SearchRun<'_>,
    assessment_only: bool,
    reason: String,
) -> Result<CounterexampleStageResult> {
    if assessment_only {
        return run.finish_terminal(
            SolverOutcome::NeedsManualReview,
            SearchStatus::NeedsManualReview,
            reason,
            None,
        );
    }
    run.finish_without_counterexample(
        SearchStatus::NeedsManualReview,
        format!(
            "counterexample assessment requested manual review without a materialized typed witness: {reason}"
        ),
    )
}

fn postgres_validator(options: &Config) -> Result<PostgresValidator> {
    PostgresValidator::new(
        options.postgres_url.clone(),
        options.statement_timeout_ms,
        options.sql_time_zone.clone(),
        options.sql_environment,
    )
}

fn output_schema_preflight_evidence(
    preflight: &OutputSchemaPreflight,
    verification_mode: VerificationMode,
) -> Result<Option<(String, Evidence)>> {
    match &preflight.result {
        OutputSchemaPreflightResult::Compatible { .. } => Ok(None),
        OutputSchemaPreflightResult::Mismatch { mismatch } => {
            let reason = match verification_mode {
                VerificationMode::SafeUnconditional
                | VerificationMode::OutcomeUnconditional
                | VerificationMode::Conditional => {
                    "validated PostgreSQL statement outcome or output schema mismatch before agent execution"
                }
            };
            Ok(Some((
                reason.to_owned(),
                Evidence::OutputSchemaMismatch {
                    mismatch: mismatch.clone(),
                },
            )))
        }
        OutputSchemaPreflightResult::ValidationError { message } => {
            Err(Error::OutputSchemaPreflight(message.clone()))
        }
    }
}

fn load_or_generate_assessment(
    request: AssessmentRequest<'_>,
) -> std::result::Result<AssessmentLoad, AssessmentLoadFailure> {
    let AssessmentRequest {
        identity,
        prompt,
        prompt_path,
        candidate_path,
        candidate_abs_path,
        provider,
        options,
        artifacts,
        previous_cumulative_usage,
    } = request;
    let round = identity.round;
    let cache_path = assessment_cache_path(options, &identity.task_key, round);
    let log_context =
        AssessmentLogContext::new(round, prompt_path, candidate_path, cache_path.clone());
    let should_reuse = options.reuse_llm_assessment && !options.force_llm_assessment;

    // Debug runs can reuse a prior assessment, but the round artifacts still
    // get rehydrated so later validation/reporting sees the same file layout.
    if should_reuse && previous_cumulative_usage.is_none() && cache_path.exists() {
        return load_cached_assessment(&log_context, &identity, &prompt, artifacts);
    }

    generate_assessment(
        identity,
        prompt,
        candidate_abs_path,
        provider,
        artifacts,
        &log_context,
        previous_cumulative_usage,
    )
}

fn load_cached_assessment(
    context: &AssessmentLogContext,
    identity: &AssessmentIdentity,
    prompt: &str,
    artifacts: &ArtifactWriter,
) -> std::result::Result<AssessmentLoad, AssessmentLoadFailure> {
    let prompt_bytes = prompt.len();
    let cache_read_started = Instant::now();
    let text = std::fs::read_to_string(&context.cache_path).map_err(|source| {
        let error = Error::ReadAssessmentCache {
            path: context.cache_path.clone(),
            source,
        };
        let error_text = error.to_string();
        context.failure(
            error,
            AssessmentCacheUse::reused(Some(cache_read_started.elapsed().as_millis())),
            AssessmentLogStats::new(prompt_bytes, 0, None),
            None,
            LlmParseLog::failed(0, error_text),
        )
    })?;
    let cache_read_elapsed_ms = cache_read_started.elapsed().as_millis();
    let cache_use = AssessmentCacheUse::reused(Some(cache_read_elapsed_ms));

    let parse_started = Instant::now();
    let mut assessment: LlmAssessment = serde_json::from_str(&text).map_err(|source| {
        let error = Error::ParseAssessmentCache {
            path: context.cache_path.clone(),
            source,
        };
        let error_text = error.to_string();
        context.failure(
            error,
            cache_use,
            AssessmentLogStats::new(prompt_bytes, text.len(), None),
            None,
            LlmParseLog::failed(parse_started.elapsed().as_millis(), error_text),
        )
    })?;
    if let Some(reason) = assessment_identity_error(&assessment, identity) {
        let error = Error::InvalidAssessmentCache {
            path: context.cache_path.clone(),
            reason,
        };
        let error_text = error.to_string();
        return Err(context.failure(
            error,
            cache_use,
            AssessmentLogStats::from_assessment(&assessment),
            None,
            LlmParseLog::failed(parse_started.elapsed().as_millis(), error_text),
        ));
    }
    // The cached semantic result is portable across run roots, but every run
    // artifact must retain the prompt that names its own candidate output.
    assessment.prompt = prompt.to_owned();
    let parse_log = LlmParseLog::succeeded(parse_started.elapsed().as_millis());
    let stats = AssessmentLogStats::from_assessment(&assessment);

    artifacts
        .write_json(&context.candidate_path, &assessment.proposal)
        .map_err(|error| context.failure(error, cache_use, stats, None, parse_log.clone()))?;
    artifacts
        .write_text(
            format!("rounds/{:02}/llm-assessment-source.txt", context.round),
            &format!("reused {}\n", context.cache_path.display()),
        )
        .map_err(|error| context.failure(error, cache_use, stats, None, parse_log.clone()))?;

    Ok(AssessmentLoad {
        assessment,
        log: context.log(cache_use, stats, None, parse_log),
        cumulative_usage: None,
    })
}

fn assessment_identity_error(
    assessment: &LlmAssessment,
    expected: &AssessmentIdentity,
) -> Option<String> {
    if assessment.cache_version != ASSESSMENT_CACHE_VERSION {
        return Some(format!(
            "cacheVersion {} does not match expected {}",
            assessment.cache_version, ASSESSMENT_CACHE_VERSION
        ));
    }
    if assessment.request_identity.task_key != expected.task_key {
        return Some("taskKey does not match the current verification input".to_owned());
    }
    if assessment.request_identity.round != expected.round {
        return Some(format!(
            "round {} does not match expected {}",
            assessment.request_identity.round, expected.round
        ));
    }
    if assessment.request_identity.semantic_prompt != expected.semantic_prompt {
        return Some("semantic prompt does not match the current assessment request".to_owned());
    }
    None
}

fn generate_assessment(
    identity: AssessmentIdentity,
    prompt: String,
    candidate_abs_path: &Path,
    provider: &dyn Provider,
    artifacts: &ArtifactWriter,
    context: &AssessmentLogContext,
    previous_cumulative_usage: Option<&CodexInvocationUsage>,
) -> std::result::Result<AssessmentLoad, AssessmentLoadFailure> {
    let round = identity.round;
    let mut log = AssessmentLogDraft::not_written(context, prompt.len());

    // The provider is required to write the machine-readable candidate here.
    // Removing stale content prevents accidentally validating an older round.
    if let Err(source) = std::fs::remove_file(candidate_abs_path)
        && source.kind() != std::io::ErrorKind::NotFound
    {
        let error = Error::ProposalCommand(format!(
            "failed to remove stale proposal file {}: {source}",
            candidate_abs_path.display()
        ));
        return Err(log.fail_now(error));
    }

    let provider_started_ms = now_ms_since_epoch();
    let provider_started = Instant::now();
    let session_resumed = previous_cumulative_usage.is_some();
    let completion = match previous_cumulative_usage {
        Some(previous) => provider.resume(&prompt, candidate_abs_path, &previous.session_id),
        None => provider.complete(&prompt, candidate_abs_path),
    };
    let completion = match completion {
        Ok(completion) => completion,
        Err(error) => {
            log.record_provider(build_provider_log(ProviderLogStats {
                round,
                command: None,
                session_id: previous_cumulative_usage.map(|usage| usage.session_id.clone()),
                session_resumed,
                started_ms_since_epoch: provider_started_ms,
                elapsed_ms: provider_started.elapsed().as_millis(),
                success: false,
                exit_code: None,
                stdout_bytes: 0,
                stderr_bytes: 0,
                usage: None,
                usage_error: Some(error.to_string()),
            }));
            return Err(log.fail_now(error));
        }
    };
    let provider_elapsed_ms = provider_started.elapsed().as_millis();
    log.record_raw_output(completion.stdout.len());
    let (cumulative_usage, provider_usage, provider_usage_error) =
        reconcile_counterexample_usage(&completion.usage, previous_cumulative_usage);
    let session_id = cumulative_usage
        .as_ref()
        .map(|usage| usage.session_id.clone())
        .or_else(|| previous_cumulative_usage.map(|usage| usage.session_id.clone()));

    // stdout/stderr are retained for audit only; the candidate JSON is read
    // from candidate_abs_path to avoid parsing mixed prose/log output.
    log.write_provider_stderr(artifacts, &completion.stderr)?;
    log.write_raw_output(artifacts, &completion.stdout)?;

    log.record_provider(build_provider_log(ProviderLogStats {
        round,
        command: completion.command.clone(),
        session_id,
        session_resumed,
        started_ms_since_epoch: provider_started_ms,
        elapsed_ms: provider_elapsed_ms,
        success: completion.success,
        exit_code: completion.exit_code,
        stdout_bytes: completion.stdout.len(),
        stderr_bytes: completion.stderr.len(),
        usage: provider_usage,
        usage_error: provider_usage_error.clone(),
    }));
    if !completion.success {
        return Err(log.fail_now(Error::ProposalCommand(completion.stderr.trim().to_owned())));
    }
    if let Some(error) = provider_usage_error {
        return Err(log.fail_now(Error::ProposalCommand(format!(
            "Codex command succeeded without valid authoritative usage: {error}"
        ))));
    }

    let parse_started = Instant::now();
    let candidate_text = match std::fs::read_to_string(candidate_abs_path) {
        Ok(text) => text,
        Err(source) => {
            let error = Error::Read {
                path: candidate_abs_path.to_owned(),
                source,
            };
            return Err(log.fail_contract_with_elapsed(
                error,
                parse_started.elapsed().as_millis(),
                cumulative_usage.clone(),
            ));
        }
    };
    let proposal = parse_proposal(&candidate_text).map_err(|error| {
        log.fail_contract_with_elapsed(
            error,
            parse_started.elapsed().as_millis(),
            cumulative_usage.clone(),
        )
    })?;
    let parse_log = LlmParseLog::succeeded(parse_started.elapsed().as_millis());

    // Normalize the provider's JSON before downstream code and reports read it.
    log.write_candidate(artifacts, &proposal, &parse_log)?;

    let assessment = LlmAssessment {
        cache_version: ASSESSMENT_CACHE_VERSION,
        request_identity: identity,
        prompt,
        raw_output: completion.stdout,
        proposal,
    };
    log.record_stats(AssessmentLogStats::from_assessment(&assessment));

    // Cache stores the full prompt/output/proposal bundle; run artifacts keep
    // a source marker so cache hits and fresh generations are distinguishable.
    if counterexample_candidate_contract_error(&assessment.proposal).is_none() {
        log.write_assessment_cache(&assessment, &parse_log)?;
    }
    log.write_assessment_source(artifacts, "generated", &parse_log)?;

    Ok(AssessmentLoad {
        assessment,
        log: log.finish(parse_log),
        cumulative_usage,
    })
}

fn reconcile_counterexample_usage(
    parsed: &std::result::Result<CodexInvocationUsage, crate::usage::UsageError>,
    previous: Option<&CodexInvocationUsage>,
) -> (
    Option<CodexInvocationUsage>,
    Option<LlmUsage>,
    Option<String>,
) {
    let record = match parsed {
        Ok(record) => record,
        Err(error) => return (None, None, Some(error.to_string())),
    };
    if !is_codex_session_id(&record.session_id) {
        return (
            None,
            None,
            Some(format!(
                "Codex thread.started returned malformed session UUID {:?}",
                record.session_id
            )),
        );
    }
    let mut cumulative = record.clone();
    cumulative.session_id.make_ascii_lowercase();
    match cumulative.incremental_usage(previous) {
        Ok(increment) => (Some(cumulative), Some(increment), None),
        Err(error) => (None, None, Some(error.to_string())),
    }
}

fn is_codex_session_id(value: &str) -> bool {
    value.len() == 36
        && value.bytes().enumerate().all(|(index, byte)| {
            if matches!(index, 8 | 13 | 18 | 23) {
                byte == b'-'
            } else {
                byte.is_ascii_hexdigit()
            }
        })
}

impl AssessmentLogContext {
    fn new(round: usize, prompt_path: &str, candidate_path: &str, cache_path: PathBuf) -> Self {
        Self {
            round,
            prompt_path: prompt_path.to_owned(),
            candidate_path: candidate_path.to_owned(),
            cache_path,
        }
    }

    fn log(
        &self,
        cache: AssessmentCacheUse,
        stats: AssessmentLogStats,
        provider: Option<LlmProviderLog>,
        parse: LlmParseLog,
    ) -> LlmAssessmentLog {
        LlmAssessmentLog {
            round: self.round,
            cache: LlmAssessmentCacheLog {
                status: cache.status,
                path: self.cache_path.display().to_string(),
                read_elapsed_ms: cache.read_elapsed_ms,
                write_elapsed_ms: cache.write_elapsed_ms,
            },
            prompt_path: self.prompt_path.clone(),
            assessment_path: format!("rounds/{:02}/llm-assessment.json", self.round),
            raw_output_path: format!("rounds/{:02}/proposal.raw.txt", self.round),
            proposal_path: format!("rounds/{:02}/proposal.json", self.round),
            candidate_path: self.candidate_path.clone(),
            prompt_bytes: stats.prompt_bytes,
            raw_output_bytes: stats.raw_output_bytes,
            decision: stats.decision,
            provider,
            parse,
        }
    }

    fn failure(
        &self,
        error: Error,
        cache: AssessmentCacheUse,
        stats: AssessmentLogStats,
        provider: Option<LlmProviderLog>,
        parse: LlmParseLog,
    ) -> AssessmentLoadFailure {
        AssessmentLoadFailure {
            log: Box::new(self.log(cache, stats, provider, parse)),
            error,
            cumulative_usage: None,
            recoverable_contract_failure: false,
        }
    }
}

impl AssessmentCacheUse {
    fn reused(read_elapsed_ms: Option<u128>) -> Self {
        Self {
            status: LlmAssessmentCacheStatus::Reused,
            read_elapsed_ms,
            write_elapsed_ms: None,
        }
    }

    fn generated(write_elapsed_ms: u128) -> Self {
        Self {
            status: LlmAssessmentCacheStatus::Generated,
            read_elapsed_ms: None,
            write_elapsed_ms: Some(write_elapsed_ms),
        }
    }

    fn not_written() -> Self {
        Self {
            status: LlmAssessmentCacheStatus::NotWritten,
            read_elapsed_ms: None,
            write_elapsed_ms: None,
        }
    }

    fn not_written_with_write_elapsed(write_elapsed_ms: u128) -> Self {
        Self {
            status: LlmAssessmentCacheStatus::NotWritten,
            read_elapsed_ms: None,
            write_elapsed_ms: Some(write_elapsed_ms),
        }
    }
}

impl AssessmentLogStats {
    fn new(prompt_bytes: usize, raw_output_bytes: usize, decision: Option<Decision>) -> Self {
        Self {
            prompt_bytes,
            raw_output_bytes,
            decision,
        }
    }

    fn from_assessment(assessment: &LlmAssessment) -> Self {
        Self {
            prompt_bytes: assessment.prompt.len(),
            raw_output_bytes: assessment.raw_output.len(),
            decision: Some(assessment.proposal.decision),
        }
    }
}

impl<'a> AssessmentLogDraft<'a> {
    fn not_written(context: &'a AssessmentLogContext, prompt_bytes: usize) -> Self {
        // Carries the evolving log state through generation so error paths only
        // report the failing action instead of rebuilding the full log object.
        Self {
            context,
            cache: AssessmentCacheUse::not_written(),
            stats: AssessmentLogStats::new(prompt_bytes, 0, None),
            provider: None,
        }
    }

    fn record_raw_output(&mut self, raw_output_bytes: usize) {
        self.stats.raw_output_bytes = raw_output_bytes;
    }

    fn record_decision(&mut self, decision: Decision) {
        self.stats.decision = Some(decision);
    }

    fn record_stats(&mut self, stats: AssessmentLogStats) {
        self.stats = stats;
    }

    fn record_provider(&mut self, provider: LlmProviderLog) {
        self.provider = Some(provider);
    }

    fn record_cache(&mut self, cache: AssessmentCacheUse) {
        self.cache = cache;
    }

    fn write_provider_stderr(
        &self,
        artifacts: &ArtifactWriter,
        stderr: &str,
    ) -> std::result::Result<(), AssessmentLoadFailure> {
        self.write_round_text(artifacts, "llm-provider.stderr.txt", stderr)
    }

    fn write_raw_output(
        &self,
        artifacts: &ArtifactWriter,
        stdout: &str,
    ) -> std::result::Result<(), AssessmentLoadFailure> {
        self.write_round_text(artifacts, "proposal.raw.txt", stdout)
    }

    fn write_round_text(
        &self,
        artifacts: &ArtifactWriter,
        file_name: &str,
        text: &str,
    ) -> std::result::Result<(), AssessmentLoadFailure> {
        artifacts
            .write_text(
                format!("rounds/{:02}/{file_name}", self.context.round),
                text,
            )
            .map_err(|error| self.fail_now(error))
    }

    fn write_candidate(
        &mut self,
        artifacts: &ArtifactWriter,
        proposal: &Candidate,
        parse: &LlmParseLog,
    ) -> std::result::Result<(), AssessmentLoadFailure> {
        self.record_decision(proposal.decision);
        artifacts
            .write_json(&self.context.candidate_path, proposal)
            .map_err(|error| self.failure(error, parse.clone()))
    }

    fn write_assessment_cache(
        &mut self,
        assessment: &LlmAssessment,
        parse: &LlmParseLog,
    ) -> std::result::Result<(), AssessmentLoadFailure> {
        let started = Instant::now();
        match write_assessment_cache(&self.context.cache_path, assessment) {
            Ok(()) => {
                self.record_cache(AssessmentCacheUse::generated(started.elapsed().as_millis()));
                Ok(())
            }
            Err(error) => {
                self.record_cache(AssessmentCacheUse::not_written_with_write_elapsed(
                    started.elapsed().as_millis(),
                ));
                Err(self.failure(error, parse.clone()))
            }
        }
    }

    fn write_assessment_source(
        &self,
        artifacts: &ArtifactWriter,
        source: &str,
        parse: &LlmParseLog,
    ) -> std::result::Result<(), AssessmentLoadFailure> {
        artifacts
            .write_text(
                format!("rounds/{:02}/llm-assessment-source.txt", self.context.round),
                &format!("{source} {}\n", self.context.cache_path.display()),
            )
            .map_err(|error| self.failure(error, parse.clone()))
    }

    fn fail_now(&self, error: Error) -> AssessmentLoadFailure {
        self.fail_with_elapsed(error, 0)
    }

    fn fail_with_elapsed(&self, error: Error, elapsed_ms: u128) -> AssessmentLoadFailure {
        let error_text = error.to_string();
        self.failure(error, LlmParseLog::failed(elapsed_ms, error_text))
    }

    fn fail_contract_with_elapsed(
        &self,
        error: Error,
        elapsed_ms: u128,
        cumulative_usage: Option<CodexInvocationUsage>,
    ) -> AssessmentLoadFailure {
        let error_text = error.to_string();
        let mut failure = self.failure(error, LlmParseLog::failed(elapsed_ms, error_text));
        failure.cumulative_usage = cumulative_usage;
        failure.recoverable_contract_failure = true;
        failure
    }

    fn failure(&self, error: Error, parse: LlmParseLog) -> AssessmentLoadFailure {
        self.context
            .failure(error, self.cache, self.stats, self.provider.clone(), parse)
    }

    fn finish(&self, parse: LlmParseLog) -> LlmAssessmentLog {
        self.context
            .log(self.cache, self.stats, self.provider.clone(), parse)
    }
}

impl LlmParseLog {
    fn succeeded(elapsed_ms: u128) -> Self {
        Self {
            elapsed_ms,
            success: true,
            error: None,
        }
    }

    fn failed(elapsed_ms: u128, error: impl Into<String>) -> Self {
        Self {
            elapsed_ms,
            success: false,
            error: Some(error.into()),
        }
    }
}

fn build_provider_log(stats: ProviderLogStats) -> LlmProviderLog {
    LlmProviderLog {
        command: stats.command,
        session_id: stats.session_id,
        session_resumed: stats.session_resumed,
        started_ms_since_epoch: stats.started_ms_since_epoch,
        elapsed_ms: stats.elapsed_ms,
        success: stats.success,
        exit_code: stats.exit_code,
        stdout_bytes: stats.stdout_bytes,
        stderr_bytes: stats.stderr_bytes,
        stderr_path: format!("rounds/{:02}/llm-provider.stderr.txt", stats.round),
        events_path: format!("rounds/{:02}/proposal.raw.txt", stats.round),
        usage: stats.usage,
        usage_error: stats.usage_error,
    }
}

fn assessment_cache_path(options: &Config, task_key: &str, round: usize) -> std::path::PathBuf {
    options
        .llm_assessment_cache_dir
        .join(task_key)
        .join(format!("round-{round:02}.json"))
}

fn write_assessment_cache(path: &std::path::Path, assessment: &LlmAssessment) -> Result<()> {
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent).map_err(|source| Error::CreateDir {
            path: parent.to_owned(),
            source,
        })?;
    }
    let text = serde_json::to_string_pretty(assessment)? + "\n";
    std::fs::write(path, text).map_err(|source| Error::WriteAssessmentCache {
        path: path.to_owned(),
        source,
    })
}

fn validation_outcome(validation: &WitnessCheck) -> ValidationOutcome {
    match &validation.result {
        CheckResult::WitnessMaterialized { .. } => ValidationOutcome::WitnessMaterialized,
        #[cfg(test)]
        CheckResult::DataDifference { .. } => ValidationOutcome::DataDifference,
        #[cfg(test)]
        CheckResult::RowSequenceDifference { .. } => ValidationOutcome::RowSequenceDifference,
        #[cfg(test)]
        CheckResult::InconclusiveObservation { .. } => ValidationOutcome::InconclusiveObservation,
        #[cfg(test)]
        CheckResult::OutputSchemaMismatch { .. } => ValidationOutcome::OutputSchemaMismatch,
        #[cfg(test)]
        CheckResult::NoDifference => ValidationOutcome::NoDifference,
        CheckResult::ValidationError { .. } => ValidationOutcome::ValidationError,
    }
}

fn failed_check_reason(validation: &WitnessCheck) -> String {
    match &validation.result {
        CheckResult::WitnessMaterialized { .. } => {
            "candidate database was materialized successfully".to_owned()
        }
        CheckResult::ValidationError { message } => message.clone(),
        #[cfg(test)]
        CheckResult::NoDifference => {
            "legacy PostgreSQL query comparison found no concrete difference; this result is not used by the production countermodel path"
                .to_owned()
        }
        #[cfg(test)]
        CheckResult::InconclusiveObservation { reason, .. } => format!(
            "legacy PostgreSQL query comparison was inconclusive and is not authoritative: {reason}"
        ),
        #[cfg(test)]
        CheckResult::DataDifference { .. } | CheckResult::RowSequenceDifference { .. } => {
            "legacy PostgreSQL query comparison produced a concrete difference, but executor observations cannot decide EQ/NEQ"
                .to_owned()
        }
        #[cfg(test)]
        CheckResult::OutputSchemaMismatch { .. } => {
            "output schema mismatch must be handled by the static preflight before witness synthesis"
                .to_owned()
        }
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Mutex;
    use std::sync::atomic::{AtomicU64, Ordering};

    use super::*;
    use crate::core::{SqlEnvironment, SqlTimeZone, VerificationMode};
    use crate::proposal::Completion;
    use crate::usage::CodexInvocationUsage;
    use crate::validation::{OutputColumn, OutputSchema, SchemaMismatch};

    static NEXT_TEST_DIRECTORY: AtomicU64 = AtomicU64::new(0);

    struct TestDirectory(PathBuf);

    impl TestDirectory {
        fn new(label: &str) -> Self {
            let sequence = NEXT_TEST_DIRECTORY.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!(
                "logos-solver-{label}-{}-{sequence}",
                std::process::id()
            ));
            std::fs::create_dir_all(&path).expect("create test directory");
            Self(path)
        }

        fn path(&self) -> &Path {
            &self.0
        }
    }

    impl Drop for TestDirectory {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    fn verification_input(root: &Path, source_sql: &str) -> VerificationInput {
        let schema = root.join("schema.sql");
        let source = root.join("source.sql");
        let target = root.join("target.sql");
        std::fs::write(&schema, "CREATE TABLE t (x TIMESTAMP);\n").expect("write schema");
        std::fs::write(&source, source_sql).expect("write source");
        std::fs::write(&target, "SELECT x FROM t;\n").expect("write target");
        VerificationInput::read_with_environment(schema, source, target, SqlEnvironment::default())
            .expect("read verification input")
    }

    fn prompt_and_identity(
        input: &VerificationInput,
        time_zone: &str,
        output_path: &Path,
    ) -> (String, AssessmentIdentity) {
        let prompt = build_counterexample_prompt(
            input,
            2,
            3,
            3,
            &["prior semantic feedback".to_owned()],
            &SqlTimeZone::parse(time_zone),
            None,
            output_path,
        )
        .expect("build prompt");
        let identity = AssessmentIdentity {
            task_key: input.stable_cache_key(),
            round: 2,
            semantic_prompt: prompt.semantic_identity().to_owned(),
        };
        (prompt.into_runtime(), identity)
    }

    fn assessment(identity: AssessmentIdentity, prompt: String) -> LlmAssessment {
        LlmAssessment {
            cache_version: ASSESSMENT_CACHE_VERSION,
            request_identity: identity,
            prompt,
            raw_output: String::new(),
            proposal: Candidate {
                decision: Decision::NoCandidate,
                reason: String::new(),
                witness_sql: String::new(),
                notes: String::new(),
            },
        }
    }

    struct ContractRepairProvider {
        first_candidate: String,
        second_candidate: String,
        calls: Mutex<Vec<String>>,
    }

    impl ContractRepairProvider {
        const SESSION_ID: &'static str = "019fa8c6-b1d2-7841-a064-5202662bf9e4";

        fn new(first_candidate: impl Into<String>) -> Self {
            Self {
                first_candidate: first_candidate.into(),
                second_candidate: r#"{"decision":"needs_review","reason":"no finite executable witness","witnessSql":""}"#.to_owned(),
                calls: Mutex::new(Vec::new()),
            }
        }

        fn with_second(
            first_candidate: impl Into<String>,
            second_candidate: impl Into<String>,
        ) -> Self {
            Self {
                first_candidate: first_candidate.into(),
                second_candidate: second_candidate.into(),
                calls: Mutex::new(Vec::new()),
            }
        }

        fn completion_for(
            session_id: &str,
            command: &str,
            input: u64,
            cached: u64,
            output: u64,
        ) -> Completion {
            Completion {
                command: Some(command.to_owned()),
                stdout: format!(
                    "{{\"type\":\"thread.started\",\"thread_id\":\"{}\"}}\n",
                    session_id
                ),
                stderr: String::new(),
                exit_code: Some(0),
                success: true,
                usage: Ok(CodexInvocationUsage {
                    session_id: session_id.to_owned(),
                    usage: LlmUsage::from_counts(input, cached, output)
                        .expect("valid fake cumulative usage"),
                }),
            }
        }

        fn completion(command: &str, input: u64, cached: u64, output: u64) -> Completion {
            Self::completion_for(Self::SESSION_ID, command, input, cached, output)
        }
    }

    impl Provider for ContractRepairProvider {
        fn complete(&self, _prompt: &str, output_path: &Path) -> Result<Completion> {
            self.calls
                .lock()
                .expect("lock calls")
                .push("fresh".to_owned());
            std::fs::write(output_path, &self.first_candidate).map_err(|source| Error::Write {
                path: output_path.to_owned(),
                source,
            })?;
            Ok(Self::completion("codex exec", 100, 50, 10))
        }

        fn resume(&self, prompt: &str, output_path: &Path, session_id: &str) -> Result<Completion> {
            assert_eq!(session_id, Self::SESSION_ID);
            assert!(prompt.contains("non-empty witnessSql"));
            assert!(prompt.contains("return needs_review"));
            assert!(
                !output_path.exists(),
                "host must remove a stale repair candidate before resuming"
            );
            self.calls
                .lock()
                .expect("lock calls")
                .push(format!("resume:{session_id}"));
            std::fs::write(output_path, &self.second_candidate).map_err(|source| Error::Write {
                path: output_path.to_owned(),
                source,
            })?;
            Ok(Self::completion("codex exec resume", 140, 70, 20))
        }
    }

    struct PerSessionRepairProvider {
        step: Mutex<usize>,
    }

    impl PerSessionRepairProvider {
        const SESSION_A: &'static str = "019fa8c6-b1d2-7841-a064-5202662bf9e4";
        const SESSION_B: &'static str = "019fa8c6-b1d2-7841-a064-5202662bf9e5";

        fn write(output_path: &Path, text: &str) -> Result<()> {
            std::fs::write(output_path, text).map_err(|source| Error::Write {
                path: output_path.to_owned(),
                source,
            })
        }
    }

    impl Provider for PerSessionRepairProvider {
        fn complete(&self, _prompt: &str, output_path: &Path) -> Result<Completion> {
            let mut step = self.step.lock().expect("lock provider step");
            let result = match *step {
                0 => {
                    Self::write(
                        output_path,
                        r#"{"decision":"counterexample_candidate","reason":"missing witness","witnessSql":""}"#,
                    )?;
                    ContractRepairProvider::completion_for(
                        Self::SESSION_A,
                        "codex exec",
                        100,
                        50,
                        10,
                    )
                }
                2 => {
                    Self::write(output_path, r#"{"decision":"obsolete"}"#)?;
                    ContractRepairProvider::completion_for(
                        Self::SESSION_B,
                        "codex exec",
                        200,
                        100,
                        20,
                    )
                }
                other => panic!("unexpected fresh provider step {other}"),
            };
            *step += 1;
            Ok(result)
        }

        fn resume(
            &self,
            _prompt: &str,
            output_path: &Path,
            session_id: &str,
        ) -> Result<Completion> {
            let mut step = self.step.lock().expect("lock provider step");
            let result = match *step {
                1 => {
                    assert_eq!(session_id, Self::SESSION_A);
                    Self::write(
                        output_path,
                        r#"{"decision":"counterexample_candidate","reason":"executable but rejected by validation","witnessSql":"INSERT INTO t VALUES (NULL);"}"#,
                    )?;
                    ContractRepairProvider::completion_for(
                        Self::SESSION_A,
                        "codex exec resume",
                        140,
                        70,
                        20,
                    )
                }
                3 => {
                    assert_eq!(session_id, Self::SESSION_B);
                    Self::write(
                        output_path,
                        r#"{"decision":"needs_review","reason":"no finite executable witness","witnessSql":""}"#,
                    )?;
                    ContractRepairProvider::completion_for(
                        Self::SESSION_B,
                        "codex exec resume",
                        240,
                        120,
                        30,
                    )
                }
                other => panic!("unexpected resume provider step {other}"),
            };
            *step += 1;
            Ok(result)
        }
    }

    fn counterexample_test_options(root: &Path) -> Config {
        Config {
            calcite_ir_command: String::new(),
            transform_only: false,
            typed_witness_empty_audit: false,
            disable_counterexample_search: false,
            llm_assessment_only: false,
            reuse_llm_assessment: false,
            force_llm_assessment: true,
            llm_assessment_cache_dir: root.join("assessment-cache"),
            proposal_command: "codex exec".to_owned(),
            proposal_resume_command: "codex exec resume {session_id}".to_owned(),
            max_counterexample_rounds: 1,
            postgres_url: Some("postgresql://unused.invalid/logos".to_owned()),
            statement_timeout_ms: 1_000,
            sql_time_zone: SqlTimeZone::utc(),
            sql_environment: SqlEnvironment::default(),
            verification_mode: VerificationMode::OutcomeUnconditional,
            run_proof_agent: false,
            proof_agent_command: String::new(),
            proof_agent_resume_command: String::new(),
            proof_agent_memory_limit_mib: 512,
            proof_agent_storage_limit_mib: 512,
            proof_agent_timeout_seconds: 1,
            proof_check_timeout_seconds: 1,
            proof_docker_image: String::new(),
            proof_rocq_opam_switch: None,
            logos_repo_root: None,
        }
    }

    fn empty_observation_certificates(input: &VerificationInput) -> ObservationCertificateReport {
        ObservationCertificateReport {
            schema_version: 1,
            verification_input_key: input.stable_cache_key(),
            verification_input_sha256: "test-input".to_owned(),
            lowering_sha256: "test-lowering".to_owned(),
            source: Vec::new(),
            target: Vec::new(),
        }
    }

    fn output_schema(type_oid: u32, type_name: &str) -> OutputSchema {
        OutputSchema {
            columns: vec![OutputColumn {
                ordinal: 1,
                name: "value".to_owned(),
                type_oid,
                type_modifier: -1,
                type_name: type_name.to_owned(),
            }],
        }
    }

    #[test]
    fn manual_review_is_carried_to_the_proof_runner_except_in_assessment_only_mode() {
        let full_root = TestDirectory::new("manual-review-full");
        let full_artifacts = ArtifactWriter::new(Some(full_root.path().to_owned()))
            .expect("create full-flow artifacts");
        let full_result = finish_manual_review(
            SearchRun::new(&full_artifacts, Instant::now()),
            false,
            "candidate needs proof-level reasoning".to_owned(),
        )
        .expect("finish full-flow manual review");
        let CounterexampleStageResult::ProceedToProof(report) = full_result else {
            panic!("manual review must be carried to the proof-runner boundary")
        };
        assert_eq!(report.outcome, SearchStatus::NeedsManualReview);
        assert!(report.reason.contains("requested manual review"));
        assert!(!report.reason.contains("resuming"));

        let assessment_root = TestDirectory::new("manual-review-assessment-only");
        let assessment_artifacts = ArtifactWriter::new(Some(assessment_root.path().to_owned()))
            .expect("create assessment-only artifacts");
        let assessment_result = finish_manual_review(
            SearchRun::new(&assessment_artifacts, Instant::now()),
            true,
            "manual classification requested".to_owned(),
        )
        .expect("finish assessment-only manual review");
        let CounterexampleStageResult::Terminal(report) = assessment_result else {
            panic!("assessment-only mode must remain terminal")
        };
        assert_eq!(report.outcome, SolverOutcome::NeedsManualReview);
    }

    fn assert_contract_failure_resumes_same_session(first_candidate: &str) {
        let root = TestDirectory::new("counterexample-contract-resume");
        let input = verification_input(root.path(), "SELECT x FROM t;\n");
        let artifacts =
            ArtifactWriter::new(Some(root.path().join("artifacts"))).expect("create artifacts");
        let stale_repair = artifacts.root().join("rounds/02/candidate.json");
        std::fs::create_dir_all(stale_repair.parent().expect("repair parent"))
            .expect("create repair directory");
        std::fs::write(&stale_repair, "stale candidate must not be reused")
            .expect("write stale repair candidate");
        let options = counterexample_test_options(root.path());
        let provider = ContractRepairProvider::new(first_candidate);
        let result = run_counterexample_search(
            &input,
            None,
            &empty_observation_certificates(&input),
            &options,
            &provider,
            &artifacts,
            Instant::now(),
        )
        .expect("contract failure must become a bounded repair");
        let CounterexampleStageResult::ProceedToProof(report) = result else {
            panic!("needs_review repair must reach the proof-runner boundary")
        };
        assert_eq!(report.outcome, SearchStatus::NeedsManualReview);
        assert_eq!(report.rounds.len(), 2);
        assert_eq!(report.llm_usage.input_tokens, 140);
        assert_eq!(report.llm_usage.cached_input_tokens, 70);
        assert_eq!(report.llm_usage.output_tokens, 20);
        assert_eq!(
            provider.calls.lock().expect("lock calls").as_slice(),
            [
                "fresh".to_owned(),
                format!("resume:{}", ContractRepairProvider::SESSION_ID),
            ]
        );
        let first = &report.rounds[0].assessment.provider.as_ref().unwrap();
        let second = &report.rounds[1].assessment.provider.as_ref().unwrap();
        assert!(!first.session_resumed);
        assert!(second.session_resumed);
        assert_eq!(
            first.session_id.as_deref(),
            Some(ContractRepairProvider::SESSION_ID)
        );
        assert_eq!(second.session_id, first.session_id);
        assert_eq!(first.usage.as_ref().unwrap().input_tokens, 100);
        assert_eq!(second.usage.as_ref().unwrap().input_tokens, 40);
        let first_round: serde_json::Value = serde_json::from_str(
            &std::fs::read_to_string(artifacts.root().join("rounds/01/round-report.json"))
                .expect("read rejected round report"),
        )
        .expect("parse rejected round report");
        assert_eq!(first_round["outcome"], "candidate_rejected");
    }

    #[test]
    fn empty_candidate_contract_resumes_once_in_the_same_session() {
        assert_contract_failure_resumes_same_session(
            r#"{"decision":"counterexample_candidate","reason":"empty database","witnessSql":""}"#,
        );
    }

    #[test]
    fn malformed_decision_contract_resumes_once_in_the_same_session() {
        assert_contract_failure_resumes_same_session(
            r#"{"decision":"not_eq","reason":"obsolete decision","witnessSql":"INSERT INTO t VALUES (1);"}"#,
        );
    }

    #[test]
    fn a_second_contract_violation_becomes_needs_manual_review() {
        let root = TestDirectory::new("counterexample-contract-repeat");
        let input = verification_input(root.path(), "SELECT x FROM t;\n");
        let artifacts =
            ArtifactWriter::new(Some(root.path().join("artifacts"))).expect("create artifacts");
        let invalid = r#"{"decision":"counterexample_candidate","reason":"missing executable witness","witnessSql":""}"#;
        let provider = ContractRepairProvider::with_second(invalid, invalid);
        let result = run_counterexample_search(
            &input,
            None,
            &empty_observation_certificates(&input),
            &counterexample_test_options(root.path()),
            &provider,
            &artifacts,
            Instant::now(),
        )
        .expect("repeated contract failure must be a semantic status, not an error");
        let CounterexampleStageResult::ProceedToProof(report) = result else {
            panic!("full flow must retain proof as an option")
        };
        assert_eq!(report.outcome, SearchStatus::NeedsManualReview);
        assert!(report.reason.contains("after one same-session repair"));
        assert_eq!(report.rounds.len(), 2);
        assert_eq!(report.llm_usage.input_tokens, 140);
    }

    #[test]
    fn each_fresh_round_receives_its_own_non_consuming_contract_repair() {
        let root = TestDirectory::new("counterexample-contract-per-session");
        let input = verification_input(root.path(), "SELECT x FROM t;\n");
        let artifacts =
            ArtifactWriter::new(Some(root.path().join("artifacts"))).expect("create artifacts");
        let mut options = counterexample_test_options(root.path());
        options.max_counterexample_rounds = 2;
        options.postgres_url = Some("postgresql://127.0.0.1:1/logos".to_owned());
        let provider = PerSessionRepairProvider {
            step: Mutex::new(0),
        };
        let result = run_counterexample_search(
            &input,
            None,
            &empty_observation_certificates(&input),
            &options,
            &provider,
            &artifacts,
            Instant::now(),
        )
        .expect("each fresh session must receive one bounded contract repair");
        let CounterexampleStageResult::ProceedToProof(report) = result else {
            panic!("needs_review must reach the proof-runner boundary")
        };
        assert_eq!(report.outcome, SearchStatus::NeedsManualReview);
        assert_eq!(report.rounds.len(), 4);
        assert_eq!(*provider.step.lock().expect("lock provider step"), 4);
        assert_eq!(report.llm_usage.input_tokens, 380);
        assert_eq!(
            report.rounds[0]
                .assessment
                .provider
                .as_ref()
                .unwrap()
                .session_id
                .as_deref(),
            Some(PerSessionRepairProvider::SESSION_A)
        );
        assert_eq!(
            report.rounds[2]
                .assessment
                .provider
                .as_ref()
                .unwrap()
                .session_id
                .as_deref(),
            Some(PerSessionRepairProvider::SESSION_B)
        );
    }

    #[test]
    fn compatible_output_schema_preflight_continues_to_llm_search() {
        let preflight = OutputSchemaPreflight {
            schema_name: "logos_preflight".to_owned(),
            result: OutputSchemaPreflightResult::Compatible {
                source: Vec::new(),
                target: Vec::new(),
            },
        };

        assert!(
            output_schema_preflight_evidence(&preflight, VerificationMode::OutcomeUnconditional,)
                .expect("compatible preflight")
                .is_none()
        );
    }

    #[test]
    fn output_schema_mismatch_preflight_is_terminal_without_witness_sql() {
        let mismatch = SchemaMismatch::StatementOutput {
            reason: "source is numeric, target is int8".to_owned(),
            statement: 1,
            source: output_schema(1700, "numeric"),
            target: output_schema(20, "int8"),
        };
        let preflight = OutputSchemaPreflight {
            schema_name: "logos_preflight".to_owned(),
            result: OutputSchemaPreflightResult::Mismatch {
                mismatch: mismatch.clone(),
            },
        };

        let (reason, evidence) =
            output_schema_preflight_evidence(&preflight, VerificationMode::OutcomeUnconditional)
                .expect("mismatch preflight")
                .expect("terminal evidence");
        assert!(reason.contains("before agent execution"));
        match evidence {
            Evidence::OutputSchemaMismatch { mismatch: observed } => {
                assert_eq!(observed.reason(), mismatch.reason())
            }
            Evidence::FormalSqlCountermodel { .. } => {
                panic!("expected schema mismatch evidence")
            }
        }
    }

    #[test]
    fn output_schema_mismatch_preflight_is_terminal_in_every_verification_mode() {
        let mismatch = SchemaMismatch::StatementOutput {
            reason: "source is numeric, target is int8".to_owned(),
            statement: 1,
            source: output_schema(1700, "numeric"),
            target: output_schema(20, "int8"),
        };
        let preflight = OutputSchemaPreflight {
            schema_name: "logos_preflight".to_owned(),
            result: OutputSchemaPreflightResult::Mismatch {
                mismatch: mismatch.clone(),
            },
        };

        for verification_mode in [
            VerificationMode::SafeUnconditional,
            VerificationMode::OutcomeUnconditional,
            VerificationMode::Conditional,
        ] {
            let (reason, evidence) =
                output_schema_preflight_evidence(&preflight, verification_mode)
                    .expect("mismatch preflight")
                    .expect("schema mismatch must be terminal in every verification mode");
            assert!(reason.contains("before agent execution"));
            match evidence {
                Evidence::OutputSchemaMismatch { mismatch: observed } => {
                    assert_eq!(observed.reason(), mismatch.reason())
                }
                Evidence::FormalSqlCountermodel { .. } => {
                    panic!("expected schema mismatch evidence in {verification_mode:?}")
                }
            }
        }
    }

    #[test]
    fn query_program_length_mismatch_is_terminal_before_llm_search() {
        let mismatch = SchemaMismatch::ProgramLength {
            reason: "query program length differs: source has 2 statements, target has 1"
                .to_owned(),
            source_statement_count: 2,
            target_statement_count: 1,
        };
        let preflight = OutputSchemaPreflight {
            schema_name: "logos_preflight".to_owned(),
            result: OutputSchemaPreflightResult::Mismatch {
                mismatch: mismatch.clone(),
            },
        };

        let (_, evidence) =
            output_schema_preflight_evidence(&preflight, VerificationMode::OutcomeUnconditional)
                .expect("program mismatch preflight")
                .expect("terminal evidence");
        match evidence {
            Evidence::OutputSchemaMismatch { mismatch: observed } => {
                assert_eq!(observed.reason(), mismatch.reason())
            }
            Evidence::FormalSqlCountermodel { .. } => {
                panic!("expected program schema mismatch evidence")
            }
        }
    }

    #[test]
    fn output_schema_preflight_errors_fail_closed() {
        let preflight = OutputSchemaPreflight {
            schema_name: "logos_preflight".to_owned(),
            result: OutputSchemaPreflightResult::ValidationError {
                message: "connection failed".to_owned(),
            },
        };

        let error =
            output_schema_preflight_evidence(&preflight, VerificationMode::OutcomeUnconditional)
                .expect_err("preflight errors must not fall through to the LLM");
        assert!(error.to_string().contains("connection failed"));
    }

    #[test]
    fn integrity_validation_error_cannot_become_a_reported_counterexample() {
        let message = "witness violates benchmark primary_key constraint on DEPT";
        let validation = WitnessCheck {
            schema_name: "logos_calcite_148".to_owned(),
            warnings: Vec::new(),
            result: CheckResult::ValidationError {
                message: message.to_owned(),
            },
        };

        assert_eq!(
            validation_outcome(&validation),
            ValidationOutcome::ValidationError
        );
        assert_eq!(failed_check_reason(&validation), message);
    }

    #[test]
    fn typed_witness_materialization_is_not_an_equivalence_verdict() {
        let validation = WitnessCheck {
            schema_name: "logos_typed_witness".to_owned(),
            warnings: Vec::new(),
            result: CheckResult::WitnessMaterialized {
                table_count: 2,
                row_count: 3,
            },
        };
        assert_eq!(
            validation_outcome(&validation),
            ValidationOutcome::WitnessMaterialized
        );
        assert_eq!(
            failed_check_reason(&validation),
            "candidate database was materialized successfully"
        );
    }

    #[test]
    fn legacy_inconclusive_observation_is_explicitly_nonauthoritative() {
        let validation = WitnessCheck {
            schema_name: "logos_possible_order".to_owned(),
            warnings: Vec::new(),
            result: CheckResult::InconclusiveObservation {
                statement: 1,
                comparison: crate::validation::ObservationComparison::Sequence,
                reason: "ORDER BY ties admit several legal lists".to_owned(),
                source_result: "source".to_owned(),
                target_result: "target".to_owned(),
            },
        };
        assert!(failed_check_reason(&validation).contains("not authoritative"));
    }

    #[test]
    fn legacy_executor_difference_cannot_become_solver_evidence() {
        let validation = WitnessCheck {
            schema_name: "logos_ordered_witness".to_owned(),
            warnings: Vec::new(),
            result: CheckResult::RowSequenceDifference {
                statement: 1,
                first_differing_row: 2,
                source_result: r#"{"rows":[["a"],["b"]]}"#.to_owned(),
                target_result: r#"{"rows":[["a"],["c"]]}"#.to_owned(),
                certificate: crate::validation::ObservationCertificateUse {
                    schema_version: 1,
                    verification_input_key: "test-input".to_owned(),
                    verification_input_sha256: "test-input-sha256".to_owned(),
                    lowering_sha256: "test-lowering".to_owned(),
                    statement: 1,
                    comparison: crate::validation::ObservationComparison::Sequence,
                    source_derivation: "test source sequence is functional".to_owned(),
                    target_derivation: "test target sequence is functional".to_owned(),
                },
            },
        };

        assert_eq!(
            validation_outcome(&validation),
            ValidationOutcome::RowSequenceDifference
        );
        assert!(failed_check_reason(&validation).contains("cannot decide EQ/NEQ"));
    }

    #[test]
    fn assessment_cache_identity_is_path_independent_and_semantic() {
        let first_input_root = TestDirectory::new("cache-first-input");
        let second_input_root = TestDirectory::new("cache-second-input");
        let changed_input_root = TestDirectory::new("cache-changed-input");
        let first_input = verification_input(first_input_root.path(), "SELECT x FROM t;\n");
        let second_input = verification_input(second_input_root.path(), "SELECT x FROM t;\n");
        let changed_input = verification_input(
            changed_input_root.path(),
            "SELECT x + INTERVAL '1 hour' FROM t;\n",
        );

        let first_candidate = first_input_root.path().join("rounds/02/candidate.json");
        let second_candidate = second_input_root.path().join("rounds/02/candidate.json");
        let (first_prompt, first_identity) =
            prompt_and_identity(&first_input, "UTC", &first_candidate);
        let (second_prompt, second_identity) =
            prompt_and_identity(&second_input, "UTC", &second_candidate);
        let cached = assessment(first_identity.clone(), first_prompt.clone());

        assert_ne!(first_prompt, second_prompt);
        assert!(first_prompt.contains(&first_candidate.display().to_string()));
        assert!(second_prompt.contains(&second_candidate.display().to_string()));
        assert_eq!(first_identity, second_identity);
        assert!(
            first_identity
                .semantic_prompt
                .contains("{{LOGOS_CURRENT_CANDIDATE_JSON_PATH}}")
        );
        assert!(
            !first_identity
                .semantic_prompt
                .contains(&first_candidate.display().to_string())
        );
        assert!(
            !first_identity
                .semantic_prompt
                .contains(&second_candidate.display().to_string())
        );
        assert_eq!(assessment_identity_error(&cached, &second_identity), None);

        let (_, mut changed_sql_identity) =
            prompt_and_identity(&changed_input, "UTC", &second_candidate);
        changed_sql_identity.task_key = first_identity.task_key.clone();
        assert!(assessment_identity_error(&cached, &changed_sql_identity).is_some());

        let (changed_zone_prompt, changed_zone_identity) =
            prompt_and_identity(&second_input, "Asia/Shanghai", &second_candidate);
        assert!(changed_zone_prompt.contains("SET TIME ZONE 'Asia/Shanghai';"));
        assert!(assessment_identity_error(&cached, &changed_zone_identity).is_some());

        let mut changed_input_identity = second_identity;
        changed_input_identity.task_key.push_str("-different-input");
        assert!(assessment_identity_error(&cached, &changed_input_identity).is_some());
    }

    #[test]
    fn assessment_cache_identity_rejects_stale_version_and_round() {
        let identity = AssessmentIdentity {
            task_key: "task".to_owned(),
            round: 2,
            semantic_prompt: "semantic prompt".to_owned(),
        };
        let mut stale = assessment(identity.clone(), "runtime prompt".to_owned());
        stale.cache_version += 1;
        assert!(assessment_identity_error(&stale, &identity).is_some());

        let mut stale = assessment(identity.clone(), "runtime prompt".to_owned());
        stale.request_identity.round += 1;
        assert!(assessment_identity_error(&stale, &identity).is_some());
    }

    #[test]
    fn assessment_cache_wire_format_rejects_unknown_fields() {
        let identity = AssessmentIdentity {
            task_key: "task".to_owned(),
            round: 2,
            semantic_prompt: "semantic prompt".to_owned(),
        };
        let encoded = serde_json::to_value(assessment(identity, "runtime prompt".to_owned()))
            .expect("serialize assessment");

        let mut unknown_assessment = encoded.clone();
        unknown_assessment
            .as_object_mut()
            .expect("assessment object")
            .insert("obsoletePromptHash".to_owned(), serde_json::json!("stale"));
        assert!(serde_json::from_value::<LlmAssessment>(unknown_assessment).is_err());

        let mut unknown_identity = encoded;
        unknown_identity
            .get_mut("requestIdentity")
            .and_then(serde_json::Value::as_object_mut)
            .expect("request identity object")
            .insert("outputPath".to_owned(), serde_json::json!("/old/run"));
        assert!(serde_json::from_value::<LlmAssessment>(unknown_identity).is_err());
    }

    #[test]
    fn cached_assessment_rehydrates_current_prompt_and_candidate_path() {
        let old_root = TestDirectory::new("cache-old-run");
        let current_root = TestDirectory::new("cache-current-run");
        let input = verification_input(old_root.path(), "SELECT x FROM t;\n");
        let old_candidate = old_root.path().join("rounds/02/candidate.json");
        let current_candidate = current_root.path().join("rounds/02/candidate.json");
        let (old_prompt, identity) = prompt_and_identity(&input, "UTC", &old_candidate);
        let (current_prompt, current_identity) =
            prompt_and_identity(&input, "UTC", &current_candidate);
        assert_eq!(identity, current_identity);

        let cache_path = old_root.path().join("assessment-cache.json");
        write_assessment_cache(
            &cache_path,
            &assessment(identity.clone(), old_prompt.clone()),
        )
        .expect("write cache");
        let artifacts = ArtifactWriter::new(Some(current_root.path().to_owned()))
            .expect("create artifact writer");
        let context = AssessmentLogContext::new(
            2,
            "rounds/02/prompt.md",
            "rounds/02/candidate.json",
            cache_path,
        );

        let loaded = load_cached_assessment(&context, &identity, &current_prompt, &artifacts)
            .expect("reuse path-independent assessment");

        assert_eq!(loaded.assessment.prompt, current_prompt);
        assert_ne!(loaded.assessment.prompt, old_prompt);
        assert!(
            loaded
                .assessment
                .prompt
                .contains(&current_candidate.display().to_string())
        );
        assert!(
            !loaded
                .assessment
                .prompt
                .contains(&old_candidate.display().to_string())
        );
        let candidate_text =
            std::fs::read_to_string(&current_candidate).expect("read rehydrated candidate");
        let candidate: Candidate =
            serde_json::from_str(&candidate_text).expect("parse rehydrated candidate");
        assert_eq!(candidate.decision, Decision::NoCandidate);
    }
}
