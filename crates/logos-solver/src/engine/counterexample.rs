use std::path::{Path, PathBuf};
use std::time::Instant;

mod reporting;

use serde::{Deserialize, Serialize};

use crate::artifacts::ArtifactWriter;
use crate::core::VerificationInput;
use crate::engine::config::Config;
use crate::engine::now_ms_since_epoch;
use crate::engine::report::{
    Evidence, LlmAssessmentCacheLog, LlmAssessmentCacheStatus, LlmAssessmentLog, LlmParseLog,
    LlmProviderLog, RoundOutcome, SearchStatus, SolverOutcome, ValidationLog, ValidationOutcome,
};
use crate::error::{Error, Result};
use crate::proposal::{
    Attempt, Candidate, Decision, Provider, build_counterexample_prompt, parse_proposal,
};
use crate::validation::{CheckResult, PostgresValidator, WitnessCheck};

pub(super) use reporting::CounterexampleStageResult;
use reporting::{RecordedRound, SearchRun};

const ASSESSMENT_CACHE_VERSION: u32 = 1;

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
struct LlmAssessment {
    cache_version: u32,
    task_key: String,
    round: usize,
    prompt: String,
    raw_output: String,
    proposal: Candidate,
}

#[derive(Debug, Clone)]
struct AssessmentLoad {
    assessment: LlmAssessment,
    log: LlmAssessmentLog,
}

#[derive(Debug)]
struct AssessmentLoadFailure {
    log: LlmAssessmentLog,
    error: Error,
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
struct AssessmentLogDraft<'a> {
    context: &'a AssessmentLogContext,
    cache: AssessmentCacheUse,
    stats: AssessmentLogStats,
    provider: Option<LlmProviderLog>,
}

pub(super) fn run_counterexample_search(
    input: &VerificationInput,
    options: &Config,
    provider: &dyn Provider,
    artifacts: &ArtifactWriter,
    started: Instant,
) -> Result<CounterexampleStageResult> {
    let max_rounds = if options.llm_assessment_only {
        1
    } else {
        options.max_counterexample_rounds.max(1)
    };
    let input_key = input.stable_cache_key();
    let mut run = SearchRun::new(artifacts, started);

    for round in 1..=max_rounds {
        let candidate_path = format!("rounds/{round:02}/candidate.json");
        let candidate_abs_path = artifacts.root().join(&candidate_path);
        let prompt = build_counterexample_prompt(
            input,
            round,
            max_rounds,
            &run.feedback,
            &candidate_abs_path,
        );
        let prompt_path = format!("rounds/{round:02}/prompt.md");
        artifacts.write_text(&prompt_path, &prompt)?;

        let assessment_load = match load_or_generate_assessment(
            &input_key,
            round,
            prompt,
            &prompt_path,
            &candidate_path,
            &candidate_abs_path,
            provider,
            options,
            artifacts,
        ) {
            Ok(load) => load,
            Err(failure) => {
                let error = failure.error;
                run.record_assessment_failure(round, failure.log, &error)?;
                return Err(error);
            }
        };
        let assessment = assessment_load.assessment;
        let assessment_log = assessment_load.log;
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
                        "counterexample search produced no candidate: {reason}; entering equivalence verification stage"
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
                return run.finish_terminal(
                    SolverOutcome::NeedsManualReview,
                    SearchStatus::NeedsManualReview,
                    reason,
                    None,
                );
            }
            Decision::CounterexampleCandidate => {
                artifacts.write_text(
                    format!("rounds/{round:02}/witness.sql"),
                    &proposal.witness_sql,
                )?;
                let validator = PostgresValidator::new(
                    options.postgres_url.clone(),
                    options.statement_timeout_ms,
                    options.diff_sample_limit,
                    options.sql_time_zone.clone(),
                )?;
                let validation_started_ms = now_ms_since_epoch();
                let validation_started = Instant::now();
                let validation = validator.validate(input, &proposal.witness_sql);
                let validation_log = ValidationLog {
                    started_ms_since_epoch: validation_started_ms,
                    elapsed_ms: validation_started.elapsed().as_millis(),
                    result: validation_outcome(&validation),
                    warnings: validation.warnings.clone(),
                };
                artifacts.write_json(format!("rounds/{round:02}/validation.json"), &validation)?;

                if let Some((reason, counterexample)) =
                    validated_counterexample(&proposal.witness_sql, &validation)
                {
                    run.record_round(RecordedRound::with_validation(
                        round,
                        assessment_log,
                        proposal,
                        validation,
                        validation_log,
                        RoundOutcome::CounterexampleValidated,
                        None,
                    ))?;
                    return run.finish_terminal(
                        SolverOutcome::NotEquivalent,
                        SearchStatus::NotEquivalent,
                        reason,
                        Some(counterexample),
                    );
                }

                let reason = failed_check_reason(&validation);
                run.feedback.push(format!(
                    "Round {round} failed deterministic validation: {reason}"
                ));
                run.record_round(RecordedRound::with_validation(
                    round,
                    assessment_log,
                    proposal,
                    validation,
                    validation_log,
                    RoundOutcome::CandidateRejected,
                    Some(reason),
                ))?;
            }
        }
    }

    if options.llm_assessment_only {
        return run.finish_terminal(
            SolverOutcome::LlmAssessmentOnly,
            SearchStatus::LlmAssessmentOnly,
            "LLM assessment produced a candidate, but deterministic validation did not confirm it"
                .to_owned(),
            None,
        );
    }

    run.finish_without_counterexample(
        SearchStatus::MaybeEquivalent,
        "no validated counterexample within round budget; entering equivalence verification stage"
            .to_owned(),
    )
}

fn load_or_generate_assessment(
    task_key: &str,
    round: usize,
    prompt: String,
    prompt_path: &str,
    candidate_path: &str,
    candidate_abs_path: &Path,
    provider: &dyn Provider,
    options: &Config,
    artifacts: &ArtifactWriter,
) -> std::result::Result<AssessmentLoad, AssessmentLoadFailure> {
    let cache_path = assessment_cache_path(options, task_key, round);
    let log_context =
        AssessmentLogContext::new(round, prompt_path, candidate_path, cache_path.clone());
    let should_reuse = options.reuse_llm_assessment && !options.force_llm_assessment;

    // Debug runs can reuse a prior assessment, but the round artifacts still
    // get rehydrated so later validation/reporting sees the same file layout.
    if should_reuse && cache_path.exists() {
        return load_cached_assessment(&log_context, prompt.len(), artifacts);
    }

    generate_assessment(
        task_key,
        round,
        prompt,
        candidate_abs_path,
        provider,
        artifacts,
        &log_context,
    )
}

fn load_cached_assessment(
    context: &AssessmentLogContext,
    prompt_bytes: usize,
    artifacts: &ArtifactWriter,
) -> std::result::Result<AssessmentLoad, AssessmentLoadFailure> {
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
    let assessment: LlmAssessment = serde_json::from_str(&text).map_err(|source| {
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
    })
}

fn generate_assessment(
    task_key: &str,
    round: usize,
    prompt: String,
    candidate_abs_path: &Path,
    provider: &dyn Provider,
    artifacts: &ArtifactWriter,
    context: &AssessmentLogContext,
) -> std::result::Result<AssessmentLoad, AssessmentLoadFailure> {
    let mut log = AssessmentLogDraft::not_written(context, prompt.len());

    // The provider is required to write the machine-readable candidate here.
    // Removing stale content prevents accidentally validating an older round.
    if let Err(source) = std::fs::remove_file(candidate_abs_path) {
        if source.kind() != std::io::ErrorKind::NotFound {
            let error = Error::ProposalCommand(format!(
                "failed to remove stale proposal file {}: {source}",
                candidate_abs_path.display()
            ));
            return Err(log.fail_now(error));
        }
    }

    let provider_started_ms = now_ms_since_epoch();
    let provider_started = Instant::now();
    let completion = match provider.complete(&prompt, candidate_abs_path) {
        Ok(completion) => completion,
        Err(error) => {
            log.record_provider(build_provider_log(
                provider,
                round,
                provider_started_ms,
                provider_started.elapsed().as_millis(),
                false,
                None,
                0,
                0,
            ));
            return Err(log.fail_now(error));
        }
    };
    let provider_elapsed_ms = provider_started.elapsed().as_millis();
    log.record_raw_output(completion.stdout.len());

    // stdout/stderr are retained for audit only; the candidate JSON is read
    // from candidate_abs_path to avoid parsing mixed prose/log output.
    log.write_provider_stderr(artifacts, &completion.stderr)?;
    log.write_raw_output(artifacts, &completion.stdout)?;

    log.record_provider(build_provider_log(
        provider,
        round,
        provider_started_ms,
        provider_elapsed_ms,
        completion.success,
        completion.exit_code,
        completion.stdout.len(),
        completion.stderr.len(),
    ));
    if !completion.success {
        return Err(log.fail_now(Error::ProposalCommand(completion.stderr.trim().to_owned())));
    }

    let parse_started = Instant::now();
    let candidate_text = match std::fs::read_to_string(candidate_abs_path) {
        Ok(text) => text,
        Err(source) => {
            let error = Error::Read {
                path: candidate_abs_path.to_owned(),
                source,
            };
            return Err(log.fail_with_elapsed(error, parse_started.elapsed().as_millis()));
        }
    };
    let proposal = parse_proposal(&candidate_text)
        .map_err(|error| log.fail_with_elapsed(error, parse_started.elapsed().as_millis()))?;
    let parse_log = LlmParseLog::succeeded(parse_started.elapsed().as_millis());

    // Normalize the provider's JSON before downstream code and reports read it.
    log.write_candidate(artifacts, &proposal, &parse_log)?;

    let assessment = LlmAssessment {
        cache_version: ASSESSMENT_CACHE_VERSION,
        task_key: task_key.to_owned(),
        round,
        prompt,
        raw_output: completion.stdout,
        proposal,
    };
    log.record_stats(AssessmentLogStats::from_assessment(&assessment));

    // Cache stores the full prompt/output/proposal bundle; run artifacts keep
    // a source marker so cache hits and fresh generations are distinguishable.
    log.write_assessment_cache(&assessment, &parse_log)?;
    log.write_assessment_source(artifacts, "generated", &parse_log)?;

    Ok(AssessmentLoad {
        assessment,
        log: log.finish(parse_log),
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
            log: self.log(cache, stats, provider, parse),
            error,
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

fn build_provider_log(
    provider: &dyn Provider,
    round: usize,
    started_ms_since_epoch: u128,
    elapsed_ms: u128,
    success: bool,
    exit_code: Option<i32>,
    stdout_bytes: usize,
    stderr_bytes: usize,
) -> LlmProviderLog {
    LlmProviderLog {
        command: provider.command_summary().map(ToOwned::to_owned),
        started_ms_since_epoch,
        elapsed_ms,
        success,
        exit_code,
        stdout_bytes,
        stderr_bytes,
        stderr_path: format!("rounds/{round:02}/llm-provider.stderr.txt"),
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
        CheckResult::DataDifference { .. } => ValidationOutcome::DataDifference,
        CheckResult::OutputSchemaMismatch { .. } => ValidationOutcome::OutputSchemaMismatch,
        CheckResult::NoDifference => ValidationOutcome::NoDifference,
        CheckResult::ValidationError { .. } => ValidationOutcome::ValidationError,
    }
}

fn validated_counterexample(
    witness_sql: &str,
    validation: &WitnessCheck,
) -> Option<(String, Evidence)> {
    match &validation.result {
        CheckResult::DataDifference {
            source_result,
            target_result,
            diff_sample,
        } => Some((
            "validated PostgreSQL counterexample witness".to_owned(),
            Evidence::DataDifference {
                witness_sql: witness_sql.to_owned(),
                source_result: source_result.clone(),
                target_result: target_result.clone(),
                diff_sample: diff_sample.clone(),
            },
        )),
        CheckResult::OutputSchemaMismatch { mismatch } => Some((
            "validated PostgreSQL output schema mismatch".to_owned(),
            Evidence::OutputSchemaMismatch {
                witness_sql: witness_sql.to_owned(),
                mismatch: mismatch.clone(),
            },
        )),
        CheckResult::NoDifference | CheckResult::ValidationError { .. } => None,
    }
}

fn failed_check_reason(validation: &WitnessCheck) -> String {
    match &validation.result {
        CheckResult::ValidationError { message } => message.clone(),
        CheckResult::NoDifference => "candidate did not make query results differ".to_owned(),
        CheckResult::DataDifference { .. } | CheckResult::OutputSchemaMismatch { .. } => {
            "candidate was already validated".to_owned()
        }
    }
}
