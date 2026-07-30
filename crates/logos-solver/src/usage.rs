use serde::{Deserialize, Serialize};
use serde_json::Value;
use thiserror::Error;

pub const EXPERIMENT_MODEL: &str = "gpt-5.6-sol";
pub const INPUT_USD_PER_MILLION_TOKENS: f64 = 5.0;
pub const CACHED_INPUT_USD_PER_MILLION_TOKENS: f64 = 0.5;
pub const OUTPUT_USD_PER_MILLION_TOKENS: f64 = 30.0;

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct LlmUsage {
    pub model: String,
    pub input_tokens: u64,
    pub cached_input_tokens: u64,
    pub output_tokens: u64,
    pub total_tokens: u64,
    pub estimated_cost_usd: f64,
}

impl LlmUsage {
    pub fn zero() -> Self {
        Self::from_counts(0, 0, 0).expect("zero token usage is valid")
    }

    pub fn from_counts(
        input_tokens: u64,
        cached_input_tokens: u64,
        output_tokens: u64,
    ) -> Result<Self, UsageError> {
        if cached_input_tokens > input_tokens {
            return Err(UsageError::CachedExceedsInput {
                cached: cached_input_tokens,
                input: input_tokens,
            });
        }
        let total_tokens = input_tokens
            .checked_add(output_tokens)
            .ok_or(UsageError::TokenOverflow)?;
        let estimated_cost_usd = ((input_tokens - cached_input_tokens) as f64
            * INPUT_USD_PER_MILLION_TOKENS
            + cached_input_tokens as f64 * CACHED_INPUT_USD_PER_MILLION_TOKENS
            + output_tokens as f64 * OUTPUT_USD_PER_MILLION_TOKENS)
            / 1_000_000.0;
        Ok(Self {
            model: EXPERIMENT_MODEL.to_owned(),
            input_tokens,
            cached_input_tokens,
            output_tokens,
            total_tokens,
            estimated_cost_usd,
        })
    }

    pub fn checked_sum<'a>(values: impl IntoIterator<Item = &'a Self>) -> Result<Self, UsageError> {
        let mut input_tokens = 0_u64;
        let mut cached_input_tokens = 0_u64;
        let mut output_tokens = 0_u64;
        for value in values {
            if value.model != EXPERIMENT_MODEL {
                return Err(UsageError::UnexpectedModel(value.model.clone()));
            }
            input_tokens = input_tokens
                .checked_add(value.input_tokens)
                .ok_or(UsageError::TokenOverflow)?;
            cached_input_tokens = cached_input_tokens
                .checked_add(value.cached_input_tokens)
                .ok_or(UsageError::TokenOverflow)?;
            output_tokens = output_tokens
                .checked_add(value.output_tokens)
                .ok_or(UsageError::TokenOverflow)?;
        }
        Self::from_counts(input_tokens, cached_input_tokens, output_tokens)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct CodexInvocationUsage {
    pub session_id: String,
    pub usage: LlmUsage,
}

impl CodexInvocationUsage {
    /// Convert Codex's cumulative thread total into usage attributable to this
    /// invocation.
    ///
    /// `codex exec --json` emits the latest thread-wide cumulative total in a
    /// `turn.completed` event.  The first invocation therefore owns the whole
    /// value, while a resumed invocation owns the monotonic delta from the
    /// preceding completion in the same session.
    pub fn incremental_usage(&self, previous: Option<&Self>) -> Result<LlmUsage, UsageError> {
        if self.usage.model != EXPERIMENT_MODEL {
            return Err(UsageError::UnexpectedModel(self.usage.model.clone()));
        }
        let Some(previous) = previous else {
            return Ok(self.usage.clone());
        };
        if self.session_id != previous.session_id {
            return Err(UsageError::SessionChanged {
                expected: previous.session_id.clone(),
                observed: self.session_id.clone(),
            });
        }
        if previous.usage.model != EXPERIMENT_MODEL {
            return Err(UsageError::UnexpectedModel(previous.usage.model.clone()));
        }
        let delta = |field: &'static str, current: u64, prior: u64| {
            current
                .checked_sub(prior)
                .ok_or(UsageError::CumulativeRegression {
                    field,
                    previous: prior,
                    current,
                })
        };
        LlmUsage::from_counts(
            delta(
                "input_tokens",
                self.usage.input_tokens,
                previous.usage.input_tokens,
            )?,
            delta(
                "cached_input_tokens",
                self.usage.cached_input_tokens,
                previous.usage.cached_input_tokens,
            )?,
            delta(
                "output_tokens",
                self.usage.output_tokens,
                previous.usage.output_tokens,
            )?,
        )
    }
}

#[derive(Debug, Error, Clone, PartialEq, Eq)]
pub enum UsageError {
    #[error("Codex JSON event line {line} is malformed: {message}")]
    MalformedEvent { line: usize, message: String },
    #[error("Codex JSON event line {line} is not an object")]
    NonObjectEvent { line: usize },
    #[error("Codex invocation did not emit exactly one thread.started event")]
    MissingThread,
    #[error("Codex invocation emitted multiple thread.started events")]
    DuplicateThread,
    #[error("Codex thread.started event has no valid thread_id")]
    InvalidThread,
    #[error("Codex invocation did not emit authoritative turn.completed usage")]
    MissingCompletedUsage,
    #[error("Codex invocation emitted multiple turn.completed usage records")]
    DuplicateCompletedUsage,
    #[error("Codex turn.completed usage field {0} is missing or not a nonnegative integer")]
    InvalidCount(&'static str),
    #[error("cached input tokens {cached} exceed input tokens {input}")]
    CachedExceedsInput { cached: u64, input: u64 },
    #[error("token total overflow")]
    TokenOverflow,
    #[error("usage uses unexpected model {0}")]
    UnexpectedModel(String),
    #[error("resumed Codex invocation changed session from {expected} to {observed}")]
    SessionChanged { expected: String, observed: String },
    #[error("Codex cumulative usage field {field} regressed from {previous} to {current}")]
    CumulativeRegression {
        field: &'static str,
        previous: u64,
        current: u64,
    },
}

/// Recover the Codex thread identifier independently of terminal usage.
///
/// A host timeout can stop an otherwise resumable turn before Codex emits
/// `turn.completed`.  The initial `thread.started` event is still authoritative
/// for resuming that thread and must not be discarded with the missing usage
/// record.
pub fn parse_codex_thread_id(events: &str) -> Result<String, UsageError> {
    let mut session_id: Option<String> = None;
    for (index, line) in events.lines().enumerate() {
        if line.trim().is_empty() {
            continue;
        }
        let line_number = index + 1;
        let value: Value =
            serde_json::from_str(line).map_err(|source| UsageError::MalformedEvent {
                line: line_number,
                message: source.to_string(),
            })?;
        let object = value
            .as_object()
            .ok_or(UsageError::NonObjectEvent { line: line_number })?;
        if object.get("type").and_then(Value::as_str) != Some("thread.started") {
            continue;
        }
        if session_id.is_some() {
            return Err(UsageError::DuplicateThread);
        }
        let value = object
            .get("thread_id")
            .and_then(Value::as_str)
            .filter(|value| !value.trim().is_empty())
            .ok_or(UsageError::InvalidThread)?;
        session_id = Some(value.to_owned());
    }
    session_id.ok_or(UsageError::MissingThread)
}

/// Parse one `codex exec --json` invocation.
///
/// `turn.completed.usage` is an authoritative provider record, but Codex emits
/// the thread-wide cumulative total there.  Callers must use
/// [`CodexInvocationUsage::incremental_usage`] before summing resumed rounds.
pub fn parse_codex_jsonl(events: &str) -> Result<CodexInvocationUsage, UsageError> {
    let mut session_id: Option<String> = None;
    let mut usage: Option<LlmUsage> = None;
    for (index, line) in events.lines().enumerate() {
        if line.trim().is_empty() {
            continue;
        }
        let line_number = index + 1;
        let value: Value =
            serde_json::from_str(line).map_err(|source| UsageError::MalformedEvent {
                line: line_number,
                message: source.to_string(),
            })?;
        let object = value
            .as_object()
            .ok_or(UsageError::NonObjectEvent { line: line_number })?;
        match object.get("type").and_then(Value::as_str) {
            Some("thread.started") => {
                if session_id.is_some() {
                    return Err(UsageError::DuplicateThread);
                }
                let value = object
                    .get("thread_id")
                    .and_then(Value::as_str)
                    .filter(|value| !value.trim().is_empty())
                    .ok_or(UsageError::InvalidThread)?;
                session_id = Some(value.to_owned());
            }
            Some("turn.completed") => {
                if usage.is_some() {
                    return Err(UsageError::DuplicateCompletedUsage);
                }
                let counts = object
                    .get("usage")
                    .and_then(Value::as_object)
                    .ok_or(UsageError::MissingCompletedUsage)?;
                let count = |name: &'static str| {
                    counts
                        .get(name)
                        .and_then(Value::as_u64)
                        .ok_or(UsageError::InvalidCount(name))
                };
                usage = Some(LlmUsage::from_counts(
                    count("input_tokens")?,
                    count("cached_input_tokens")?,
                    count("output_tokens")?,
                )?);
            }
            _ => {}
        }
    }
    Ok(CodexInvocationUsage {
        session_id: session_id.ok_or(UsageError::MissingThread)?,
        usage: usage.ok_or(UsageError::MissingCompletedUsage)?,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn valid_events() -> &'static str {
        concat!(
            "{\"type\":\"thread.started\",\"thread_id\":\"0199a213-81c0-7800-8aa1-bbab2a035a53\"}\n",
            "{\"type\":\"turn.started\"}\n",
            "{\"type\":\"item.completed\",\"item\":{\"type\":\"agent_message\"}}\n",
            "{\"type\":\"turn.completed\",\"usage\":{\"input_tokens\":24763,\"cached_input_tokens\":24448,\"output_tokens\":122,\"reasoning_output_tokens\":10}}\n",
        )
    }

    #[test]
    fn parses_authoritative_codex_usage_and_prices_uncached_cached_and_output() {
        let parsed = parse_codex_jsonl(valid_events()).expect("valid Codex JSON events");
        assert_eq!(parsed.session_id, "0199a213-81c0-7800-8aa1-bbab2a035a53");
        assert_eq!(parsed.usage.input_tokens, 24_763);
        assert_eq!(parsed.usage.cached_input_tokens, 24_448);
        assert_eq!(parsed.usage.output_tokens, 122);
        assert_eq!(parsed.usage.total_tokens, 24_885);
        let expected = (315.0 * 5.0 + 24_448.0 * 0.5 + 122.0 * 30.0) / 1_000_000.0;
        assert!((parsed.usage.estimated_cost_usd - expected).abs() < 1e-12);
    }

    #[test]
    fn missing_malformed_and_inconsistent_usage_fail_closed() {
        for (events, expected) in [
            (
                "{\"type\":\"thread.started\",\"thread_id\":\"x\"}\n",
                UsageError::MissingCompletedUsage,
            ),
            (
                "{not json}\n",
                UsageError::MalformedEvent {
                    line: 1,
                    message: "key must be a string at line 1 column 2".to_owned(),
                },
            ),
            (
                concat!(
                    "{\"type\":\"thread.started\",\"thread_id\":\"x\"}\n",
                    "{\"type\":\"turn.completed\",\"usage\":{\"input_tokens\":1,\"cached_input_tokens\":2,\"output_tokens\":3}}\n"
                ),
                UsageError::CachedExceedsInput {
                    cached: 2,
                    input: 1,
                },
            ),
        ] {
            assert_eq!(parse_codex_jsonl(events).unwrap_err(), expected);
        }
    }

    #[test]
    fn recovers_thread_id_before_a_turn_has_completed() {
        let events = concat!(
            "{\"type\":\"thread.started\",\"thread_id\":\"0199a213-81c0-7800-8aa1-bbab2a035a53\"}\n",
            "{\"type\":\"turn.started\"}\n",
            "{\"type\":\"item.completed\",\"item\":{\"type\":\"agent_message\"}}\n",
        );
        assert_eq!(
            parse_codex_thread_id(events).unwrap(),
            "0199a213-81c0-7800-8aa1-bbab2a035a53"
        );
        assert_eq!(
            parse_codex_jsonl(events).unwrap_err(),
            UsageError::MissingCompletedUsage
        );
    }

    #[test]
    fn cumulative_resumed_rounds_are_counted_once_by_monotonic_delta() {
        let first = CodexInvocationUsage {
            session_id: "0199a213-81c0-7800-8aa1-bbab2a035a53".to_owned(),
            usage: LlmUsage::from_counts(100, 80, 20).unwrap(),
        };
        let resumed = CodexInvocationUsage {
            session_id: first.session_id.clone(),
            usage: LlmUsage::from_counts(220, 180, 50).unwrap(),
        };
        let first_increment = first.incremental_usage(None).unwrap();
        let resumed_increment = resumed.incremental_usage(Some(&first)).unwrap();
        assert_eq!(
            (
                resumed_increment.input_tokens,
                resumed_increment.cached_input_tokens,
                resumed_increment.output_tokens,
            ),
            (120, 100, 30)
        );
        let total = LlmUsage::checked_sum([&first_increment, &resumed_increment]).unwrap();
        assert_eq!(total, resumed.usage);
    }

    #[test]
    fn cumulative_resume_rejects_session_changes_and_counter_regressions() {
        let previous = CodexInvocationUsage {
            session_id: "0199a213-81c0-7800-8aa1-bbab2a035a53".to_owned(),
            usage: LlmUsage::from_counts(100, 80, 20).unwrap(),
        };
        let changed_session = CodexInvocationUsage {
            session_id: "0299a213-81c0-7800-8aa1-bbab2a035a53".to_owned(),
            usage: LlmUsage::from_counts(120, 90, 30).unwrap(),
        };
        assert_eq!(
            changed_session
                .incremental_usage(Some(&previous))
                .unwrap_err(),
            UsageError::SessionChanged {
                expected: previous.session_id.clone(),
                observed: changed_session.session_id.clone(),
            }
        );

        for (usage, field, prior, current) in [
            (
                LlmUsage::from_counts(99, 80, 30).unwrap(),
                "input_tokens",
                100,
                99,
            ),
            (
                LlmUsage::from_counts(110, 79, 30).unwrap(),
                "cached_input_tokens",
                80,
                79,
            ),
            (
                LlmUsage::from_counts(110, 90, 19).unwrap(),
                "output_tokens",
                20,
                19,
            ),
        ] {
            let resumed = CodexInvocationUsage {
                session_id: previous.session_id.clone(),
                usage,
            };
            assert_eq!(
                resumed.incremental_usage(Some(&previous)).unwrap_err(),
                UsageError::CumulativeRegression {
                    field,
                    previous: prior,
                    current,
                }
            );
        }

        let impossible_increment = CodexInvocationUsage {
            session_id: previous.session_id.clone(),
            // Both cumulative snapshots are individually valid, but the
            // resumed turn cannot add 15 cached tokens within 10 input tokens.
            usage: LlmUsage::from_counts(110, 95, 30).unwrap(),
        };
        assert_eq!(
            impossible_increment
                .incremental_usage(Some(&previous))
                .unwrap_err(),
            UsageError::CachedExceedsInput {
                cached: 15,
                input: 10,
            }
        );
    }

    #[test]
    fn cumulative_reconciliation_rejects_unexpected_models() {
        let mut current = CodexInvocationUsage {
            session_id: "0199a213-81c0-7800-8aa1-bbab2a035a53".to_owned(),
            usage: LlmUsage::from_counts(100, 80, 20).unwrap(),
        };
        current.usage.model = "unexpected-model".to_owned();
        assert_eq!(
            current.incremental_usage(None).unwrap_err(),
            UsageError::UnexpectedModel("unexpected-model".to_owned())
        );

        let current = CodexInvocationUsage {
            session_id: current.session_id.clone(),
            usage: LlmUsage::from_counts(120, 90, 30).unwrap(),
        };
        let mut previous = current.clone();
        previous.usage.model = "previous-model".to_owned();
        assert_eq!(
            current.incremental_usage(Some(&previous)).unwrap_err(),
            UsageError::UnexpectedModel("previous-model".to_owned())
        );
    }
}
