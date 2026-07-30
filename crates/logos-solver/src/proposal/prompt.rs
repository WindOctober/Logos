use crate::core::{ObservationCertificateReport, SqlTimeZone, VerificationInput};
use crate::error::{Error, Result};

const COUNTEREXAMPLE_PROMPT: &str = include_str!("../../prompts/counterexample.md");
const SHARED_SEMANTIC_PRIMER: &str = include_str!("../../prompts/semantic-primer.md");
const ASSESSMENT_IDENTITY_OUTPUT_PATH: &str = "{{LOGOS_CURRENT_CANDIDATE_JSON_PATH}}";
const REQUIRED_PLACEHOLDERS: [(&str, u16); 9] = [
    ("SCHEMA_SQL", 1 << 0),
    ("SOURCE_SQL", 1 << 1),
    ("TARGET_SQL", 1 << 2),
    ("ROUND", 1 << 3),
    ("MAX_ROUNDS", 1 << 4),
    ("OUTPUT_JSON_PATH", 1 << 5),
    ("FEEDBACK", 1 << 6),
    ("INTEGRITY_CONTRACT", 1 << 7),
    ("SEMANTIC_ROUND_BUDGET", 1 << 8),
];
const ALL_REQUIRED_PLACEHOLDERS: u16 = (1 << REQUIRED_PLACEHOLDERS.len()) - 1;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CounterexamplePrompt {
    runtime: String,
    semantic_identity: String,
}

impl CounterexamplePrompt {
    pub fn semantic_identity(&self) -> &str {
        &self.semantic_identity
    }

    pub fn into_runtime(self) -> String {
        self.runtime
    }
}

struct PromptValues<'a> {
    schema_sql: &'a str,
    source_sql: &'a str,
    target_sql: &'a str,
    round: &'a str,
    max_rounds: &'a str,
    semantic_round_budget: &'a str,
    feedback: &'a str,
    integrity_contract: &'a str,
}

fn invalid_prompt_template(reason: impl std::fmt::Display) -> Error {
    Error::ProposalCommand(format!(
        "invalid embedded counterexample prompt template: {reason}"
    ))
}

/// Render both prompt forms while scanning only the embedded template. Values
/// are appended opaquely, so SQL comments/literals and checker feedback cannot
/// accidentally become a second template language.
fn render_prompt_pair(
    template: &str,
    values: &PromptValues<'_>,
    runtime_output_path: &str,
    identity_output_path: &str,
) -> Result<(String, String)> {
    let mut runtime = String::with_capacity(template.len());
    let mut semantic_identity = String::with_capacity(template.len());
    let mut cursor = 0;
    let mut seen = 0_u16;

    while cursor < template.len() {
        let remaining = &template[cursor..];
        let next_open = remaining.find("{{");
        let next_close = remaining.find("}}");
        let Some(open_offset) = next_open else {
            if next_close.is_some() {
                return Err(invalid_prompt_template("unmatched closing delimiter `}}`"));
            }
            runtime.push_str(remaining);
            semantic_identity.push_str(remaining);
            cursor = template.len();
            continue;
        };
        if next_close.is_some_and(|close_offset| close_offset < open_offset) {
            return Err(invalid_prompt_template("unmatched closing delimiter `}}`"));
        }

        let literal = &remaining[..open_offset];
        runtime.push_str(literal);
        semantic_identity.push_str(literal);

        let placeholder_start = cursor + open_offset + 2;
        let after_open = &template[placeholder_start..];
        let Some(close_offset) = after_open.find("}}") else {
            return Err(invalid_prompt_template(
                "unclosed placeholder delimiter `{{`",
            ));
        };
        let name = &after_open[..close_offset];
        if name.is_empty()
            || !name
                .bytes()
                .all(|byte| byte.is_ascii_uppercase() || byte == b'_')
        {
            return Err(invalid_prompt_template(format_args!(
                "malformed placeholder `{{{{{name}}}}}`"
            )));
        }

        let (bit, runtime_value, identity_value) = match name {
            "SCHEMA_SQL" => (1 << 0, values.schema_sql, values.schema_sql),
            "SOURCE_SQL" => (1 << 1, values.source_sql, values.source_sql),
            "TARGET_SQL" => (1 << 2, values.target_sql, values.target_sql),
            "ROUND" => (1 << 3, values.round, values.round),
            "MAX_ROUNDS" => (1 << 4, values.max_rounds, values.max_rounds),
            "OUTPUT_JSON_PATH" => (1 << 5, runtime_output_path, identity_output_path),
            "FEEDBACK" => (1 << 6, values.feedback, values.feedback),
            "INTEGRITY_CONTRACT" => (1 << 7, values.integrity_contract, values.integrity_contract),
            "SEMANTIC_ROUND_BUDGET" => (
                1 << 8,
                values.semantic_round_budget,
                values.semantic_round_budget,
            ),
            _ => {
                return Err(invalid_prompt_template(format_args!(
                    "unknown placeholder `{{{{{name}}}}}`"
                )));
            }
        };
        if seen & bit != 0 {
            return Err(invalid_prompt_template(format_args!(
                "duplicate placeholder `{{{{{name}}}}}`"
            )));
        }
        seen |= bit;
        runtime.push_str(runtime_value);
        semantic_identity.push_str(identity_value);
        cursor = placeholder_start + close_offset + 2;
    }

    if seen != ALL_REQUIRED_PLACEHOLDERS {
        let missing = REQUIRED_PLACEHOLDERS
            .iter()
            .filter(|(_, bit)| seen & bit == 0)
            .map(|(name, _)| format!("{{{{{name}}}}}"))
            .collect::<Vec<_>>()
            .join(", ");
        return Err(invalid_prompt_template(format_args!(
            "missing required placeholder(s): {missing}"
        )));
    }

    Ok((runtime, semantic_identity))
}

pub fn build_counterexample_prompt(
    input: &VerificationInput,
    round: usize,
    max_rounds: usize,
    semantic_round_budget: usize,
    feedback: &[String],
    sql_time_zone: &SqlTimeZone,
    observation_certificates: Option<&ObservationCertificateReport>,
    output_path: &std::path::Path,
) -> Result<CounterexamplePrompt> {
    let feedback_text = if feedback.is_empty() {
        "None.".to_owned()
    } else {
        feedback
            .iter()
            .enumerate()
            .map(|(index, item)| format!("{}. {}", index + 1, item))
            .collect::<Vec<_>>()
            .join("\n")
    };
    let sql_time_zone_command = sql_time_zone
        .postgres_set_time_zone_sql()
        .ok_or_else(|| Error::InvalidSqlTimeZone(format!("{sql_time_zone:?}")))?;
    let round = round.to_string();
    let max_rounds = max_rounds.to_string();
    let semantic_round_budget = semantic_round_budget.to_string();
    let output_path = output_path.display().to_string();
    let integrity_contract = input.integrity_contract_summary();
    let values = PromptValues {
        schema_sql: input.schema_sql(),
        source_sql: input.source_sql(),
        target_sql: input.target_sql(),
        round: &round,
        max_rounds: &max_rounds,
        semantic_round_budget: &semantic_round_budget,
        feedback: &feedback_text,
        integrity_contract: &integrity_contract,
    };
    let (runtime_request, identity_request) = render_prompt_pair(
        COUNTEREXAMPLE_PROMPT,
        &values,
        &output_path,
        ASSESSMENT_IDENTITY_OUTPUT_PATH,
    )?;
    let observation_certificates = observation_certificates
        .map(serde_json::to_string_pretty)
        .transpose()?
        .unwrap_or_else(|| "{\"status\":\"unavailable\"}".to_owned());
    let semantic_context = format!(
        "{SHARED_SEMANTIC_PRIMER}\n\n\
         Configured PostgreSQL semantic context:\n\
         Interpret temporal values using this exact session time zone. The typed-witness \
         materializer applies the same command before executing candidate DML:\n\
         ```sql\n{sql_time_zone_command};\n```\n\n\
         Host-recomputed FormalQueryExpr observation analysis (navigation for the trusted proof only; it never authorizes PostgreSQL execution as an EQ/NEQ verdict):\n\
         ```json\n{observation_certificates}\n```\n\n"
    );

    Ok(CounterexamplePrompt {
        runtime: format!("{semantic_context}{runtime_request}"),
        semantic_identity: format!("{semantic_context}{identity_request}"),
    })
}

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};
    use std::sync::atomic::{AtomicU64, Ordering};

    use logos_ir::ir::SqlEnvironment;

    use super::*;

    static NEXT_TEST_DIRECTORY: AtomicU64 = AtomicU64::new(0);

    struct TestDirectory(PathBuf);

    impl TestDirectory {
        fn new() -> Self {
            let sequence = NEXT_TEST_DIRECTORY.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!(
                "logos-solver-prompt-{}-{sequence}",
                std::process::id()
            ));
            std::fs::create_dir_all(&path).expect("create prompt test directory");
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

    fn write_input(
        root: &Path,
        schema_sql: &str,
        source_sql: &str,
        target_sql: &str,
    ) -> VerificationInput {
        let schema = root.join("schema.sql");
        let source = root.join("source.sql");
        let target = root.join("target.sql");
        std::fs::write(&schema, schema_sql).expect("write schema SQL");
        std::fs::write(&source, source_sql).expect("write source SQL");
        std::fs::write(&target, target_sql).expect("write target SQL");
        VerificationInput::read_with_environment(schema, source, target, SqlEnvironment::default())
            .expect("read verification input")
    }

    fn value_between<'a>(text: &'a str, before: &str, after: &str) -> &'a str {
        let start = text.find(before).expect("opening prompt delimiter") + before.len();
        let end = start + text[start..].find(after).expect("closing prompt delimiter");
        &text[start..end]
    }

    fn split_output_slot(text: &str) -> (&str, &str, &str) {
        const BEFORE: &str = "Write exactly one JSON object to this file:\n\n";
        const AFTER: &str = "\n\nDo not put the final JSON answer in stdout.";
        let start = text.find(BEFORE).expect("output slot opening") + BEFORE.len();
        let end = start + text[start..].find(AFTER).expect("output slot closing");
        (&text[..start], &text[start..end], &text[end..])
    }

    #[test]
    fn inserted_sql_feedback_and_paths_are_never_rescanned_as_template_syntax() {
        const MARKERS: &str = "{{OUTPUT_JSON_PATH}} {{FEEDBACK}} {{SCHEMA_SQL}} \
            {{SOURCE_SQL}} {{TARGET_SQL}} {{ROUND}} {{MAX_ROUNDS}} \
            {{SEMANTIC_ROUND_BUDGET}} {{NOT_A_TEMPLATE}} {{UNFINISHED";
        let directory = TestDirectory::new();
        let schema_sql = format!("CREATE TABLE t (x TEXT); -- schema {MARKERS}\n");
        let source_sql = format!("SELECT '{MARKERS}'::text AS source_value;\n");
        let target_sql = format!("SELECT '{MARKERS}'::text AS target_value;\n");
        let feedback = format!("checker feedback bytes: {MARKERS}");
        let input = write_input(directory.path(), &schema_sql, &source_sql, &target_sql);
        let output_path = directory.path().join(format!("candidate {MARKERS}.json"));

        let built = build_counterexample_prompt(
            &input,
            7,
            11,
            3,
            std::slice::from_ref(&feedback),
            &SqlTimeZone::utc(),
            None,
            &output_path,
        )
        .expect("render adversarial prompt values");
        let semantic_identity = built.semantic_identity().to_owned();
        let runtime = built.into_runtime();

        let (runtime_prefix, runtime_output, runtime_suffix) = split_output_slot(&runtime);
        let (identity_prefix, identity_output, identity_suffix) =
            split_output_slot(&semantic_identity);
        assert_eq!(runtime_output, output_path.display().to_string());
        assert_eq!(identity_output, ASSESSMENT_IDENTITY_OUTPUT_PATH);
        assert_eq!(runtime_prefix, identity_prefix);
        assert_eq!(runtime_suffix, identity_suffix);

        assert_eq!(
            value_between(
                &runtime,
                "Schema:\n```sql\n",
                "\n```\n\nAuthoritative benchmark integrity contract"
            ),
            schema_sql
        );
        assert!(runtime.contains("No benchmark integrity constraints."));
        assert_eq!(
            value_between(
                &runtime,
                "Source query:\n```sql\n",
                "\n```\n\nTarget query:"
            ),
            source_sql
        );
        assert_eq!(
            value_between(
                &runtime,
                "Target query:\n```sql\n",
                "\n```\n\nProvider invocation "
            ),
            target_sql
        );
        assert!(runtime.contains("Provider invocation 7 of at most 11."));
        assert!(runtime.contains("semantic\nwitness-attempt budget is 3"));
        assert!(runtime.ends_with(&format!("Previous checker feedback:\n1. {feedback}\n")));
        assert!(runtime.starts_with("# Shared FormalSQL semantic primer\n"));
        assert!(runtime.contains("uncertainty, not NEQ."));
        assert!(runtime.contains(
            "Configured PostgreSQL semantic context:\nInterpret temporal values using this exact session time zone. The typed-witness materializer applies the same command before executing candidate DML:\n```sql\nSET TIME ZONE INTERVAL '+00:00' HOUR TO MINUTE;\n```\n\n"
        ));
        assert!(runtime.contains(
            "the counterexample path never executes the source and target to\n\
             decide equivalence."
        ));
        assert!(runtime.contains("a legal outcome on one side"));
        assert!(runtime.contains("cannot be matched by any legal outcome on the other side"));
        assert!(!runtime.contains("CountermodelFacts.v"));
        assert!(!runtime.contains("ProofAgentFacade.v"));
        assert!(!runtime.contains("Witness.generated_witness_db"));
    }

    #[test]
    fn renderer_rejects_missing_unknown_malformed_and_duplicate_placeholders() {
        let values = PromptValues {
            schema_sql: "schema",
            source_sql: "source",
            target_sql: "target",
            round: "1",
            max_rounds: "2",
            semantic_round_budget: "2",
            feedback: "feedback",
            integrity_contract: "contract",
        };
        let assert_rejected = |template: &str, expected: &str| {
            let error = render_prompt_pair(template, &values, "runtime", "identity")
                .expect_err("invalid template must fail closed")
                .to_string();
            assert!(
                error.contains(expected),
                "expected {expected:?} in {error:?}"
            );
        };

        let missing = COUNTEREXAMPLE_PROMPT.replacen("{{SCHEMA_SQL}}", "", 1);
        assert_rejected(&missing, "missing required placeholder(s): {{SCHEMA_SQL}}");

        let unknown = format!("{COUNTEREXAMPLE_PROMPT}\n{{{{UNKNOWN}}}}");
        assert_rejected(&unknown, "unknown placeholder `{{UNKNOWN}}`");

        let malformed = format!("{COUNTEREXAMPLE_PROMPT}\n{{{{BROKEN");
        assert_rejected(&malformed, "unclosed placeholder delimiter");

        let unmatched_close = format!("{COUNTEREXAMPLE_PROMPT}\n}}}}");
        assert_rejected(&unmatched_close, "unmatched closing delimiter");

        let duplicate = format!("{COUNTEREXAMPLE_PROMPT}\n{{{{SCHEMA_SQL}}}}");
        assert_rejected(&duplicate, "duplicate placeholder `{{SCHEMA_SQL}}`");
    }
}
