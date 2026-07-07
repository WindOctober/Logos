use crate::core::VerificationInput;

const COUNTEREXAMPLE_PROMPT: &str = include_str!("../../prompts/counterexample.md");

pub fn build_counterexample_prompt(
    input: &VerificationInput,
    round: usize,
    max_rounds: usize,
    feedback: &[String],
    output_path: &std::path::Path,
) -> String {
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

    COUNTEREXAMPLE_PROMPT
        .replace("{{SCHEMA_SQL}}", input.schema_sql())
        .replace("{{SOURCE_SQL}}", input.source_sql())
        .replace("{{TARGET_SQL}}", input.target_sql())
        .replace("{{ROUND}}", &round.to_string())
        .replace("{{MAX_ROUNDS}}", &max_rounds.to_string())
        .replace("{{OUTPUT_JSON_PATH}}", &output_path.display().to_string())
        .replace("{{FEEDBACK}}", &feedback_text)
}
