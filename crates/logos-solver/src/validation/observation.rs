use crate::core::{PostgresStructureToken, postgres_structure_tokens};
use crate::validation::types::ValidationWarning;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum ObservationMode {
    Bag,
    ExecutableSequence,
    Unclassifiable,
}

#[derive(Debug, Clone)]
pub(super) struct ObservationPlan {
    pub mode: ObservationMode,
    pub warnings: Vec<ValidationWarning>,
}

impl ObservationPlan {
    pub(super) fn rejection_message(&self) -> String {
        let details = self
            .warnings
            .iter()
            .map(|warning| warning.message.as_str())
            .collect::<Vec<_>>()
            .join("; ");
        format!(
            "PostgreSQL observation cannot be classified without approximating the submitted SQL: {details}"
        )
    }
}

pub(super) fn classify_observation(source: &str, target: &str) -> ObservationPlan {
    let mut warnings = Vec::new();
    let mut mode = ObservationMode::Bag;

    for (label, query) in [("source", source), ("target", target)] {
        match TopLevelFeatures::scan(query) {
            Ok(features) => {
                mode = mode.combine(features.observation_mode(label, &mut warnings));
            }
            Err(reason) => {
                mode = ObservationMode::Unclassifiable;
                warnings.push(ValidationWarning {
                    code: format!("{label}_observation_scan_unsupported"),
                    message: format!(
                        "{label} query cannot be classified without approximating PostgreSQL lexical structure ({reason}); validation is refused"
                    ),
                });
            }
        }
    }

    ObservationPlan { mode, warnings }
}

impl ObservationMode {
    fn combine(self, other: Self) -> Self {
        match (self, other) {
            (Self::Unclassifiable, _) | (_, Self::Unclassifiable) => Self::Unclassifiable,
            (Self::ExecutableSequence, _) | (_, Self::ExecutableSequence) => {
                Self::ExecutableSequence
            }
            (Self::Bag, Self::Bag) => Self::Bag,
        }
    }
}

#[derive(Debug, Clone, Copy, Default)]
struct TopLevelFeatures {
    has_order_by: bool,
    has_top_level_limit: bool,
    has_top_level_offset: bool,
    has_top_level_fetch: bool,
    has_nested_topk: bool,
    has_any_distinct_on: bool,
}

impl TopLevelFeatures {
    fn observation_mode(
        self,
        label: &str,
        warnings: &mut Vec<ValidationWarning>,
    ) -> ObservationMode {
        if self.has_order_by {
            warnings.push(ValidationWarning {
                code: format!("{label}_ordered_executable_sequence"),
                message: format!(
                    "{label} query has a top-level ORDER BY; PostgreSQL supplies one concrete sequence, which is authoritative only with a host-recomputed exact-observation functionality certificate"
                ),
            });
        }
        if self.has_nested_topk {
            warnings.push(ValidationWarning {
                code: format!("{label}_nested_topk_execution_choice"),
                message: format!(
                    "{label} query has nested LIMIT, OFFSET, or FETCH; one PostgreSQL execution may select only one of several legal observations, so a functionality or FormalSQL separation certificate is required"
                ),
            });
        }
        if self.has_any_distinct_on {
            warnings.push(ValidationWarning {
                code: format!("{label}_distinct_on_execution_choice"),
                message: format!(
                    "{label} query has DISTINCT ON; when ordering does not uniquely select a representative, one PostgreSQL choice is not a non-equivalence certificate"
                ),
            });
        }
        let has_top_level_slice =
            self.has_top_level_limit || self.has_top_level_offset || self.has_top_level_fetch;
        if has_top_level_slice {
            warnings.push(ValidationWarning {
                code: format!("{label}_topk_executable_sequence"),
                message: format!(
                    "{label} query has top-level LIMIT, OFFSET, or FETCH; the concrete PostgreSQL sequence is conclusive only after exact-observation functionality is certified"
                ),
            });
        }
        if self.has_order_by || has_top_level_slice {
            ObservationMode::ExecutableSequence
        } else {
            ObservationMode::Bag
        }
    }

    fn scan(sql: &str) -> Result<Self, String> {
        let lexemes = postgres_structure_tokens(sql)?;
        let range = query_lexeme_range(&lexemes)?;
        let mut features = TopLevelFeatures::default();
        let mut depth = 0usize;
        let mut words = Vec::new();

        for lexeme in &lexemes[range] {
            match lexeme {
                PostgresStructureToken::LeftParen => {
                    depth = depth.checked_add(1).ok_or_else(|| {
                        "parenthesis nesting exceeds the supported range".to_owned()
                    })?
                }
                PostgresStructureToken::RightParen => {
                    depth = depth
                        .checked_sub(1)
                        .ok_or_else(|| "unmatched closing parenthesis".to_owned())?;
                }
                PostgresStructureToken::Word(word) => words.push((depth, word.as_str())),
            }
        }
        if depth != 0 {
            return Err("unmatched opening parenthesis".to_owned());
        }

        for index in 0..words.len() {
            let (depth, word) = words[index];
            match word {
                "order"
                    if depth == 0
                        && words
                            .get(index + 1)
                            .is_some_and(|next| *next == (depth, "by")) =>
                {
                    features.has_order_by = true;
                }
                "limit" if depth == 0 => features.has_top_level_limit = true,
                "offset" if depth == 0 => features.has_top_level_offset = true,
                "fetch" if depth == 0 => features.has_top_level_fetch = true,
                "limit" | "offset" | "fetch" => features.has_nested_topk = true,
                "distinct"
                    if words
                        .get(index + 1)
                        .is_some_and(|next| *next == (depth, "on")) =>
                {
                    features.has_any_distinct_on = true;
                }
                _ => {}
            }
        }
        Ok(features)
    }
}

fn query_lexeme_range(
    lexemes: &[PostgresStructureToken],
) -> Result<std::ops::Range<usize>, String> {
    let mut start = 0usize;
    let mut end = lexemes.len();
    while lexemes.get(start) == Some(&PostgresStructureToken::LeftParen) {
        let mut depth = 0usize;
        let mut matching_close = None;
        for (index, lexeme) in lexemes.iter().enumerate().take(end).skip(start) {
            match lexeme {
                PostgresStructureToken::LeftParen => {
                    depth = depth.checked_add(1).ok_or_else(|| {
                        "parenthesis nesting exceeds the supported range".to_owned()
                    })?;
                }
                PostgresStructureToken::RightParen => {
                    depth = depth
                        .checked_sub(1)
                        .ok_or_else(|| "unmatched closing parenthesis".to_owned())?;
                    if depth == 0 {
                        matching_close = Some(index);
                        break;
                    }
                }
                PostgresStructureToken::Word(_) => {}
            }
        }
        if matching_close == Some(end - 1) {
            start += 1;
            end -= 1;
        } else {
            break;
        }
    }
    Ok(start..end)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn validates_source_top_level_order_by_as_an_executable_sequence() {
        let plan = classify_observation("select * from t order by a", "select * from t");
        assert_eq!(plan.mode, ObservationMode::ExecutableSequence);
        assert_eq!(plan.warnings.len(), 1);
        assert_eq!(plan.warnings[0].code, "source_ordered_executable_sequence");
    }

    #[test]
    fn validates_target_top_level_order_by_as_an_executable_sequence() {
        let plan = classify_observation("select * from t", "select * from t order by a");
        assert_eq!(plan.mode, ObservationMode::ExecutableSequence);
        assert_eq!(plan.warnings.len(), 1);
        assert_eq!(plan.warnings[0].code, "target_ordered_executable_sequence");
    }

    #[test]
    fn ignores_nested_order_by_without_top_level_observation() {
        let plan = classify_observation(
            "select * from (select * from t order by a) q",
            "select * from t",
        );
        assert_eq!(plan.mode, ObservationMode::Bag);
        assert!(plan.warnings.is_empty());
    }

    #[test]
    fn validates_nested_limit_by_the_outer_bag_observation() {
        let plan = classify_observation(
            "select * from (select * from t limit 1) q",
            "select * from t",
        );
        assert_eq!(plan.mode, ObservationMode::Bag);
        assert_eq!(plan.warnings[0].code, "source_nested_topk_execution_choice");
    }

    #[test]
    fn validates_limit_as_an_executable_sequence_without_synthetic_ordinals() {
        let plan = classify_observation(
            "select * from t order by non_unique limit 1",
            "select * from t order by non_unique limit 1",
        );
        assert_eq!(plan.mode, ObservationMode::ExecutableSequence);
        assert_eq!(plan.warnings.len(), 4);
        assert!(
            plan.warnings
                .iter()
                .any(|warning| warning.code == "source_topk_executable_sequence")
        );
    }

    #[test]
    fn validates_offset_and_fetch_as_executable_sequences() {
        let plan = classify_observation(
            "select * from t offset 1",
            "select * from t fetch first 1 row only",
        );
        assert_eq!(plan.mode, ObservationMode::ExecutableSequence);
        assert_eq!(plan.warnings.len(), 2);
    }

    #[test]
    fn validates_distinct_on_as_the_concrete_postgres_execution() {
        let plan = classify_observation(
            "select distinct on (k) k, v from t order by k",
            "select distinct on (k) k, v from t order by k",
        );
        assert_eq!(plan.mode, ObservationMode::ExecutableSequence);
        assert_eq!(plan.warnings.len(), 4);
        assert!(
            plan.warnings
                .iter()
                .any(|warning| warning.code == "source_distinct_on_execution_choice")
        );
    }

    #[test]
    fn detects_order_by_inside_whole_query_parentheses() {
        let plan = classify_observation("((select * from t order by a))", "select * from t");
        assert_eq!(plan.mode, ObservationMode::ExecutableSequence);
    }

    #[test]
    fn skips_dollar_quoted_strings() {
        let plan = classify_observation("select $$ limit 1 $$ as text", "select 'x' as text");
        assert_eq!(plan.mode, ObservationMode::Bag);
        assert!(plan.warnings.is_empty());
    }

    #[test]
    fn ordinary_string_backslash_does_not_escape_closing_quote() {
        let plan = classify_observation(r"select 'ordinary \' order by a", "select 'ordinary'");
        assert_eq!(plan.mode, ObservationMode::ExecutableSequence);
        assert_eq!(plan.warnings[0].code, "source_ordered_executable_sequence");
    }

    #[test]
    fn escape_string_backslash_does_escape_quote() {
        let plan = classify_observation(
            r"select E'not a query: \' order by a' as text",
            "select 'x' as text",
        );
        assert_eq!(plan.mode, ObservationMode::Bag);
        assert!(plan.warnings.is_empty());
    }

    #[test]
    fn skips_nested_block_comments() {
        let plan = classify_observation(
            "select /* outer /* inner */ limit 1 */ * from t",
            "select * from t",
        );
        assert_eq!(plan.mode, ObservationMode::Bag);
        assert!(plan.warnings.is_empty());
    }

    #[test]
    fn malformed_lexical_structure_is_rejected_conservatively() {
        let plan = classify_observation("select 'unterminated", "select 1");
        assert_eq!(plan.mode, ObservationMode::Unclassifiable);
        assert_eq!(plan.warnings[0].code, "source_observation_scan_unsupported");
    }
}
