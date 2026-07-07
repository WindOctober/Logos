use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum ObservationMode {
    Bag,
    OrderedList,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ValidationWarning {
    pub code: String,
    pub message: String,
}

#[derive(Debug, Clone)]
pub(super) struct ObservationPlan {
    pub mode: ObservationMode,
    pub warnings: Vec<ValidationWarning>,
}

pub(super) fn classify_observation(source: &str, target: &str) -> ObservationPlan {
    let source_features = TopLevelFeatures::scan(source);
    let target_features = TopLevelFeatures::scan(target);
    let order_sensitive =
        source_features.is_order_sensitive() || target_features.is_order_sensitive();
    let mut warnings = Vec::new();

    for (label, features) in [("source", source_features), ("target", target_features)] {
        if features.has_unstable_topk() {
            warnings.push(ValidationWarning {
                code: format!("{label}_topk_without_order_by"),
                message: format!(
                    "{label} query uses LIMIT/OFFSET/FETCH without a top-level ORDER BY; validation compares the observed PostgreSQL row order"
                ),
            });
        }
        if features.has_distinct_on && !features.has_order_by {
            warnings.push(ValidationWarning {
                code: format!("{label}_distinct_on_without_order_by"),
                message: format!(
                    "{label} query uses DISTINCT ON without a top-level ORDER BY; validation compares the observed PostgreSQL row order"
                ),
            });
        }
    }

    ObservationPlan {
        mode: if order_sensitive || !warnings.is_empty() {
            ObservationMode::OrderedList
        } else {
            ObservationMode::Bag
        },
        warnings,
    }
}

#[derive(Debug, Clone, Copy, Default)]
struct TopLevelFeatures {
    has_order_by: bool,
    has_limit: bool,
    has_offset: bool,
    has_fetch: bool,
    has_distinct_on: bool,
}

impl TopLevelFeatures {
    fn is_order_sensitive(self) -> bool {
        self.has_order_by
            || self.has_limit
            || self.has_offset
            || self.has_fetch
            || self.has_distinct_on
    }

    fn has_unstable_topk(self) -> bool {
        (self.has_limit || self.has_offset || self.has_fetch) && !self.has_order_by
    }

    fn scan(sql: &str) -> Self {
        let tokens = top_level_tokens(sql);
        let mut features = TopLevelFeatures::default();
        for index in 0..tokens.len() {
            match tokens[index].as_str() {
                "ORDER" if tokens.get(index + 1).is_some_and(|next| next == "BY") => {
                    features.has_order_by = true;
                }
                "LIMIT" => features.has_limit = true,
                "OFFSET" => features.has_offset = true,
                "FETCH" => features.has_fetch = true,
                "DISTINCT" if tokens.get(index + 1).is_some_and(|next| next == "ON") => {
                    features.has_distinct_on = true;
                }
                _ => {}
            }
        }
        features
    }
}

fn top_level_tokens(sql: &str) -> Vec<String> {
    let sql = strip_redundant_enclosing_parens(sql);
    let mut tokens = Vec::new();
    let mut token = String::new();
    let mut depth = 0usize;
    let mut chars = sql.chars().peekable();
    while let Some(ch) = chars.next() {
        match ch {
            '\'' => skip_single_quoted_string(&mut chars),
            '"' => skip_double_quoted_identifier(&mut chars),
            '-' if chars.peek() == Some(&'-') => {
                chars.next();
                skip_line_comment(&mut chars);
            }
            '/' if chars.peek() == Some(&'*') => {
                chars.next();
                skip_block_comment(&mut chars);
            }
            '$' if try_skip_dollar_quoted_string(&mut chars) => {}
            '(' => {
                flush_token(&mut tokens, &mut token, depth);
                depth += 1;
            }
            ')' => {
                flush_token(&mut tokens, &mut token, depth);
                depth = depth.saturating_sub(1);
            }
            _ if depth == 0 && is_token_char(ch) => token.push(ch.to_ascii_uppercase()),
            _ => flush_token(&mut tokens, &mut token, depth),
        }
    }
    flush_token(&mut tokens, &mut token, depth);
    tokens
}

fn strip_redundant_enclosing_parens(mut sql: &str) -> &str {
    loop {
        let trimmed = sql.trim();
        let Some(inner) = enclosed_by_single_paren_pair(trimmed) else {
            return trimmed;
        };
        sql = inner;
    }
}

fn enclosed_by_single_paren_pair(sql: &str) -> Option<&str> {
    if !sql.starts_with('(') || !sql.ends_with(')') {
        return None;
    }

    let mut depth = 0usize;
    let mut chars = sql.char_indices().peekable();
    while let Some((index, ch)) = chars.next() {
        match ch {
            '\'' => skip_single_quoted_string_with_indices(&mut chars),
            '"' => skip_double_quoted_identifier_with_indices(&mut chars),
            '-' if chars.peek().is_some_and(|(_, next)| *next == '-') => {
                chars.next();
                skip_line_comment_with_indices(&mut chars);
            }
            '/' if chars.peek().is_some_and(|(_, next)| *next == '*') => {
                chars.next();
                skip_block_comment_with_indices(&mut chars);
            }
            '$' if try_skip_dollar_quoted_string_with_indices(&mut chars) => {}
            '(' => depth += 1,
            ')' => {
                depth = depth.saturating_sub(1);
                if depth == 0 && index != sql.len() - 1 {
                    return None;
                }
            }
            _ => {}
        }
    }

    Some(&sql[1..sql.len() - 1])
}

fn flush_token(tokens: &mut Vec<String>, token: &mut String, depth: usize) {
    if depth == 0 && !token.is_empty() {
        tokens.push(std::mem::take(token));
    } else {
        token.clear();
    }
}

fn is_token_char(ch: char) -> bool {
    ch.is_ascii_alphanumeric() || ch == '_'
}

fn skip_single_quoted_string(chars: &mut std::iter::Peekable<std::str::Chars<'_>>) {
    while let Some(ch) = chars.next() {
        if ch == '\\' {
            chars.next();
        } else if ch == '\'' {
            if chars.peek() == Some(&'\'') {
                chars.next();
            } else {
                break;
            }
        }
    }
}

fn skip_double_quoted_identifier(chars: &mut std::iter::Peekable<std::str::Chars<'_>>) {
    while let Some(ch) = chars.next() {
        if ch == '"' {
            if chars.peek() == Some(&'"') {
                chars.next();
            } else {
                break;
            }
        }
    }
}

fn skip_line_comment(chars: &mut std::iter::Peekable<std::str::Chars<'_>>) {
    for ch in chars.by_ref() {
        if ch == '\n' {
            break;
        }
    }
}

fn skip_block_comment(chars: &mut std::iter::Peekable<std::str::Chars<'_>>) {
    let mut depth = 1usize;
    while let Some(ch) = chars.next() {
        if ch == '/' && chars.peek() == Some(&'*') {
            chars.next();
            depth += 1;
        } else if ch == '*' && chars.peek() == Some(&'/') {
            chars.next();
            depth -= 1;
            if depth == 0 {
                break;
            }
        }
    }
}

fn try_skip_dollar_quoted_string(chars: &mut std::iter::Peekable<std::str::Chars<'_>>) -> bool {
    let Some(delimiter) = dollar_quote_delimiter(chars.clone()) else {
        return false;
    };
    for _ in 1..delimiter.chars().count() {
        chars.next();
    }
    skip_until_delimiter(chars, &delimiter);
    true
}

fn dollar_quote_delimiter(mut chars: std::iter::Peekable<std::str::Chars<'_>>) -> Option<String> {
    let mut delimiter = String::from("$");
    while let Some(ch) = chars.next() {
        delimiter.push(ch);
        if ch == '$' {
            return Some(delimiter);
        }
        if !(ch.is_ascii_alphanumeric() || ch == '_') {
            return None;
        }
    }
    None
}

fn skip_until_delimiter(chars: &mut std::iter::Peekable<std::str::Chars<'_>>, delimiter: &str) {
    let mut window = String::new();
    let delimiter_len = delimiter.chars().count();
    while let Some(ch) = chars.next() {
        window.push(ch);
        while window.chars().count() > delimiter_len {
            let next_len = window.chars().next().map_or(0, char::len_utf8);
            window.drain(..next_len);
        }
        if window == delimiter {
            break;
        }
    }
}

fn skip_single_quoted_string_with_indices(
    chars: &mut std::iter::Peekable<std::str::CharIndices<'_>>,
) {
    while let Some((_, ch)) = chars.next() {
        if ch == '\\' {
            chars.next();
        } else if ch == '\'' {
            if chars.peek().is_some_and(|(_, next)| *next == '\'') {
                chars.next();
            } else {
                break;
            }
        }
    }
}

fn skip_double_quoted_identifier_with_indices(
    chars: &mut std::iter::Peekable<std::str::CharIndices<'_>>,
) {
    while let Some((_, ch)) = chars.next() {
        if ch == '"' {
            if chars.peek().is_some_and(|(_, next)| *next == '"') {
                chars.next();
            } else {
                break;
            }
        }
    }
}

fn skip_line_comment_with_indices(chars: &mut std::iter::Peekable<std::str::CharIndices<'_>>) {
    for (_, ch) in chars.by_ref() {
        if ch == '\n' {
            break;
        }
    }
}

fn skip_block_comment_with_indices(chars: &mut std::iter::Peekable<std::str::CharIndices<'_>>) {
    let mut depth = 1usize;
    while let Some((_, ch)) = chars.next() {
        if ch == '/' && chars.peek().is_some_and(|(_, next)| *next == '*') {
            chars.next();
            depth += 1;
        } else if ch == '*' && chars.peek().is_some_and(|(_, next)| *next == '/') {
            chars.next();
            depth -= 1;
            if depth == 0 {
                break;
            }
        }
    }
}

fn try_skip_dollar_quoted_string_with_indices(
    chars: &mut std::iter::Peekable<std::str::CharIndices<'_>>,
) -> bool {
    let Some(delimiter) = dollar_quote_delimiter_with_indices(chars.clone()) else {
        return false;
    };
    for _ in 1..delimiter.chars().count() {
        chars.next();
    }
    skip_until_delimiter_with_indices(chars, &delimiter);
    true
}

fn dollar_quote_delimiter_with_indices(
    mut chars: std::iter::Peekable<std::str::CharIndices<'_>>,
) -> Option<String> {
    let mut delimiter = String::from("$");
    while let Some((_, ch)) = chars.next() {
        delimiter.push(ch);
        if ch == '$' {
            return Some(delimiter);
        }
        if !(ch.is_ascii_alphanumeric() || ch == '_') {
            return None;
        }
    }
    None
}

fn skip_until_delimiter_with_indices(
    chars: &mut std::iter::Peekable<std::str::CharIndices<'_>>,
    delimiter: &str,
) {
    let mut window = String::new();
    let delimiter_len = delimiter.chars().count();
    while let Some((_, ch)) = chars.next() {
        window.push(ch);
        while window.chars().count() > delimiter_len {
            let next_len = window.chars().next().map_or(0, char::len_utf8);
            window.drain(..next_len);
        }
        if window == delimiter {
            break;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn detects_top_level_order_by() {
        let plan = classify_observation("select * from t order by a", "select * from t");
        assert_eq!(plan.mode, ObservationMode::OrderedList);
        assert!(plan.warnings.is_empty());
    }

    #[test]
    fn ignores_nested_order_by_without_top_level_observation() {
        let plan = classify_observation(
            "select * from (select * from t order by a) q",
            "select * from t",
        );
        assert_eq!(plan.mode, ObservationMode::Bag);
    }

    #[test]
    fn warns_on_limit_without_order_by() {
        let plan = classify_observation("select * from t limit 1", "select * from t limit 1");
        assert_eq!(plan.mode, ObservationMode::OrderedList);
        assert_eq!(plan.warnings.len(), 2);
    }

    #[test]
    fn detects_order_by_inside_whole_query_parentheses() {
        let plan = classify_observation("(select * from t order by a)", "select * from t");
        assert_eq!(plan.mode, ObservationMode::OrderedList);
    }

    #[test]
    fn skips_dollar_quoted_strings() {
        let plan = classify_observation("select $$ limit 1 $$ as text", "select 'x' as text");
        assert_eq!(plan.mode, ObservationMode::Bag);
        assert!(plan.warnings.is_empty());
    }

    #[test]
    fn skips_escape_string_quotes() {
        let plan = classify_observation(
            r"select E'not a query: \' limit 1' as text",
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
}
