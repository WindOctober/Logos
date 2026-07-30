//! One conservative lexical authority for Calcite-retained SQL source.
//!
//! This is deliberately not a SQL parser. It identifies byte-exact lexical
//! regions so source-attestation consumers cannot disagree about whether
//! comments, quoted text, or delimiters expose SQL structure. Purpose-specific
//! projections in `convert` and `query_shape` remain responsible for deciding
//! which otherwise valid lexical forms their proof boundary supports.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum LexemeKind {
    Whitespace,
    LineComment,
    BlockComment,
    Word,
    QuotedIdentifier { quote: u8 },
    StandardString,
    EscapeString,
    DollarString,
    Number,
    Operator,
    Symbol,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Lexeme {
    pub(super) kind: LexemeKind,
    pub(super) start: usize,
    pub(super) end: usize,
}

impl Lexeme {
    pub(super) fn text<'a>(&self, source: &'a str) -> Option<&'a str> {
        source.get(self.start..self.end)
    }

    pub(super) fn is_symbol(&self, source: &str, symbol: &str) -> bool {
        matches!(self.kind, LexemeKind::Operator | LexemeKind::Symbol)
            && self.text(source) == Some(symbol)
    }

    pub(super) fn is_trivia(&self) -> bool {
        matches!(
            self.kind,
            LexemeKind::Whitespace | LexemeKind::LineComment | LexemeKind::BlockComment
        )
    }

    pub(super) fn is_protected(&self) -> bool {
        matches!(
            self.kind,
            LexemeKind::QuotedIdentifier { .. }
                | LexemeKind::StandardString
                | LexemeKind::EscapeString
                | LexemeKind::DollarString
        )
    }
}

pub(super) fn postgres_whitespace(byte: u8) -> bool {
    matches!(byte, b' ' | b'\t' | b'\n' | b'\r' | 0x0c | 0x0b)
}

fn bare_identifier_start(byte: u8) -> bool {
    byte.is_ascii_alphabetic() || byte == b'_'
}

fn bare_identifier_part(byte: u8) -> bool {
    bare_identifier_start(byte) || byte.is_ascii_digit() || byte == b'$'
}

fn identifier_adjacency(byte: u8) -> bool {
    bare_identifier_part(byte) || !byte.is_ascii()
}

/// Whether one structured identifier component can be Calcite's unquoted
/// display of a PostgreSQL identifier. This does not make high-bit unquoted
/// source text generally admissible; callers must separately bind the display
/// to parser-backed exact quoted text.
pub(super) fn calcite_rendered_identifier_component(value: &str) -> bool {
    let Some((&first, rest)) = value.as_bytes().split_first() else {
        return false;
    };
    (bare_identifier_start(first) || !first.is_ascii())
        && rest
            .iter()
            .all(|byte| bare_identifier_part(*byte) || !byte.is_ascii())
}

fn line_comment_end(source: &[u8], mut index: usize) -> usize {
    while index < source.len() && !matches!(source[index], b'\n' | b'\r') {
        index += 1;
    }
    index
}

fn block_comment_end(source: &[u8], start: usize) -> Option<usize> {
    let mut index = start.checked_add(2)?;
    let mut depth = 1usize;
    while index < source.len() {
        match (source[index], source.get(index + 1).copied()) {
            (b'/', Some(b'*')) => {
                depth = depth.checked_add(1)?;
                index += 2;
            }
            (b'*', Some(b'/')) => {
                depth = depth.checked_sub(1)?;
                index += 2;
                if depth == 0 {
                    return Some(index);
                }
            }
            _ => index += 1,
        }
    }
    None
}

fn quoted_end(source: &[u8], start: usize, quote: u8, backslash_escapes: bool) -> Option<usize> {
    let mut index = start.checked_add(1)?;
    while index < source.len() {
        let current = source[index];
        index += 1;
        if current == b'\\' && backslash_escapes && index < source.len() {
            index += 1;
        } else if current == quote {
            if source.get(index) == Some(&quote) {
                index += 1;
            } else {
                return Some(index);
            }
        }
    }
    None
}

/// Return the end of a recognized opening dollar delimiter. High-bit tag
/// bytes are valid only under locale-sensitive PostgreSQL identifier rules;
/// this framework rejects that rare spelling rather than approximating it.
fn dollar_delimiter_end(source: &[u8], start: usize) -> Option<Result<Option<usize>, ()>> {
    if source.get(start) != Some(&b'$') {
        return None;
    }
    if start > 0 && identifier_adjacency(source[start - 1]) {
        return Some(Ok(None));
    }
    let first = start.checked_add(1)?;
    if source.get(first) == Some(&b'$') {
        return Some(Ok(Some(first + 1)));
    }
    let Some(&first_byte) = source.get(first) else {
        return Some(Ok(None));
    };
    if !first_byte.is_ascii() {
        return Some(Err(()));
    }
    if !bare_identifier_start(first_byte) {
        return Some(Ok(None));
    }
    let mut index = first + 1;
    while let Some(&byte) = source.get(index) {
        if byte == b'$' {
            return Some(Ok(Some(index + 1)));
        }
        if !byte.is_ascii() {
            return Some(Err(()));
        }
        if !bare_identifier_start(byte) && !byte.is_ascii_digit() {
            return Some(Ok(None));
        }
        index += 1;
    }
    Some(Ok(None))
}

fn dollar_string_end(source: &[u8], start: usize, delimiter_end: usize) -> Option<usize> {
    let delimiter = source.get(start..delimiter_end)?;
    let relative = source
        .get(delimiter_end..)?
        .windows(delimiter.len())
        .position(|candidate| candidate == delimiter)?;
    delimiter_end
        .checked_add(relative)?
        .checked_add(delimiter.len())
}

fn word_end(source: &[u8], mut index: usize) -> usize {
    index += 1;
    while source
        .get(index)
        .is_some_and(|byte| bare_identifier_part(*byte))
    {
        index += 1;
    }
    index
}

fn number_end(source: &[u8], start: usize) -> usize {
    let mut index = start;
    if source[index] == b'.' {
        index += 1;
        while source
            .get(index)
            .is_some_and(|byte| byte.is_ascii_digit() || *byte == b'_')
        {
            index += 1;
        }
    } else if source.get(index) == Some(&b'0')
        && source
            .get(index + 1)
            .is_some_and(|byte| matches!(byte, b'x' | b'X' | b'o' | b'O' | b'b' | b'B'))
    {
        index += 2;
        while source
            .get(index)
            .is_some_and(|byte| byte.is_ascii_alphanumeric() || *byte == b'_')
        {
            index += 1;
        }
        return index;
    } else {
        while source
            .get(index)
            .is_some_and(|byte| byte.is_ascii_digit() || *byte == b'_')
        {
            index += 1;
        }
        if source.get(index) == Some(&b'.') {
            index += 1;
            while source
                .get(index)
                .is_some_and(|byte| byte.is_ascii_digit() || *byte == b'_')
            {
                index += 1;
            }
        }
    }
    if source
        .get(index)
        .is_some_and(|byte| matches!(byte, b'e' | b'E'))
    {
        let exponent = index;
        index += 1;
        if source
            .get(index)
            .is_some_and(|byte| matches!(byte, b'+' | b'-'))
        {
            index += 1;
        }
        let digits = index;
        while source
            .get(index)
            .is_some_and(|byte| byte.is_ascii_digit() || *byte == b'_')
        {
            index += 1;
        }
        if index == digits {
            index = exponent;
        }
    }
    // Malformed number/identifier adjacency stays one opaque token rather
    // than becoming equal to a valid whitespace-separated sequence.
    while source
        .get(index)
        .is_some_and(|byte| bare_identifier_part(*byte))
    {
        index += 1;
    }
    index
}

fn operator_byte(byte: u8) -> bool {
    matches!(
        byte,
        b'+' | b'-'
            | b'*'
            | b'/'
            | b'<'
            | b'>'
            | b'='
            | b'~'
            | b'!'
            | b'@'
            | b'#'
            | b'%'
            | b'^'
            | b'&'
            | b'|'
            | b'?'
            | b':'
    )
}

pub(super) fn lex(source: &str) -> Option<Vec<Lexeme>> {
    let bytes = source.as_bytes();
    let mut lexemes = Vec::new();
    let mut index = 0usize;
    while index < bytes.len() {
        let start = index;
        let (kind, end) = match (bytes[index], bytes.get(index + 1).copied()) {
            (byte, _) if postgres_whitespace(byte) => {
                index += 1;
                while bytes
                    .get(index)
                    .is_some_and(|byte| postgres_whitespace(*byte))
                {
                    index += 1;
                }
                (LexemeKind::Whitespace, index)
            }
            (b'-', Some(b'-')) => (LexemeKind::LineComment, line_comment_end(bytes, index + 2)),
            (b'/', Some(b'*')) => (LexemeKind::BlockComment, block_comment_end(bytes, index)?),
            (b'"', _) => (
                LexemeKind::QuotedIdentifier { quote: b'"' },
                quoted_end(bytes, index, b'"', false)?,
            ),
            (b'`', _) => (
                LexemeKind::QuotedIdentifier { quote: b'`' },
                quoted_end(bytes, index, b'`', false)?,
            ),
            (b'\'', _) => (
                LexemeKind::StandardString,
                quoted_end(bytes, index, b'\'', false)?,
            ),
            (b'$', _) => match dollar_delimiter_end(bytes, index)?.ok()? {
                Some(delimiter_end) => (
                    LexemeKind::DollarString,
                    dollar_string_end(bytes, index, delimiter_end)?,
                ),
                None => (LexemeKind::Symbol, index + 1),
            },
            (byte, _) if bare_identifier_start(byte) => {
                let word_end = word_end(bytes, index);
                let standalone_escape = word_end == index + 1
                    && matches!(byte, b'E' | b'e')
                    && bytes.get(word_end) == Some(&b'\'')
                    && (index == 0 || !identifier_adjacency(bytes[index - 1]));
                if standalone_escape {
                    (
                        LexemeKind::EscapeString,
                        quoted_end(bytes, word_end, b'\'', true)?,
                    )
                } else {
                    (LexemeKind::Word, word_end)
                }
            }
            (byte, _) if byte.is_ascii_digit() => (LexemeKind::Number, number_end(bytes, index)),
            (b'.', Some(next)) if next.is_ascii_digit() => {
                (LexemeKind::Number, number_end(bytes, index))
            }
            (byte, _) if operator_byte(byte) => {
                index += 1;
                while bytes.get(index).is_some_and(|byte| operator_byte(*byte)) {
                    index += 1;
                }
                (LexemeKind::Operator, index)
            }
            // PostgreSQL admits high-bit bytes in unquoted identifiers. This
            // deliberately ASCII-only source authority cannot classify their
            // locale-sensitive continuation precisely, so reject the whole
            // source instead of exposing an adjacent ASCII keyword fragment.
            (byte, _) if !byte.is_ascii() => return None,
            _ => (LexemeKind::Symbol, index + 1),
        };
        lexemes.push(Lexeme { kind, start, end });
        index = end;
    }
    Some(lexemes)
}

/// Parenthesis depth for each lexeme. `(` receives its pre-open depth and `)`
/// its post-close depth, matching the historical Calcite source projections.
pub(super) fn parenthesis_depths(source: &str, lexemes: &[Lexeme]) -> Option<Vec<usize>> {
    let mut result = Vec::with_capacity(lexemes.len());
    let mut depth = 0usize;
    for lexeme in lexemes {
        if lexeme.is_symbol(source, "(") {
            result.push(depth);
            depth = depth.checked_add(1)?;
        } else if lexeme.is_symbol(source, ")") {
            depth = depth.checked_sub(1)?;
            result.push(depth);
        } else {
            result.push(depth);
        }
    }
    (depth == 0).then_some(result)
}

/// Validate and annotate all grouping delimiters used by the source
/// structural checks. The returned value is the nesting depth before ordinary
/// tokens, before an opener, and after a closer.
pub(super) fn grouping_depths(source: &str, lexemes: &[Lexeme]) -> Option<Vec<usize>> {
    let mut result = Vec::with_capacity(lexemes.len());
    let mut expected = Vec::new();
    for lexeme in lexemes {
        let opener = [("(", ")"), ("[", "]"), ("{", "}")]
            .into_iter()
            .find(|(open, _)| lexeme.is_symbol(source, open));
        if let Some((_, close)) = opener {
            result.push(expected.len());
            expected.push(close);
            continue;
        }
        if let Some(close) = [")", "]", "}"]
            .into_iter()
            .find(|close| lexeme.is_symbol(source, close))
        {
            if expected.pop() != Some(close) {
                return None;
            }
            result.push(expected.len());
            continue;
        }
        result.push(expected.len());
    }
    expected.is_empty().then_some(result)
}

pub(super) fn skip_trivia(source: &str, lexemes: &[Lexeme], start: usize) -> Option<usize> {
    if start > source.len() || !source.is_char_boundary(start) {
        return None;
    }
    let mut index = start;
    for lexeme in lexemes.iter().filter(|lexeme| lexeme.end > start) {
        if lexeme.start != index || !lexeme.is_trivia() {
            break;
        }
        index = lexeme.end;
    }
    Some(index)
}

pub(super) fn matching_parenthesis(source: &str, lexemes: &[Lexeme], open: usize) -> Option<usize> {
    let open_index = lexemes
        .iter()
        .position(|lexeme| lexeme.start == open && lexeme.is_symbol(source, "("))?;
    let mut depth = 0usize;
    for lexeme in &lexemes[open_index..] {
        if lexeme.is_symbol(source, "(") {
            depth = depth.checked_add(1)?;
        } else if lexeme.is_symbol(source, ")") {
            depth = depth.checked_sub(1)?;
            if depth == 0 {
                return Some(lexeme.end);
            }
        }
    }
    None
}

pub(super) fn decode_doubled(source: &str, lexeme: Lexeme) -> Option<String> {
    let (prefix, quote) = match lexeme.kind {
        LexemeKind::QuotedIdentifier { quote } => (1usize, quote),
        LexemeKind::StandardString => (1usize, b'\''),
        _ => return None,
    };
    let raw = source.get(lexeme.start + prefix..lexeme.end.checked_sub(1)?)?;
    let doubled = [quote, quote];
    let mut decoded = Vec::with_capacity(raw.len());
    let bytes = raw.as_bytes();
    let mut index = 0usize;
    while index < bytes.len() {
        if bytes.get(index..index + 2) == Some(doubled.as_slice()) {
            decoded.push(quote);
            index += 2;
        } else {
            decoded.push(bytes[index]);
            index += 1;
        }
    }
    String::from_utf8(decoded).ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn kinds(source: &str) -> Option<Vec<(LexemeKind, String, usize, usize)>> {
        lex(source).map(|tokens| {
            tokens
                .into_iter()
                .map(|token| {
                    (
                        token.kind,
                        token.text(source).unwrap().to_owned(),
                        token.start,
                        token.end,
                    )
                })
                .collect()
        })
    }

    #[test]
    fn protects_nested_comments_and_cr_lf_line_comments_with_exact_spans() {
        let source = "a/* outer /* SELECT */ JOIN */b-- WHERE\rc";
        let tokens = kinds(source).unwrap();
        assert_eq!(tokens[0], (LexemeKind::Word, "a".to_owned(), 0, 1));
        assert_eq!(tokens[1].0, LexemeKind::BlockComment);
        assert_eq!(tokens[2].1, "b");
        assert_eq!(tokens[3].0, LexemeKind::LineComment);
        assert_eq!(tokens[4].0, LexemeKind::Whitespace);
        assert_eq!(tokens[5].1, "c");
        assert!(lex("/* outer /* inner */").is_none());
    }

    #[test]
    fn distinguishes_standard_escape_and_doubled_quoted_tokens() {
        let source = "'a\\\\' \"a\"\"b\" `c``d` E'not \\' ORDER BY'";
        let tokens = lex(source).unwrap();
        assert_eq!(tokens[0].kind, LexemeKind::StandardString);
        assert_eq!(tokens[2].kind, LexemeKind::QuotedIdentifier { quote: b'"' });
        assert_eq!(decode_doubled(source, tokens[2]), Some("a\"b".to_owned()));
        assert_eq!(tokens[4].kind, LexemeKind::QuotedIdentifier { quote: b'`' });
        assert_eq!(decode_doubled(source, tokens[4]), Some("c`d".to_owned()));
        assert_eq!(tokens[6].kind, LexemeKind::EscapeString);
    }

    #[test]
    fn dollar_quotes_obey_tags_adjacency_and_high_bit_policy() {
        let source = "$$ SELECT $$ $tag$ JOIN $tag$ b$tag$qux $1";
        let tokens = lex(source).unwrap();
        assert_eq!(tokens[0].kind, LexemeKind::DollarString);
        assert_eq!(tokens[2].kind, LexemeKind::DollarString);
        assert!(
            tokens
                .iter()
                .any(|token| token.text(source) == Some("b$tag$qux")
                    && token.kind == LexemeKind::Word)
        );
        assert!(
            tokens
                .iter()
                .any(|token| token.text(source) == Some("$") && token.kind == LexemeKind::Symbol)
        );
        assert!(lex("$tag$ unterminated").is_none());
        assert!(lex("$é$ body $é$").is_none());
        assert!(lex("é$tag$body").is_none());
    }

    #[test]
    fn high_bit_unquoted_identifiers_fail_closed_before_keyword_projection() {
        assert!(lex("éSELECT").is_none());
        assert!(lex("prefixéFROM suffix").is_none());
        assert!(lex("SELECT éWHERE FROM t").is_none());
        assert!(lex("SELECT 'éFROM', \"éWHERE\", $$éSELECT$$").is_some());
    }

    #[test]
    fn calcite_rendered_identifier_components_are_closed_and_do_not_change_lexing() {
        for value in ["name", "_name", "列", "列1$x"] {
            assert!(calcite_rendered_identifier_component(value), "{value:?}");
        }
        for value in ["", "1列", "$列", "列.名", "列 名"] {
            assert!(!calcite_rendered_identifier_component(value), "{value:?}");
        }
        assert!(lex("列").is_none());
    }

    #[test]
    fn numbers_operators_and_depths_are_exact() {
        let source = "f(.5, 1.2e-3)<=g(1foo)::numeric";
        let tokens = lex(source).unwrap();
        assert!(
            tokens
                .iter()
                .any(|token| token.text(source) == Some(".5") && token.kind == LexemeKind::Number)
        );
        assert!(
            tokens
                .iter()
                .any(|token| token.text(source) == Some("1.2e-3")
                    && token.kind == LexemeKind::Number)
        );
        assert!(tokens.iter().any(|token| token.text(source) == Some("1foo")
            && token.kind == LexemeKind::Number));
        assert!(tokens.iter().any(|token| token.text(source) == Some("<=")
            && token.kind == LexemeKind::Operator));
        assert!(tokens.iter().any(|token| token.text(source) == Some("::")
            && token.kind == LexemeKind::Operator));
        let depths = parenthesis_depths(source, &tokens).unwrap();
        for (token, depth) in tokens.iter().zip(depths) {
            if token.is_symbol(source, "(") || token.is_symbol(source, ")") {
                assert_eq!(depth, 0);
            }
        }
        assert!(parenthesis_depths("(", &lex("(").unwrap()).is_none());
        assert!(grouping_depths("([)]", &lex("([)]").unwrap()).is_none());
    }
}
