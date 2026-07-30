use std::path::{Path, PathBuf};

use logos_ir::SqlIrFrontend;
use logos_ir::integrity::{SchemaIntegrityContract, load_adjacent_integrity_contract};
use logos_ir::ir::{Query, Schema, SqlEnvironment};
use serde::Serialize;

use crate::error::{Error, Result};

#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct VerificationInput {
    pub sql_environment: SqlEnvironment,
    pub integrity_contract: SchemaIntegrityContract,
    schema: SchemaInput,
    source_query: QueryInput,
    target_query: QueryInput,
}

#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SchemaInput {
    pub path: PathBuf,
    pub sql: String,
}

#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct QueryInput {
    pub path: PathBuf,
    pub sql: String,
}

#[derive(Debug, Clone)]
pub struct VerificationIr {
    pub(super) sql_environment: SqlEnvironment,
    pub(super) schema: Schema,
    pub(super) source_program: Vec<Query>,
    pub(super) target_program: Vec<Query>,
}

impl VerificationInput {
    pub fn read_with_environment(
        schema: PathBuf,
        source: PathBuf,
        target: PathBuf,
        sql_environment: SqlEnvironment,
    ) -> Result<Self> {
        let schema_sql = read_to_string(&schema)?;
        let source_sql = read_to_string(&source)?;
        let target_sql = read_to_string(&target)?;
        let integrity_contract = load_adjacent_integrity_contract(&schema)?;

        Ok(Self {
            sql_environment,
            integrity_contract,
            schema: SchemaInput {
                path: schema,
                sql: schema_sql,
            },
            source_query: QueryInput {
                path: source,
                sql: source_sql,
            },
            target_query: QueryInput {
                path: target,
                sql: target_sql,
            },
        })
    }

    pub fn load_ir(&self, ir_frontend: &dyn SqlIrFrontend) -> Result<VerificationIr> {
        // Load the target first so a terminal target syntax error is not
        // hidden by an unrelated conservative source-conversion rejection.
        // This changes only error precedence when both programs are invalid:
        // no IR is returned after either failure, and a parseable target still
        // proceeds to the unchanged fail-closed source conversion below.
        let mut target_ir = ir_frontend.load_sql(&self.schema.path, &self.target_query.path)?;
        let mut source_ir = ir_frontend.load_sql(&self.schema.path, &self.source_query.path)?;
        if source_ir.environment != self.sql_environment {
            return Err(Error::InvalidLogosIrInput(format!(
                "source Calcite import attested SQL environment {:?}, expected {:?}",
                source_ir.environment, self.sql_environment
            )));
        }
        if target_ir.environment != self.sql_environment {
            return Err(Error::InvalidLogosIrInput(format!(
                "target Calcite import attested SQL environment {:?}, expected {:?}",
                target_ir.environment, self.sql_environment
            )));
        }
        let source_program = take_query_program(&self.source_query.path, &mut source_ir)?;
        let target_program = take_query_program(&self.target_query.path, &mut target_ir)?;
        bind_query_program_to_sql(
            &self.source_query.path,
            &self.source_query.sql,
            &source_program,
        )?;
        bind_query_program_to_sql(
            &self.target_query.path,
            &self.target_query.sql,
            &target_program,
        )?;

        if source_ir.schema != target_ir.schema {
            return Err(Error::InvalidLogosIrInput(
                "source and target Calcite imports produced different schemas".to_owned(),
            ));
        }

        let mut schema = source_ir.schema;
        self.integrity_contract.merge_into_schema(&mut schema)?;

        Ok(VerificationIr {
            sql_environment: self.sql_environment,
            schema,
            source_program,
            target_program,
        })
    }

    /// Resolve parser-facing DDL declarations into the same immutable
    /// benchmark contract used by metadata-only declarations.  The caller
    /// supplies a trivial query path so schema hydration remains independent
    /// of source/target query support and cannot change counterexample-search
    /// semantics.
    pub fn hydrate_integrity_contract(
        &mut self,
        ir_frontend: &dyn SqlIrFrontend,
        schema_probe_query: &Path,
    ) -> Result<()> {
        if self.integrity_contract.case_id.is_none() {
            return self.ensure_integrity_environment();
        }
        let schema_ir = ir_frontend.load_sql(&self.schema.path, schema_probe_query)?;
        if schema_ir.environment != self.sql_environment {
            return Err(Error::InvalidLogosIrInput(format!(
                "schema probe attested SQL environment {:?}, expected {:?}",
                schema_ir.environment, self.sql_environment
            )));
        }
        self.integrity_contract = self
            .integrity_contract
            .merged_with_schema(&schema_ir.schema)?;
        self.ensure_integrity_environment()
    }

    /// Fail closed before any consumer uses string-valued integrity
    /// semantics under an environment weaker than the one modeled by the
    /// reusable FormalSQL contract.
    pub fn ensure_integrity_environment(&self) -> Result<()> {
        if self
            .integrity_contract
            .requires_postgres_utf8_c_text_semantics
            && !self.sql_environment.has_postgres_utf8_c_text_semantics()
        {
            return Err(Error::InvalidSqlEnvironment(format!(
                "benchmark integrity contract {} uses PostgreSQL text equality or collation semantics and requires LC_COLLATE=C, LC_CTYPE=C, locale provider libc, and server encoding UTF8; received LC_COLLATE={}, LC_CTYPE={}, locale provider {}, and server encoding {}",
                self.integrity_contract
                    .case_id
                    .as_deref()
                    .unwrap_or("<unknown>"),
                self.sql_environment.default_collation_label(),
                self.sql_environment.character_classification_label(),
                self.sql_environment.locale_provider_label(),
                self.sql_environment.server_encoding_label(),
            )));
        }
        Ok(())
    }

    pub fn schema_sql(&self) -> &str {
        &self.schema.sql
    }

    pub fn source_sql(&self) -> &str {
        &self.source_query.sql
    }

    pub fn target_sql(&self) -> &str {
        &self.target_query.sql
    }

    pub fn integrity_contract(&self) -> &SchemaIntegrityContract {
        &self.integrity_contract
    }

    pub fn integrity_contract_summary(&self) -> String {
        self.integrity_contract.human_readable()
    }

    pub(crate) fn source_sql_program(&self) -> Result<Vec<&str>> {
        split_input_query_program(&self.source_query.path, &self.source_query.sql)
    }

    pub(crate) fn target_sql_program(&self) -> Result<Vec<&str>> {
        split_input_query_program(&self.target_query.path, &self.target_query.sql)
    }

    pub fn stable_cache_key(&self) -> String {
        let mut hash = Fnv64::new();
        hash.write("logos-solver-verification-input-v4-query-program-environment");
        hash.write(self.sql_environment.default_collation_label());
        hash.write(self.sql_environment.character_classification_label());
        hash.write(self.sql_environment.locale_provider_label());
        hash.write(self.sql_environment.server_encoding_label());
        hash.write(self.schema_sql());
        hash.write(
            &serde_json::to_string(&self.integrity_contract)
                .expect("validated integrity contract must serialize"),
        );
        hash.write(self.source_sql());
        hash.write(self.target_sql());
        format!("{:016x}", hash.finish())
    }
}

impl VerificationIr {
    pub fn sql_environment(&self) -> SqlEnvironment {
        self.sql_environment
    }

    pub fn schema_ir(&self) -> &Schema {
        &self.schema
    }

    pub fn source_program_ir(&self) -> &[Query] {
        &self.source_program
    }

    pub fn target_program_ir(&self) -> &[Query] {
        &self.target_program
    }
}

struct Fnv64 {
    state: u64,
}

impl Fnv64 {
    fn new() -> Self {
        Self {
            state: 0xcbf29ce484222325,
        }
    }

    fn write(&mut self, value: &str) {
        for byte in value.as_bytes() {
            self.state ^= u64::from(*byte);
            self.state = self.state.wrapping_mul(0x100000001b3);
        }
        self.state ^= 0xff;
        self.state = self.state.wrapping_mul(0x100000001b3);
    }

    fn finish(self) -> u64 {
        self.state
    }
}

fn take_query_program(path: &Path, ir: &mut logos_ir::ir::LogosIrFile) -> Result<Vec<Query>> {
    if ir.queries.is_empty() {
        return Err(Error::InvalidLogosIrInput(format!(
            "{} must produce a nonempty ordered Logos IR query program",
            path.display()
        )));
    }
    Ok(std::mem::take(&mut ir.queries))
}

fn bind_query_program_to_sql(path: &Path, sql: &str, program: &[Query]) -> Result<()> {
    let statements = split_input_query_program(path, sql)?;
    if statements.len() != program.len() {
        return Err(Error::InvalidLogosIrInput(format!(
            "{} contains {} PostgreSQL SQL statement(s), but the frontend returned {} query IR statement(s)",
            path.display(),
            statements.len(),
            program.len()
        )));
    }

    for (index, (statement, query)) in statements.iter().zip(program).enumerate() {
        let Some(frontend_sql) = query.source_sql.as_deref() else {
            return Err(Error::InvalidLogosIrInput(format!(
                "frontend query IR statement {} for {} is missing sourceSql",
                index + 1,
                path.display()
            )));
        };
        if *statement == frontend_sql {
            continue;
        }

        let actual_tokens = postgres_binding_tokens(statement).map_err(|message| {
            Error::InvalidLogosIrInput(format!(
                "cannot tokenize PostgreSQL SQL statement {} in {}: {message}",
                index + 1,
                path.display()
            ))
        })?;
        let frontend_tokens = postgres_binding_tokens(frontend_sql).map_err(|message| {
            Error::InvalidLogosIrInput(format!(
                "cannot tokenize frontend sourceSql for statement {} in {}: {message}",
                index + 1,
                path.display()
            ))
        })?;
        if binding_token_sequences_equal(&actual_tokens, &frontend_tokens) {
            continue;
        }

        let difference = first_binding_token_difference(&actual_tokens, &frontend_tokens);
        return Err(Error::InvalidLogosIrInput(format!(
            "frontend sourceSql for statement {} in {} does not match the input program ({difference})",
            index + 1,
            path.display()
        )));
    }
    Ok(())
}

fn split_input_query_program<'a>(path: &Path, sql: &'a str) -> Result<Vec<&'a str>> {
    let statements = split_postgres_query_program(sql).map_err(|message| {
        Error::InvalidLogosIrInput(format!(
            "cannot split the PostgreSQL query program {}: {message}",
            path.display()
        ))
    })?;
    if statements.is_empty() {
        return Err(Error::InvalidLogosIrInput(format!(
            "{} must contain a nonempty PostgreSQL query program",
            path.display()
        )));
    }
    Ok(statements)
}

/// Split a PostgreSQL query file exactly where the Calcite wrapper can split
/// it: semicolons outside protected tokens and comments delimit statements,
/// the six PostgreSQL SQL whitespace bytes are trimmed, and comment-only
/// fragments are omitted. The returned slices still point into the exact
/// program text, so the frontend cannot substitute a different statement.
fn split_postgres_query_program(sql: &str) -> std::result::Result<Vec<&str>, String> {
    let bytes = sql.as_bytes();
    let mut statements = Vec::new();
    let mut start = 0;
    let mut index = 0;
    while index < bytes.len() {
        match (bytes[index], bytes.get(index + 1).copied()) {
            (b'-', Some(b'-')) => index = postgres_line_comment_end(bytes, index + 2),
            (b'/', Some(b'*')) => index = postgres_block_comment_end(bytes, index)?,
            (quote @ (b'\'' | b'"' | b'`'), _) => {
                index = postgres_quoted_token_end(bytes, index, quote)?;
            }
            (b'[', _) => index = postgres_bracket_quoted_token_end(bytes, index)?,
            (b'$', _) => {
                if let Some(delimiter_end) = postgres_dollar_quote_delimiter_end(bytes, index)? {
                    index = postgres_dollar_quoted_token_end(bytes, index, delimiter_end)?;
                } else {
                    index += 1;
                }
            }
            (b';', _) => {
                add_postgres_query_slice(sql, start, index, &mut statements)?;
                index += 1;
                start = index;
            }
            _ => index += 1,
        }
    }
    add_postgres_query_slice(sql, start, bytes.len(), &mut statements)?;
    Ok(statements)
}

fn add_postgres_query_slice<'a>(
    sql: &'a str,
    start: usize,
    end: usize,
    statements: &mut Vec<&'a str>,
) -> std::result::Result<(), String> {
    let statement = trim_postgres_sql_whitespace(&sql[start..end]);
    if !statement.is_empty() && contains_postgres_sql_token(statement)? {
        statements.push(statement);
    }
    Ok(())
}

fn trim_postgres_sql_whitespace(value: &str) -> &str {
    value.trim_matches(|value: char| value.is_ascii() && is_postgres_sql_whitespace(value as u8))
}

fn is_postgres_sql_whitespace(value: u8) -> bool {
    matches!(value, b' ' | b'\t' | b'\n' | b'\r' | 0x0c | 0x0b)
}

fn contains_postgres_sql_token(sql: &str) -> std::result::Result<bool, String> {
    let bytes = sql.as_bytes();
    let mut index = 0;
    while index < bytes.len() {
        match (bytes[index], bytes.get(index + 1).copied()) {
            (byte, _) if is_postgres_sql_whitespace(byte) => index += 1,
            (b'-', Some(b'-')) => index = postgres_line_comment_end(bytes, index + 2),
            (b'/', Some(b'*')) => index = postgres_block_comment_end(bytes, index)?,
            _ => return Ok(true),
        }
    }
    Ok(false)
}

fn postgres_line_comment_end(sql: &[u8], mut index: usize) -> usize {
    while index < sql.len() && !matches!(sql[index], b'\n' | b'\r') {
        index += 1;
    }
    index
}

fn postgres_block_comment_end(sql: &[u8], mut index: usize) -> std::result::Result<usize, String> {
    let mut depth = 1usize;
    index += 2;
    while index < sql.len() {
        match (sql[index], sql.get(index + 1).copied()) {
            (b'/', Some(b'*')) => {
                depth = depth
                    .checked_add(1)
                    .ok_or_else(|| "PostgreSQL block comment nesting is too deep".to_owned())?;
                index += 2;
            }
            (b'*', Some(b'/')) => {
                depth -= 1;
                index += 2;
                if depth == 0 {
                    return Ok(index);
                }
            }
            _ => index += 1,
        }
    }
    Err("unterminated block comment in SQL query file".to_owned())
}

fn postgres_quoted_token_end(
    sql: &[u8],
    start: usize,
    quote: u8,
) -> std::result::Result<usize, String> {
    let mut index = start + 1;
    let backslash_escapes = quote == b'\'' && postgres_escape_string_quote(sql, start);
    while index < sql.len() {
        let current = sql[index];
        index += 1;
        if current == b'\\' && backslash_escapes && index < sql.len() {
            index += 1;
        } else if current == quote {
            if index < sql.len() && sql[index] == quote {
                index += 1;
            } else {
                return Ok(index);
            }
        }
    }
    Err("unterminated quoted token in SQL query file".to_owned())
}

fn postgres_escape_string_quote(sql: &[u8], quote_start: usize) -> bool {
    if quote_start == 0 || !matches!(sql[quote_start - 1], b'E' | b'e') {
        return false;
    }
    quote_start == 1
        || (!is_postgres_bare_identifier_part(sql[quote_start - 2])
            && sql[quote_start - 2].is_ascii())
}

fn postgres_bracket_quoted_token_end(
    sql: &[u8],
    start: usize,
) -> std::result::Result<usize, String> {
    let mut index = start + 1;
    while index < sql.len() {
        if sql[index] == b']' {
            index += 1;
            if index < sql.len() && sql[index] == b']' {
                index += 1;
            } else {
                return Ok(index);
            }
        } else {
            index += 1;
        }
    }
    Err("unterminated bracket-quoted identifier in SQL query file".to_owned())
}

fn postgres_dollar_quote_delimiter_end(
    sql: &[u8],
    start: usize,
) -> std::result::Result<Option<usize>, String> {
    if start > 0 && (is_postgres_bare_identifier_part(sql[start - 1]) || !sql[start - 1].is_ascii())
    {
        return Ok(None);
    }
    let mut index = start + 1;
    if index < sql.len() && !sql[index].is_ascii() {
        return Err("non-ASCII PostgreSQL dollar-quote tags are not supported".to_owned());
    }
    if index < sql.len() && sql[index] == b'$' {
        return Ok(Some(index + 1));
    }
    if index >= sql.len() || !is_postgres_bare_identifier_start(sql[index]) {
        return Ok(None);
    }
    index += 1;
    while index < sql.len()
        && (is_postgres_bare_identifier_start(sql[index]) || sql[index].is_ascii_digit())
    {
        index += 1;
    }
    if index < sql.len() && !sql[index].is_ascii() {
        return Err("non-ASCII PostgreSQL dollar-quote tags are not supported".to_owned());
    }
    Ok((index < sql.len() && sql[index] == b'$').then_some(index + 1))
}

fn postgres_dollar_quoted_token_end(
    sql: &[u8],
    start: usize,
    delimiter_end: usize,
) -> std::result::Result<usize, String> {
    let delimiter = &sql[start..delimiter_end];
    let Some(close_offset) = sql[delimiter_end..]
        .windows(delimiter.len())
        .position(|candidate| candidate == delimiter)
    else {
        return Err("unterminated dollar-quoted SQL string".to_owned());
    };
    Ok(delimiter_end + close_offset + delimiter.len())
}

fn is_postgres_bare_identifier_start(value: u8) -> bool {
    value.is_ascii_alphabetic() || value == b'_'
}

fn is_postgres_bare_identifier_part(value: u8) -> bool {
    is_postgres_bare_identifier_start(value) || value.is_ascii_digit() || value == b'$'
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum SqlBindingToken {
    BareWord(String),
    QuotedIdentifier(String),
    Protected(String),
    Number(String),
    Symbol(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg(test)]
pub(crate) enum PostgresStructureToken {
    Word(String),
    LeftParen,
    RightParen,
}

/// Reuse the source-identity tokenizer for consumers that need only words and
/// parenthesis structure. This keeps PostgreSQL comments and protected-token
/// boundaries, including the distinction between ordinary and E/e strings,
/// authoritative in one lexer.
#[cfg(test)]
pub(crate) fn postgres_structure_tokens(
    sql: &str,
) -> std::result::Result<Vec<PostgresStructureToken>, String> {
    postgres_binding_tokens(sql).map(|tokens| {
        tokens
            .into_iter()
            .filter_map(|token| match token {
                SqlBindingToken::BareWord(word) => Some(PostgresStructureToken::Word(word)),
                SqlBindingToken::Symbol(symbol) if symbol == "(" => {
                    Some(PostgresStructureToken::LeftParen)
                }
                SqlBindingToken::Symbol(symbol) if symbol == ")" => {
                    Some(PostgresStructureToken::RightParen)
                }
                _ => None,
            })
            .collect()
    })
}

/// Tokenize only for source-program identity. This is intentionally much
/// narrower than SQL parsing: formatting and comments disappear, unquoted
/// words receive PostgreSQL's ASCII case fold, while literal and operator
/// spellings remain opaque and exact.
fn postgres_binding_tokens(sql: &str) -> std::result::Result<Vec<SqlBindingToken>, String> {
    let sql = trim_postgres_sql_whitespace(sql);
    let bytes = sql.as_bytes();
    let mut tokens = Vec::new();
    let mut index = 0;
    while index < bytes.len() {
        match (bytes[index], bytes.get(index + 1).copied()) {
            (byte, _) if is_postgres_sql_whitespace(byte) => index += 1,
            (b'-', Some(b'-')) => index = postgres_line_comment_end(bytes, index + 2),
            (b'/', Some(b'*')) => index = postgres_block_comment_end(bytes, index)?,
            (b'"', _) => {
                let end = postgres_quoted_token_end(bytes, index, b'"')?;
                tokens.push(SqlBindingToken::QuotedIdentifier(
                    decode_postgres_quoted_identifier(&sql[index + 1..end - 1]),
                ));
                index = end;
            }
            (quote @ (b'\'' | b'`'), _) => {
                let end = postgres_quoted_token_end(bytes, index, quote)?;
                tokens.push(SqlBindingToken::Protected(sql[index..end].to_owned()));
                index = end;
            }
            (b'[', _) => {
                let end = postgres_bracket_quoted_token_end(bytes, index)?;
                tokens.push(SqlBindingToken::Protected(sql[index..end].to_owned()));
                index = end;
            }
            (b'$', _) => {
                if let Some(delimiter_end) = postgres_dollar_quote_delimiter_end(bytes, index)? {
                    let end = postgres_dollar_quoted_token_end(bytes, index, delimiter_end)?;
                    tokens.push(SqlBindingToken::Protected(sql[index..end].to_owned()));
                    index = end;
                } else if bytes.get(index + 1).is_some_and(u8::is_ascii_digit) {
                    let end = scan_postgres_parameter(bytes, index);
                    tokens.push(SqlBindingToken::Protected(sql[index..end].to_owned()));
                    index = end;
                } else {
                    tokens.push(SqlBindingToken::Symbol("$".to_owned()));
                    index += 1;
                }
            }
            (byte, _) if is_postgres_bare_identifier_start(byte) => {
                let end = scan_postgres_bare_word(bytes, index);
                // E'...' is one PostgreSQL string token. Keeping the complete
                // spelling opaque prevents a normal string from being treated
                // as equivalent to one with backslash escape semantics.
                if end == index + 1 && matches!(byte, b'E' | b'e') && bytes.get(end) == Some(&b'\'')
                {
                    let quote_end = postgres_quoted_token_end(bytes, end, b'\'')?;
                    tokens.push(SqlBindingToken::Protected(sql[index..quote_end].to_owned()));
                    index = quote_end;
                } else {
                    tokens.push(SqlBindingToken::BareWord(
                        sql[index..end].to_ascii_lowercase(),
                    ));
                    index = end;
                }
            }
            (byte, _) if byte.is_ascii_digit() => {
                let end = scan_postgres_number(bytes, index);
                tokens.push(SqlBindingToken::Number(sql[index..end].to_owned()));
                index = end;
            }
            (b'.', Some(next)) if next.is_ascii_digit() => {
                let end = scan_postgres_number(bytes, index);
                tokens.push(SqlBindingToken::Number(sql[index..end].to_owned()));
                index = end;
            }
            (byte, _) if is_postgres_operator_byte(byte) => {
                let mut end = index + 1;
                while end < bytes.len() && is_postgres_operator_byte(bytes[end]) {
                    end += 1;
                }
                tokens.push(SqlBindingToken::Symbol(sql[index..end].to_owned()));
                index = end;
            }
            (_, _) => {
                let end = next_utf8_boundary(sql, index);
                tokens.push(SqlBindingToken::Symbol(sql[index..end].to_owned()));
                index = end;
            }
        }
    }
    if matches!(tokens.last(), Some(SqlBindingToken::Symbol(symbol)) if symbol == ";") {
        tokens.pop();
    }
    Ok(tokens)
}

fn decode_postgres_quoted_identifier(value: &str) -> String {
    value.replace("\"\"", "\"")
}

fn scan_postgres_bare_word(sql: &[u8], mut index: usize) -> usize {
    index += 1;
    while index < sql.len() && is_postgres_bare_identifier_part(sql[index]) {
        index += 1;
    }
    index
}

fn scan_postgres_parameter(sql: &[u8], mut index: usize) -> usize {
    index += 1;
    while index < sql.len() && sql[index].is_ascii_digit() {
        index += 1;
    }
    index
}

fn scan_postgres_number(sql: &[u8], start: usize) -> usize {
    let mut index = start;
    if sql[index] == b'.' {
        index += 1;
        while index < sql.len() && (sql[index].is_ascii_digit() || sql[index] == b'_') {
            index += 1;
        }
    } else if index + 2 <= sql.len()
        && sql[index] == b'0'
        && index + 1 < sql.len()
        && matches!(sql[index + 1], b'x' | b'X' | b'o' | b'O' | b'b' | b'B')
    {
        index += 2;
        while index < sql.len() && (sql[index].is_ascii_alphanumeric() || sql[index] == b'_') {
            index += 1;
        }
        return index;
    } else {
        while index < sql.len() && (sql[index].is_ascii_digit() || sql[index] == b'_') {
            index += 1;
        }
        if index < sql.len() && sql[index] == b'.' {
            index += 1;
            while index < sql.len() && (sql[index].is_ascii_digit() || sql[index] == b'_') {
                index += 1;
            }
        }
    }
    if index < sql.len() && matches!(sql[index], b'e' | b'E') {
        let exponent = index;
        index += 1;
        if index < sql.len() && matches!(sql[index], b'+' | b'-') {
            index += 1;
        }
        let digits = index;
        while index < sql.len() && (sql[index].is_ascii_digit() || sql[index] == b'_') {
            index += 1;
        }
        if index == digits {
            index = exponent;
        }
    }
    // Keep malformed number/identifier adjacency opaque rather than making
    // it equal to the valid, whitespace-separated token sequence.
    while index < sql.len() && is_postgres_bare_identifier_part(sql[index]) {
        index += 1;
    }
    index
}

fn is_postgres_operator_byte(value: u8) -> bool {
    matches!(
        value,
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
            | b'`'
            | b'?'
            | b':'
    )
}

fn next_utf8_boundary(sql: &str, index: usize) -> usize {
    index + sql[index..].chars().next().map_or(1, char::len_utf8)
}

fn binding_token_sequences_equal(actual: &[SqlBindingToken], frontend: &[SqlBindingToken]) -> bool {
    let actual = canonicalize_postgres_date_string_constants(actual);
    let frontend = canonicalize_postgres_date_string_constants(frontend);
    let actual = canonicalize_qualified_is_not_null(&actual);
    let frontend = canonicalize_qualified_is_not_null(&frontend);
    if actual.len() != frontend.len() {
        return false;
    }
    let substring_separators = postgres_substring_separator_rewrites(&actual, &frontend);
    let integer_cast_aliases = postgres_cast_integer_alias_rewrites(&actual, &frontend);
    (0..actual.len()).all(|index| {
        binding_tokens_equal_at(&actual, &frontend, index)
            || substring_separators[index]
            || integer_cast_aliases[index]
    })
}

/// SQLGlot renders `qualified.column IS NOT NULL` as the PostgreSQL-equivalent
/// `NOT qualified.column IS NULL`. Admit only that closed six-token rewrite
/// over one direct qualified identifier. Parenthesized or computed operands,
/// other IS predicates, and unqualified expressions remain observable.
fn canonicalize_qualified_is_not_null(tokens: &[SqlBindingToken]) -> Vec<SqlBindingToken> {
    let mut canonical = Vec::with_capacity(tokens.len());
    let mut index = 0usize;
    while index < tokens.len() {
        let prefix_not = matches!(
            tokens.get(index),
            Some(SqlBindingToken::BareWord(word)) if word == "not"
        );
        let qualifier = index + if prefix_not { 1 } else { 0 };
        let qualified_operand = binding_identifier(tokens.get(qualifier))
            && binding_symbol(tokens.get(qualifier + 1), ".")
            && binding_identifier(tokens.get(qualifier + 2));
        let suffix = qualifier + 3;
        let is_null = matches!(
            tokens.get(suffix),
            Some(SqlBindingToken::BareWord(word)) if word == "is"
        ) && matches!(
            tokens.get(suffix + 1),
            Some(SqlBindingToken::BareWord(word)) if word == "null"
        );
        let is_not_null = matches!(
            tokens.get(suffix),
            Some(SqlBindingToken::BareWord(word)) if word == "is"
        ) && matches!(
            tokens.get(suffix + 1),
            Some(SqlBindingToken::BareWord(word)) if word == "not"
        ) && matches!(
            tokens.get(suffix + 2),
            Some(SqlBindingToken::BareWord(word)) if word == "null"
        );

        if qualified_operand && ((prefix_not && is_null) || (!prefix_not && is_not_null)) {
            canonical.extend_from_slice(&tokens[qualifier..qualifier + 3]);
            canonical.push(SqlBindingToken::BareWord("is".to_owned()));
            canonical.push(SqlBindingToken::BareWord("not".to_owned()));
            canonical.push(SqlBindingToken::BareWord("null".to_owned()));
            index = if prefix_not { suffix + 2 } else { suffix + 3 };
        } else {
            canonical.push(tokens[index].clone());
            index += 1;
        }
    }
    canonical
}

fn binding_identifier(token: Option<&SqlBindingToken>) -> bool {
    matches!(
        token,
        Some(SqlBindingToken::BareWord(_) | SqlBindingToken::QuotedIdentifier(_))
    )
}

/// PostgreSQL defines `INT` as an exact spelling alias for `INTEGER` in a
/// CAST target, while SQLGlot can exchange those spellings during rendering.
/// Admit only the differing target position in a paired, unqualified
/// `CAST(expression AS INTEGER|INT)` with one bare type token.  A column or
/// alias named `integer`, a quoted or qualified type, array/modifier syntax,
/// and every other type spelling remain token-observable.
fn postgres_cast_integer_alias_rewrites(
    actual: &[SqlBindingToken],
    frontend: &[SqlBindingToken],
) -> Vec<bool> {
    let mut allowed = vec![false; actual.len()];
    for start in 0..actual.len() {
        let (Some(actual_type), Some(frontend_type)) = (
            direct_postgres_cast_integer_target(actual, start),
            direct_postgres_cast_integer_target(frontend, start),
        ) else {
            continue;
        };
        if actual_type != frontend_type {
            continue;
        }
        let pair = (actual.get(actual_type), frontend.get(frontend_type));
        if matches!(
            pair,
            (
                Some(SqlBindingToken::BareWord(left)),
                Some(SqlBindingToken::BareWord(right))
            ) if matches!((left.as_str(), right.as_str()), ("integer", "int") | ("int", "integer"))
        ) {
            allowed[actual_type] = true;
        }
    }
    allowed
}

fn direct_postgres_cast_integer_target(tokens: &[SqlBindingToken], start: usize) -> Option<usize> {
    if !matches!(tokens.get(start), Some(SqlBindingToken::BareWord(word)) if word == "cast")
        || start
            .checked_sub(1)
            .is_some_and(|previous| binding_symbol(tokens.get(previous), "."))
    {
        return None;
    }
    let open = start.checked_add(1)?;
    let close = matching_binding_parenthesis(tokens, open)?;
    let mut depth = 0usize;
    let mut direct_as = None;
    for index in open.checked_add(1)?..close {
        match tokens.get(index)? {
            SqlBindingToken::Symbol(symbol) if symbol == "(" => {
                depth = depth.checked_add(1)?;
            }
            SqlBindingToken::Symbol(symbol) if symbol == ")" => {
                depth = depth.checked_sub(1)?;
            }
            SqlBindingToken::BareWord(word) if depth == 0 && word == "as" => {
                if direct_as.replace(index).is_some() {
                    return None;
                }
            }
            _ => {}
        }
    }
    let direct_as = direct_as?;
    if direct_as == open.checked_add(1)? {
        return None;
    }
    let type_index = direct_as.checked_add(1)?;
    if type_index.checked_add(1)? != close
        || !matches!(tokens.get(type_index), Some(SqlBindingToken::BareWord(word)) if matches!(word.as_str(), "int" | "integer"))
    {
        return None;
    }
    Some(type_index)
}

/// PostgreSQL documents `DATE 'string'` and `CAST('string' AS DATE)` as two
/// spellings of the same typed constant: both pass the identical string text
/// to the DATE input conversion routine.  SQLGlot exchanges these spellings.
/// Canonicalize only that closed six-token CAST with one protected string
/// literal; casts of expressions, other types, qualified/quoted names, and
/// malformed or extended type syntax remain byte-token observable.
fn canonicalize_postgres_date_string_constants(tokens: &[SqlBindingToken]) -> Vec<SqlBindingToken> {
    let mut canonical = Vec::with_capacity(tokens.len());
    let mut index = 0usize;
    while index < tokens.len() {
        let exact_date_cast = matches!(tokens.get(index), Some(SqlBindingToken::BareWord(word)) if word == "cast")
            && binding_symbol(tokens.get(index + 1), "(")
            && postgres_protected_string_constant(tokens.get(index + 2))
            && matches!(tokens.get(index + 3), Some(SqlBindingToken::BareWord(word)) if word == "as")
            && matches!(tokens.get(index + 4), Some(SqlBindingToken::BareWord(word)) if word == "date")
            && binding_symbol(tokens.get(index + 5), ")")
            && index
                .checked_sub(1)
                .is_none_or(|previous| !binding_symbol(tokens.get(previous), "."));
        if exact_date_cast {
            canonical.push(SqlBindingToken::BareWord("date".to_owned()));
            canonical.push(tokens[index + 2].clone());
            index += 6;
        } else {
            canonical.push(tokens[index].clone());
            index += 1;
        }
    }
    canonical
}

fn postgres_protected_string_constant(token: Option<&SqlBindingToken>) -> bool {
    let Some(SqlBindingToken::Protected(raw)) = token else {
        return false;
    };
    raw.starts_with('\'')
        || matches!(raw.as_bytes(), [b'E' | b'e', b'\'', ..])
        || raw.starts_with('$')
            && postgres_dollar_quote_delimiter_end(raw.as_bytes(), 0)
                .ok()
                .flatten()
                .is_some()
}

/// PostgreSQL's grammar lowers both `SUBSTRING(value FROM start FOR count)`
/// and `SUBSTRING(value, start, count)` to the same ordered three-argument
/// function call.  SQLGlot can exchange those spellings while identifying a
/// query.  Admit only that complete paired grammar shape: the bare function
/// name, balanced call extent, two direct separators, all three nonempty
/// arguments, and every other token position must remain identical under the
/// ordinary conservative identifier-quoting rules.
fn postgres_substring_separator_rewrites(
    actual: &[SqlBindingToken],
    frontend: &[SqlBindingToken],
) -> Vec<bool> {
    let mut allowed = vec![false; actual.len()];
    for start in 0..actual.len() {
        if !matches!(actual.get(start), Some(SqlBindingToken::BareWord(word)) if word == "substring")
            || !matches!(frontend.get(start), Some(SqlBindingToken::BareWord(word)) if word == "substring")
            || start.checked_sub(1).is_some_and(|previous| {
                binding_symbol(actual.get(previous), ".")
                    || binding_symbol(frontend.get(previous), ".")
            })
        {
            continue;
        }
        let Some(open) = start.checked_add(1) else {
            continue;
        };
        if !binding_symbol(actual.get(open), "(") || !binding_symbol(frontend.get(open), "(") {
            continue;
        }
        let (Some(actual_close), Some(frontend_close)) = (
            matching_binding_parenthesis(actual, open),
            matching_binding_parenthesis(frontend, open),
        ) else {
            continue;
        };
        if actual_close != frontend_close {
            continue;
        }

        let standard_then_comma = direct_standard_substring_separators(actual, open, actual_close)
            .zip(direct_comma_call_separators(frontend, open, frontend_close));
        let comma_then_standard = direct_comma_call_separators(actual, open, actual_close).zip(
            direct_standard_substring_separators(frontend, open, frontend_close),
        );
        let Some((left, right)) = standard_then_comma.or(comma_then_standard) else {
            continue;
        };
        if left == right {
            allowed[left[0]] = true;
            allowed[left[1]] = true;
        }
    }
    allowed
}

fn binding_symbol(token: Option<&SqlBindingToken>, expected: &str) -> bool {
    matches!(token, Some(SqlBindingToken::Symbol(symbol)) if symbol == expected)
}

fn matching_binding_parenthesis(tokens: &[SqlBindingToken], open: usize) -> Option<usize> {
    if !binding_symbol(tokens.get(open), "(") {
        return None;
    }
    let mut depth = 0usize;
    for (index, token) in tokens.iter().enumerate().skip(open) {
        if matches!(token, SqlBindingToken::Symbol(symbol) if symbol == "(") {
            depth = depth.checked_add(1)?;
        } else if matches!(token, SqlBindingToken::Symbol(symbol) if symbol == ")") {
            depth = depth.checked_sub(1)?;
            if depth == 0 {
                return Some(index);
            }
        }
    }
    None
}

fn direct_standard_substring_separators(
    tokens: &[SqlBindingToken],
    open: usize,
    close: usize,
) -> Option<[usize; 2]> {
    let mut depth = 0usize;
    let mut from = None;
    let mut for_ = None;
    for index in open.checked_add(1)?..close {
        match tokens.get(index)? {
            SqlBindingToken::Symbol(symbol) if symbol == "(" => {
                depth = depth.checked_add(1)?;
            }
            SqlBindingToken::Symbol(symbol) if symbol == ")" => {
                depth = depth.checked_sub(1)?;
            }
            SqlBindingToken::Symbol(symbol) if depth == 0 && symbol == "," => return None,
            SqlBindingToken::BareWord(word) if depth == 0 && word == "from" => {
                if from.replace(index).is_some() || for_.is_some() {
                    return None;
                }
            }
            SqlBindingToken::BareWord(word) if depth == 0 && word == "for" => {
                if from.is_none() || for_.replace(index).is_some() {
                    return None;
                }
            }
            _ => {}
        }
    }
    let separators = [from?, for_?];
    three_nonempty_binding_arguments(open, close, separators).then_some(separators)
}

fn direct_comma_call_separators(
    tokens: &[SqlBindingToken],
    open: usize,
    close: usize,
) -> Option<[usize; 2]> {
    let mut depth = 0usize;
    let mut separators = Vec::with_capacity(2);
    for index in open.checked_add(1)?..close {
        match tokens.get(index)? {
            SqlBindingToken::Symbol(symbol) if symbol == "(" => {
                depth = depth.checked_add(1)?;
            }
            SqlBindingToken::Symbol(symbol) if symbol == ")" => {
                depth = depth.checked_sub(1)?;
            }
            SqlBindingToken::Symbol(symbol) if depth == 0 && symbol == "," => {
                separators.push(index);
            }
            SqlBindingToken::BareWord(word)
                if depth == 0 && matches!(word.as_str(), "from" | "for") =>
            {
                return None;
            }
            _ => {}
        }
    }
    let [first, second] = separators.as_slice() else {
        return None;
    };
    let separators = [*first, *second];
    three_nonempty_binding_arguments(open, close, separators).then_some(separators)
}

fn three_nonempty_binding_arguments(open: usize, close: usize, separators: [usize; 2]) -> bool {
    open.checked_add(1)
        .is_some_and(|start| start < separators[0])
        && separators[0]
            .checked_add(1)
            .is_some_and(|start| start < separators[1])
        && separators[1]
            .checked_add(1)
            .is_some_and(|start| start < close)
}

fn binding_tokens_equal_at(
    actual: &[SqlBindingToken],
    frontend: &[SqlBindingToken],
    index: usize,
) -> bool {
    let left = &actual[index];
    let right = &frontend[index];
    if left == right {
        return true;
    }
    match (left, right) {
        (SqlBindingToken::BareWord(bare), SqlBindingToken::QuotedIdentifier(quoted))
        | (SqlBindingToken::QuotedIdentifier(quoted), SqlBindingToken::BareWord(bare)) => {
            quoted == bare
                && is_foldable_lowercase_identifier(quoted)
                && (!postgres17_keyword(bare)
                    || !postgres17_bare_schema_identifier_forbidden(bare)
                        && keyword_is_unambiguously_an_identifier(actual, index))
        }
        _ => false,
    }
}

fn is_foldable_lowercase_identifier(value: &str) -> bool {
    let bytes = value.as_bytes();
    bytes.first().is_some_and(|byte| {
        (byte.is_ascii_lowercase() || *byte == b'_')
            && bytes.iter().all(|byte| {
                byte.is_ascii_lowercase() || byte.is_ascii_digit() || matches!(*byte, b'_' | b'$')
            })
    })
}

fn keyword_is_unambiguously_an_identifier(tokens: &[SqlBindingToken], index: usize) -> bool {
    let is_dot = |token: Option<&SqlBindingToken>| matches!(token, Some(SqlBindingToken::Symbol(symbol)) if symbol == ".");
    if is_dot(
        index
            .checked_sub(1)
            .and_then(|previous| tokens.get(previous)),
    ) || is_dot(tokens.get(index + 1))
    {
        return true;
    }

    matches!(
        index
            .checked_sub(1)
            .and_then(|previous| tokens.get(previous)),
        Some(SqlBindingToken::BareWord(introducer))
            if matches!(introducer.as_str(), "from" | "join" | "into" | "update")
    ) || matches!(
        tokens.get(index + 1),
        Some(SqlBindingToken::BareWord(alias_keyword)) if alias_keyword == "as"
    )
}

const POSTGRES17_KEYWORDS: &str = "abort absent absolute access action add admin after aggregate all also alter always analyse analyze and any array as asc asensitive assertion assignment asymmetric at atomic attach attribute authorization backward before begin between bigint binary bit boolean both breadth by cache call called cascade cascaded case cast catalog chain char character characteristics check checkpoint class close cluster coalesce collate collation column columns comment comments commit committed compression concurrently conditional configuration conflict connection constraint constraints content continue conversion copy cost create cross csv cube current current_catalog current_date current_role current_schema current_time current_timestamp current_user cursor cycle data database day deallocate dec decimal declare default defaults deferrable deferred definer delete delimiter delimiters depends depth desc detach dictionary disable discard distinct do document domain double drop each else empty enable encoding encrypted end enum error escape event except exclude excluding exclusive execute exists explain expression extension external extract false family fetch filter finalize first float following for force foreign format forward freeze from full function functions generated global grant granted greatest group grouping groups handler having header hold hour identity if ilike immediate immutable implicit import in include including increment indent index indexes inherit inherits initially inline inner inout input insensitive insert instead int integer intersect interval into invoker is isnull isolation join json json_array json_arrayagg json_exists json_object json_objectagg json_query json_scalar json_serialize json_table json_value keep key keys label language large last lateral leading leakproof least left level like limit listen load local localtime localtimestamp location lock locked logged mapping match matched materialized maxvalue merge merge_action method minute minvalue mode month move name names national natural nchar nested new next nfc nfd nfkc nfkd no none normalize normalized not nothing notify notnull nowait null nullif nulls numeric object of off offset oids old omit on only operator option options or order ordinality others out outer over overlaps overlay overriding owned owner parallel parameter parser partial partition passing password path placing plan plans policy position preceding precision prepare prepared preserve primary prior privileges procedural procedure procedures program publication quote quotes range read real reassign recheck recursive ref references referencing refresh reindex relative release rename repeatable replace replica reset restart restrict return returning returns revoke right role rollback rollup routine routines row rows rule savepoint scalar schema schemas scroll search second security select sequence sequences serializable server session session_user set setof sets share show similar simple skip smallint snapshot some source sql stable standalone start statement statistics stdin stdout storage stored strict string strip subscription substring support symmetric sysid system system_user table tables tablesample tablespace target temp template temporary text then ties time timestamp to trailing transaction transform treat trigger trim true truncate trusted type types uescape unbounded uncommitted unconditional unencrypted union unique unknown unlisten unlogged until update user using vacuum valid validate validator value values varchar variadic varying verbose version view views volatile when where whitespace window with within without work wrapper write xml xmlattributes xmlconcat xmlelement xmlexists xmlforest xmlnamespaces xmlparse xmlpi xmlroot xmlserialize xmltable year yes zone";

/// PostgreSQL 17 keyword categories `R` (reserved) and `T` (reserved for type
/// or function names) are not legal bare schema-object identifiers.  A token's
/// syntactic position after `FROM` or next to `.` cannot make one of these
/// spellings equivalent to a quoted identifier.  Less restrictive keyword
/// categories remain eligible only in the independently checked identifier
/// positions below (for example PostgreSQL's legal bare relation `returns`).
const POSTGRES17_BARE_SCHEMA_IDENTIFIER_FORBIDDEN: &str = "all analyse analyze and any array as asc asymmetric authorization binary both case cast check collate collation column concurrently constraint create cross current_catalog current_date current_role current_schema current_time current_timestamp current_user default deferrable desc distinct do else end except false fetch for foreign freeze from full grant group having ilike in initially inner intersect into is isnull join lateral leading left like limit localtime localtimestamp natural not notnull null offset on only or order outer overlaps placing primary references returning right select session_user similar some symmetric system_user table tablesample then to trailing true union unique user using variadic verbose when where window with";

/// Complete PostgreSQL 17 lexer keyword set from `src/include/parser/kwlist.h`.
/// A keyword is not accepted as a quote/unquote normalization unless its
/// neighboring tokens independently put it in a qualified-name or relation
/// identifier position. This closes substitutions such as `EXISTS` to
/// `"exists"` while retaining SQLGlot's quotes around real names such as
/// `comments.name`.
fn postgres17_keyword(value: &str) -> bool {
    POSTGRES17_KEYWORDS
        .split_ascii_whitespace()
        .any(|keyword| keyword == value)
}

fn postgres17_bare_schema_identifier_forbidden(value: &str) -> bool {
    POSTGRES17_BARE_SCHEMA_IDENTIFIER_FORBIDDEN
        .split_ascii_whitespace()
        .any(|keyword| keyword == value)
}

fn first_binding_token_difference(
    actual: &[SqlBindingToken],
    frontend: &[SqlBindingToken],
) -> String {
    let index = actual
        .iter()
        .zip(frontend)
        .enumerate()
        .position(|(index, _)| !binding_tokens_equal_at(actual, frontend, index))
        .unwrap_or_else(|| actual.len().min(frontend.len()));
    format!(
        "first differing token {}: input {}, frontend {}",
        index + 1,
        binding_token_description(actual.get(index)),
        binding_token_description(frontend.get(index))
    )
}

fn binding_token_description(token: Option<&SqlBindingToken>) -> String {
    let description = token.map_or_else(
        || "<end of statement>".to_owned(),
        |token| format!("{token:?}"),
    );
    const MAX_DESCRIPTION_BYTES: usize = 160;
    if description.len() <= MAX_DESCRIPTION_BYTES {
        description
    } else {
        let mut end = MAX_DESCRIPTION_BYTES;
        while !description.is_char_boundary(end) {
            end -= 1;
        }
        format!("{}...", &description[..end])
    }
}

fn read_to_string(path: &Path) -> Result<String> {
    std::fs::read_to_string(path).map_err(|source| Error::Read {
        path: path.to_owned(),
        source,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use logos_ir::ShellSqlIrFrontend;
    use logos_ir::ir::{
        Column, LogosIrFile, RelExpr, SqlStringType, SqlType, Table, TableConstraints,
        UniqueConstraint,
    };

    #[derive(Debug, Clone)]
    struct StaticSqlIrFrontend {
        ir: LogosIrFile,
    }

    impl SqlIrFrontend for StaticSqlIrFrontend {
        fn load_sql(
            &self,
            _schema_path: &Path,
            _query_path: &Path,
        ) -> logos_ir::Result<LogosIrFile> {
            Ok(self.ir.clone())
        }
    }

    #[derive(Debug, Clone)]
    struct BothProgramsFailFrontend;

    impl SqlIrFrontend for BothProgramsFailFrontend {
        fn load_sql(
            &self,
            _schema_path: &Path,
            query_path: &Path,
        ) -> logos_ir::Result<LogosIrFile> {
            if query_path == Path::new("target.sql") {
                Err(logos_ir::Error::CalciteQueryError(
                    "target SqlParseException near ON".to_owned(),
                ))
            } else {
                Err(logos_ir::Error::InvalidScalar(
                    "source conversion rejection".to_owned(),
                ))
            }
        }
    }

    #[test]
    fn terminal_target_error_precedes_unrelated_source_conversion_error() {
        let input = VerificationInput {
            sql_environment: SqlEnvironment::default(),
            integrity_contract: SchemaIntegrityContract::default(),
            schema: SchemaInput {
                path: PathBuf::from("schema.sql"),
                sql: "create table t(id integer)".to_owned(),
            },
            source_query: QueryInput {
                path: PathBuf::from("source.sql"),
                sql: "select 'source'".to_owned(),
            },
            target_query: QueryInput {
                path: PathBuf::from("target.sql"),
                sql: "select distinct on (id) id from t".to_owned(),
            },
        };

        let error = input
            .load_ir(&BothProgramsFailFrontend)
            .expect_err("the terminal target parser error must be reported");
        assert!(matches!(
            error,
            Error::LogosIr(logos_ir::Error::CalciteQueryError(message))
                if message == "target SqlParseException near ON"
        ));
    }

    #[test]
    fn string_integrity_hydration_requires_the_complete_postgres_utf8_c_environment() {
        let partial_environment = SqlEnvironment::try_parse("C", "unspecified", "libc", "UTF8")
            .expect("construct a deliberately partial SQL environment");

        for environment in [SqlEnvironment::default(), partial_environment] {
            let mut input = verification_input("select code from t", "select code from t");
            input.sql_environment = environment;
            input.integrity_contract.case_id = Some("text-integrity-gate".to_owned());
            let frontend = StaticSqlIrFrontend {
                ir: string_unique_schema_ir(environment),
            };

            let error = input
                .hydrate_integrity_contract(&frontend, Path::new("schema-probe.sql"))
                .expect_err("unspecified or partial environments must fail during hydration");
            assert!(matches!(error, Error::InvalidSqlEnvironment(_)), "{error}");
            assert!(error.to_string().contains("LC_COLLATE=C"), "{error}");
            assert!(error.to_string().contains("LC_CTYPE=C"), "{error}");
        }

        let environment = SqlEnvironment::postgres_utf8_c();
        let mut input = verification_input("select code from t", "select code from t");
        input.sql_environment = environment;
        input.integrity_contract.case_id = Some("text-integrity-gate".to_owned());
        input
            .hydrate_integrity_contract(
                &StaticSqlIrFrontend {
                    ir: string_unique_schema_ir(environment),
                },
                Path::new("schema-probe.sql"),
            )
            .expect("the complete PostgreSQL UTF8/libc/C environment must pass the guard");
        assert!(
            input
                .integrity_contract()
                .requires_postgres_utf8_c_text_semantics
        );
    }

    #[test]
    #[ignore = "requires SQLGlot, the Java Calcite wrapper, and frozen benchmark inputs"]
    fn frozen_wetune44_preserves_distinct_on_parser_exception_for_both_frontends() {
        let repo = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(Path::parent)
            .expect("logos-solver crate should be nested under the repository root");
        let case = repo.join("benchmarks/core/.generated/sqlsolver/wetune-issues/44");
        let environment = SqlEnvironment::postgres_utf8_c();
        let input = VerificationInput::read_with_environment(
            case.join("schema.sql"),
            case.join("sql1.sql"),
            case.join("sql2.sql"),
            environment,
        )
        .expect("read frozen wetune44 input");

        for command in [
            repo.join("scripts/calcite-ir").display().to_string(),
            format!(
                "{} --read postgres --write postgres",
                repo.join("scripts/calcite-ir-sqlglot").display()
            ),
        ] {
            let frontend = ShellSqlIrFrontend::new(command.clone()).with_environment(environment);
            let error = input
                .load_ir(&frontend)
                .expect_err("DISTINCT ON must remain a terminal Calcite parser exception");
            let Error::LogosIr(logos_ir::Error::CalciteQueryError(message)) = error else {
                panic!("{command}: expected CalciteQueryError, found {error}")
            };
            assert!(
                message.contains("org.apache.calcite.sql.parser.SqlParseException"),
                "{command}: {message}"
            );
            assert!(
                message.contains("Incorrect syntax near the keyword 'ON'"),
                "{command}: {message}"
            );
            assert!(!message.contains("InvalidScalar"), "{command}: {message}");
            assert!(
                !message.contains("character literal source provenance"),
                "{command}: {message}"
            );
        }
    }

    #[test]
    fn rejects_empty_ir_query_programs() {
        let mut ir = empty_ir();
        ir.queries.clear();
        let error = take_query_program(Path::new("query.sql"), &mut ir)
            .expect_err("empty query list should fail");
        assert!(format!("{error}").contains("nonempty ordered Logos IR query program"));
    }

    #[test]
    fn rejects_comment_only_sql_query_programs() {
        let error = split_input_query_program(
            Path::new("query.sql"),
            "-- heading only;\n/* nested /* comment */ only */;",
        )
        .expect_err("a comment-only file is not a query program");

        assert!(
            error
                .to_string()
                .contains("query.sql must contain a nonempty PostgreSQL query program")
        );
    }

    #[test]
    fn preserves_every_query_in_program_order() {
        let mut ir = empty_ir();
        let mut second = ir.queries[0].clone();
        second.source_sql = Some("select 2".to_owned());
        ir.queries.push(second);

        let program = take_query_program(Path::new("query.sql"), &mut ir)
            .expect("two statements form one query program");

        assert_eq!(program.len(), 2);
        assert_eq!(program[0].source_sql.as_deref(), Some("select 1"));
        assert_eq!(program[1].source_sql.as_deref(), Some("select 2"));
        assert!(ir.queries.is_empty());
    }

    #[test]
    fn postgres_splitter_preserves_protected_text_and_omits_comment_only_statements() {
        let sql = "\u{000b}-- heading;\r\n/* outer; /* inner; */ done */\nSELECT ';' AS \"a;\", E'a\\';b', `c;``d`, [e;]]f], $tag$g;h$tag$;\n-- comment only;\n/* still; only */;\n SELECT 2\u{000c}";
        let statements = split_postgres_query_program(sql).expect("split protected SQL text");

        assert_eq!(statements.len(), 2);
        assert_eq!(
            statements[0],
            "-- heading;\r\n/* outer; /* inner; */ done */\nSELECT ';' AS \"a;\", E'a\\';b', `c;``d`, [e;]]f], $tag$g;h$tag$"
        );
        assert_eq!(statements[1], "SELECT 2");
    }

    #[test]
    fn postgres_splitter_rejects_unterminated_protected_text() {
        for (sql, expected) in [
            ("select 'unterminated", "unterminated quoted token"),
            ("select [unterminated", "unterminated bracket-quoted"),
            ("select $body$unterminated", "unterminated dollar-quoted"),
            ("select 1 /* unterminated", "unterminated block comment"),
        ] {
            let error = split_postgres_query_program(sql).expect_err("protected text must close");
            assert!(error.contains(expected), "{sql:?}: {error}");
        }
    }

    #[test]
    fn source_program_binding_accepts_only_conservative_sqlglot_lexical_changes() {
        let actual = "-- provenance comment\nselect projects.status, em.name from projects as projects where em.name <> 'ARCHIVED'; -- terminal comment";
        let frontend = "SELECT \"projects\".\"status\", \"em\".\"name\" FROM \"projects\" AS \"projects\" WHERE \"em\".\"name\" <> 'ARCHIVED';";
        let ir = ir_with_program(&[frontend]);
        bind_query_program_to_sql(Path::new("sql1.sql"), actual, &ir.queries)
            .expect("formatting and safe lowercase identifier quoting preserve the program");

        for forged in [
            "SELECT \"projects\".\"status\", \"em\".\"name\" FROM \"projects\" AS \"projects\" WHERE \"em\".\"name\" <> 'DELETED'",
            "SELECT \"projects\".\"status\", \"em\".\"name\" FROM \"projects\" AS \"projects\" WHERE \"em\".\"name\" = 'ARCHIVED'",
            "SELECT \"projects\".\"status\", \"em\".\"name\" FROM \"projects\" AS \"projects\" HAVING \"em\".\"name\" <> 'ARCHIVED'",
        ] {
            let forged_ir = ir_with_program(&[forged]);
            let error =
                bind_query_program_to_sql(Path::new("sql1.sql"), actual, &forged_ir.queries)
                    .expect_err("substantive frontend SQL changes must be rejected");
            assert!(matches!(error, Error::InvalidLogosIrInput(_)));
            assert!(format!("{error}").contains("first differing token"));
        }

        let reserved_ir = ir_with_program(&["SELECT \"current_date\""]);
        bind_query_program_to_sql(
            Path::new("sql1.sql"),
            "SELECT current_date",
            &reserved_ir.queries,
        )
        .expect_err("a reserved expression must not be reclassified as an identifier");

        let exists_ir = ir_with_program(&["SELECT \"exists\"(SELECT 1)"]);
        bind_query_program_to_sql(
            Path::new("sql1.sql"),
            "SELECT EXISTS(SELECT 1)",
            &exists_ir.queries,
        )
        .expect_err("a non-reserved grammar keyword must not be reclassified as an identifier");

        for (actual, frontend) in [
            ("SELECT * FROM \"select\"", "SELECT * FROM select"),
            ("SELECT * FROM select", "SELECT * FROM \"select\""),
            (
                "SELECT \"select\".x FROM \"select\"",
                "SELECT select.x FROM select",
            ),
        ] {
            let reserved_relation = ir_with_program(&[frontend]);
            bind_query_program_to_sql(Path::new("sql1.sql"), actual, &reserved_relation.queries)
                .expect_err(
                    "a PostgreSQL reserved word cannot become a bare relation or qualifier",
                );
        }

        let legal_nonreserved_relation = ir_with_program(&["SELECT * FROM \"returns\""]);
        bind_query_program_to_sql(
            Path::new("sql1.sql"),
            "SELECT * FROM returns",
            &legal_nonreserved_relation.queries,
        )
        .expect("PostgreSQL permits the non-reserved word returns as a bare relation name");

        let explicit_alias_relation = ir_with_program(&["SELECT * FROM users, \"comments\" AS c"]);
        bind_query_program_to_sql(
            Path::new("sql1.sql"),
            "SELECT * FROM users, comments AS c",
            &explicit_alias_relation.queries,
        )
        .expect(
            "an explicit AS proves that PostgreSQL's non-reserved comments token is an identifier",
        );

        let reserved_aliased_expression = ir_with_program(&["SELECT \"current_date\" AS d"]);
        bind_query_program_to_sql(
            Path::new("sql1.sql"),
            "SELECT current_date AS d",
            &reserved_aliased_expression.queries,
        )
        .expect_err("AS must not turn a reserved SQL expression into an identifier");
    }

    #[test]
    fn source_program_binding_closes_postgres_substring_separator_normalization() {
        for (source, frontend) in [
            (
                "SELECT substring(i_item_desc, 1, 30) FROM item",
                "SELECT SUBSTRING(\"i_item_desc\" FROM 1 FOR 30) FROM \"item\"",
            ),
            (
                "SELECT substring(i_item_desc FROM 1 FOR 30) FROM item",
                "SELECT SUBSTRING(\"i_item_desc\", 1, 30) FROM \"item\"",
            ),
            (
                "SELECT substring(substring(customer_name, 1, 10), 2, 3) FROM users",
                "SELECT SUBSTRING(SUBSTRING(\"customer_name\" FROM 1 FOR 10) FROM 2 FOR 3) FROM \"users\"",
            ),
        ] {
            bind_query_program_to_sql(
                Path::new("sql1.sql"),
                source,
                &ir_with_program(&[frontend]).queries,
            )
            .expect("the two exact PostgreSQL three-argument SUBSTRING grammars are equivalent");
        }

        let source = "SELECT substring(i_item_desc, 1, 30) FROM item";
        for forged in [
            "SELECT SUBSTRING(\"i_item_desc\" FROM 1 FOR 31) FROM \"item\"",
            "SELECT SUBSTRING(\"i_item_desc\" FROM 30 FOR 1) FROM \"item\"",
            "SELECT SUBSTRING(\"other\" FROM 1 FOR 30) FROM \"item\"",
            "SELECT SUBSTRING(\"i_item_desc\" FROM 1, 30) FROM \"item\"",
            "SELECT SUBSTRING(\"i_item_desc\", 1 FOR 30) FROM \"item\"",
            "SELECT SUBSTRING(\"i_item_desc\" FROM 1) FROM \"item\"",
            "SELECT pg_catalog.substring(\"i_item_desc\" FROM 1 FOR 30) FROM \"item\"",
            "SELECT OVERLAY(\"i_item_desc\" FROM 1 FOR 30) FROM \"item\"",
        ] {
            bind_query_program_to_sql(
                Path::new("sql1.sql"),
                source,
                &ir_with_program(&[forged]).queries,
            )
            .expect_err("near-miss SUBSTRING rewrites must not bind to the submitted program");
        }
    }

    #[test]
    fn source_program_binding_closes_postgres_date_constant_normalization() {
        for (source, frontend) in [
            (
                "SELECT date '1994-01-01'",
                "SELECT CAST('1994-01-01' AS DATE)",
            ),
            (
                "SELECT CAST('1994-01-01' AS DATE)",
                "SELECT DATE '1994-01-01'",
            ),
            (
                "SELECT date $$1994-01-01$$",
                "SELECT CAST($$1994-01-01$$ AS DATE)",
            ),
            (
                "SELECT date '1994-01-01' + (date '1995-02-03' - date '1995-02-02')",
                "SELECT CAST('1994-01-01' AS DATE) + (CAST('1995-02-03' AS DATE) - CAST('1995-02-02' AS DATE))",
            ),
        ] {
            bind_query_program_to_sql(
                Path::new("sql1.sql"),
                source,
                &ir_with_program(&[frontend]).queries,
            )
            .expect("PostgreSQL typed DATE constants and exact literal CASTs are equivalent");
        }

        let source = "SELECT date '1994-01-01'";
        for forged in [
            "SELECT CAST('1994-01-02' AS DATE)",
            "SELECT CAST('1994-01-01' AS TIMESTAMP)",
            "SELECT CAST('1994-01-01' || '' AS DATE)",
            "SELECT CAST(('1994-01-01') AS DATE)",
            "SELECT CAST('1994-01-01' AS DATE[])",
            "SELECT CAST('1994-01-01' AS \"date\")",
            "SELECT CAST($1 AS DATE)",
            "SELECT CAST(`1994-01-01` AS DATE)",
            "SELECT pg_catalog.date '1994-01-01'",
        ] {
            bind_query_program_to_sql(
                Path::new("sql1.sql"),
                source,
                &ir_with_program(&[forged]).queries,
            )
            .expect_err("near-miss DATE rewrites must not bind to the submitted program");
        }
    }

    #[test]
    fn source_program_binding_closes_postgres_cast_integer_alias_normalization() {
        for (source, frontend) in [
            (
                "SELECT CAST(value AS INTEGER) FROM measurements",
                "SELECT CAST(\"value\" AS INT) FROM \"measurements\"",
            ),
            (
                "SELECT CAST(value AS INT) FROM measurements",
                "SELECT CAST(\"value\" AS INTEGER) FROM \"measurements\"",
            ),
            (
                "SELECT CAST(CAST(value AS INTEGER) AS INTEGER) FROM measurements",
                "SELECT CAST(CAST(\"value\" AS INT) AS INT) FROM \"measurements\"",
            ),
        ] {
            bind_query_program_to_sql(
                Path::new("sql1.sql"),
                source,
                &ir_with_program(&[frontend]).queries,
            )
            .expect("PostgreSQL INT and INTEGER are exact aliases in a simple CAST target");
        }

        for (source, forged) in [
            ("SELECT integer AS answer", "SELECT int AS answer"),
            (
                "SELECT CAST(value AS INTEGER)",
                "SELECT CAST(\"value\" AS BIGINT)",
            ),
            (
                "SELECT CAST(value AS \"integer\")",
                "SELECT CAST(\"value\" AS INT)",
            ),
            (
                "SELECT CAST(value AS INTEGER[])",
                "SELECT CAST(\"value\" AS INT[])",
            ),
            ("SELECT CAST(integer AS INTEGER)", "SELECT CAST(int AS INT)"),
            (
                "SELECT types.cast(value AS INTEGER)",
                "SELECT \"types\".cast(\"value\" AS INT)",
            ),
        ] {
            bind_query_program_to_sql(
                Path::new("sql1.sql"),
                source,
                &ir_with_program(&[forged]).queries,
            )
            .expect_err("INTEGER alias normalization must remain confined to an exact CAST target");
        }
    }

    #[test]
    fn source_program_binding_closes_qualified_is_not_null_normalization() {
        for (source, frontend) in [
            (
                "SELECT t5.i IS NOT NULL FROM joined AS t5",
                "SELECT NOT \"t5\".\"i\" IS NULL FROM \"joined\" AS \"t5\"",
            ),
            (
                "SELECT NOT t5.i IS NULL FROM joined AS t5",
                "SELECT \"t5\".\"i\" IS NOT NULL FROM \"joined\" AS \"t5\"",
            ),
        ] {
            bind_query_program_to_sql(
                Path::new("sql1.sql"),
                source,
                &ir_with_program(&[frontend]).queries,
            )
            .expect("direct qualified IS NOT NULL spellings are PostgreSQL-equivalent");
        }

        let source = "SELECT t5.i IS NOT NULL FROM joined AS t5";
        for forged in [
            "SELECT \"t5\".\"i\" IS NULL FROM \"joined\" AS \"t5\"",
            "SELECT NOT \"t5\".\"other\" IS NULL FROM \"joined\" AS \"t5\"",
            "SELECT NOT (\"t5\".\"i\") IS NULL FROM \"joined\" AS \"t5\"",
            "SELECT NOT \"t5\".\"i\" IS NOT NULL FROM \"joined\" AS \"t5\"",
        ] {
            bind_query_program_to_sql(
                Path::new("sql1.sql"),
                source,
                &ir_with_program(&[forged]).queries,
            )
            .expect_err("nearby boolean rewrites must remain source-observable");
        }
    }

    #[test]
    fn source_program_binding_rejects_frontend_inserted_as_for_implicit_aliases() {
        let source = "SELECT count(*) cnt1 FROM customer c";
        bind_query_program_to_sql(
            Path::new("sql1.sql"),
            source,
            &ir_with_program(&[source]).queries,
        )
        .expect("an unchanged implicit output and relation alias must bind");

        for forged in [
            "SELECT count(*) AS cnt1 FROM customer c",
            "SELECT count(*) cnt1 FROM customer AS c",
            "SELECT count(*) AS cnt1 FROM customer AS c",
        ] {
            let error = bind_query_program_to_sql(
                Path::new("sql1.sql"),
                source,
                &ir_with_program(&[forged]).queries,
            )
            .expect_err("a frontend-inserted AS token must remain observable");
            assert!(matches!(error, Error::InvalidLogosIrInput(_)));
            assert!(format!("{error}").contains("first differing token"));
        }
    }

    #[test]
    fn load_ir_rejects_static_frontend_source_sql_forgery_and_count_drift() {
        let input = verification_input("select 1", "select 1");
        let error = input
            .load_ir(&StaticSqlIrFrontend {
                ir: ir_with_program(&["select 2"]),
            })
            .expect_err("a static frontend cannot substitute a different query");
        assert!(matches!(error, Error::InvalidLogosIrInput(_)));
        assert!(format!("{error}").contains("first differing token"));

        let two_statement_input = verification_input("select 1; select 2", "select 1; select 2");
        let error = two_statement_input
            .load_ir(&StaticSqlIrFrontend {
                ir: ir_with_program(&["select 1"]),
            })
            .expect_err("a static frontend cannot omit a program statement");
        assert!(matches!(error, Error::InvalidLogosIrInput(_)));
        assert!(format!("{error}").contains("contains 2 PostgreSQL SQL statement(s)"));

        let mut missing_source = ir_with_program(&["select 1"]);
        missing_source.queries[0].source_sql = None;
        let error = input
            .load_ir(&StaticSqlIrFrontend { ir: missing_source })
            .expect_err("every frontend query must carry sourceSql");
        assert!(matches!(error, Error::InvalidLogosIrInput(_)));
        assert!(format!("{error}").contains("missing sourceSql"));
    }

    #[test]
    fn multi_statement_program_is_bound_in_statement_order() {
        let source = "SELECT account_id FROM accounts WHERE active = TRUE;\n\
                      SELECT account_id FROM accounts WHERE balance > 0;";
        let statements =
            split_postgres_query_program(source).expect("split generic two-statement program");
        assert_eq!(statements.len(), 2);
        assert!(statements[0].contains("active = TRUE"));
        assert!(!statements[0].contains("balance > 0"));
        assert!(statements[1].contains("balance > 0"));

        let input = verification_input(source, source);
        input
            .load_ir(&StaticSqlIrFrontend {
                ir: ir_with_program(&statements),
            })
            .expect("ordered exact statements must bind");

        let error = input
            .load_ir(&StaticSqlIrFrontend {
                ir: ir_with_program(&[statements[1], statements[0]]),
            })
            .expect_err("swapped statements must not bind");
        assert!(matches!(error, Error::InvalidLogosIrInput(_)));
        assert!(format!("{error}").contains("statement 1"));
    }

    #[test]
    fn reads_verification_input_with_logos_ir_queries() {
        let temp = std::env::temp_dir().join(format!(
            "logos-solver-verification-input-test-{}",
            std::process::id()
        ));
        std::fs::create_dir_all(&temp).expect("create temp dir");
        let schema_path = temp.join("schema.sql");
        let source_path = temp.join("source.sql");
        let target_path = temp.join("target.sql");
        std::fs::write(&schema_path, "create table t(a int);").expect("write schema");
        std::fs::write(&source_path, "select 1;").expect("write source");
        std::fs::write(&target_path, "select 1;").expect("write target");

        let input = VerificationInput::read_with_environment(
            schema_path,
            source_path,
            target_path,
            SqlEnvironment::default(),
        )
        .expect("read input");

        assert_eq!(input.stable_cache_key(), input.stable_cache_key());

        let ir = input
            .load_ir(&StaticSqlIrFrontend { ir: empty_ir() })
            .expect("verification IR should load");
        assert_eq!(ir.schema_ir().tables.len(), 0);
        assert_eq!(ir.source_program_ir().len(), 1);
        assert_eq!(ir.target_program_ir().len(), 1);
        assert_eq!(ir.source_program_ir()[0].output().len(), 0);
        assert_eq!(ir.target_program_ir()[0].output().len(), 0);
    }

    fn empty_ir() -> LogosIrFile {
        ir_with_program(&["select 1"])
    }

    fn string_unique_schema_ir(environment: SqlEnvironment) -> LogosIrFile {
        LogosIrFile {
            environment,
            schema: Schema {
                tables: vec![Table {
                    name: "t".to_owned(),
                    columns: vec![Column {
                        name: "code".to_owned(),
                        ty: SqlType::String(SqlStringType::Text),
                        nullable: true,
                    }],
                    constraints: TableConstraints {
                        unique: vec![UniqueConstraint {
                            name: None,
                            columns: vec!["code".to_owned()],
                        }],
                        ..TableConstraints::default()
                    },
                }],
            },
            queries: vec![],
        }
    }

    fn verification_input(source_sql: &str, target_sql: &str) -> VerificationInput {
        VerificationInput {
            sql_environment: SqlEnvironment::default(),
            integrity_contract: SchemaIntegrityContract::default(),
            schema: SchemaInput {
                path: PathBuf::from("schema.sql"),
                sql: String::new(),
            },
            source_query: QueryInput {
                path: PathBuf::from("source.sql"),
                sql: source_sql.to_owned(),
            },
            target_query: QueryInput {
                path: PathBuf::from("target.sql"),
                sql: target_sql.to_owned(),
            },
        }
    }

    fn ir_with_program(statements: &[&str]) -> LogosIrFile {
        LogosIrFile {
            environment: SqlEnvironment::default(),
            schema: Schema { tables: vec![] },
            queries: statements
                .iter()
                .map(|statement| Query {
                    source_sql: Some((*statement).to_owned()),
                    rel: RelExpr::Values {
                        rows: vec![],
                        output: vec![],
                    },
                    analysis_errors: vec![],
                })
                .collect(),
        }
    }
}
