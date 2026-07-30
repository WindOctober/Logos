use std::time::{SystemTime, UNIX_EPOCH};

use logos_ir::ir::{
    SqlCharacterClassification, SqlDefaultCollation, SqlLocaleProvider, SqlServerEncoding,
};
use postgres::Transaction;

use crate::core::{SqlEnvironment, SqlTimeZone};
use crate::error::{Error, Result};

pub(super) fn fresh_schema_name() -> String {
    let millis = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|duration| duration.as_millis())
        .unwrap_or(0);
    format!("logos_cex_{}_{}", std::process::id(), millis)
}

pub(super) fn setup_witness_schema(
    transaction: &mut Transaction<'_>,
    schema_name: &str,
    statement_timeout_ms: u64,
    sql_time_zone: &SqlTimeZone,
    sql_environment: &SqlEnvironment,
    schema_sql: &str,
    witness_sql: &str,
) -> Result<()> {
    if !witness_uses_only_allowed_dml(witness_sql) {
        return Err(Error::InvalidCandidate(
            "witnessSql must contain only top-level INSERT, UPDATE, or DELETE statements; transaction control, SET, DDL, CALL, DO, and CTE-prefixed statements are rejected"
                .to_owned(),
        ));
    }
    setup_validation_context(
        transaction,
        schema_name,
        statement_timeout_ms,
        sql_time_zone,
        sql_environment,
        schema_sql,
        Some(witness_sql),
    )
}

pub(super) fn setup_output_schema_probe(
    transaction: &mut Transaction<'_>,
    schema_name: &str,
    statement_timeout_ms: u64,
    sql_time_zone: &SqlTimeZone,
    sql_environment: &SqlEnvironment,
    schema_sql: &str,
) -> Result<()> {
    setup_validation_context(
        transaction,
        schema_name,
        statement_timeout_ms,
        sql_time_zone,
        sql_environment,
        schema_sql,
        None,
    )
}

fn setup_validation_context(
    transaction: &mut Transaction<'_>,
    schema_name: &str,
    statement_timeout_ms: u64,
    sql_time_zone: &SqlTimeZone,
    sql_environment: &SqlEnvironment,
    schema_sql: &str,
    witness_sql: Option<&str>,
) -> Result<()> {
    reject_schema_transaction_control(schema_sql)?;
    validate_database_environment(transaction, *sql_environment)?;
    transaction.batch_execute(&format!("CREATE SCHEMA {};", quote_ident(schema_name),))?;
    apply_validation_profile(
        transaction,
        schema_name,
        statement_timeout_ms,
        sql_time_zone,
    )?;
    // Force assignment of PostgreSQL's epoch-aware 64-bit transaction
    // identifier before either external SQL batch. If a batch commits,
    // rolls back, prepares, or restarts the transaction, the identifier below
    // necessarily changes. This is a protocol check independent of textual
    // transaction-control spelling.
    let original_transaction_id = current_transaction_id(transaction)?;
    transaction.batch_execute(schema_sql)?;
    ensure_same_transaction(
        transaction,
        original_transaction_id,
        "schema SQL terminated or replaced the PostgreSQL validation transaction",
    )?;
    // The schema is benchmark input rather than witness data, but it can
    // contain SET. Restore the lexical/execution profile before an optional
    // witness batch or the schema-only probe.
    apply_validation_profile(
        transaction,
        schema_name,
        statement_timeout_ms,
        sql_time_zone,
    )?;
    if let Some(witness_sql) = witness_sql {
        transaction.batch_execute(witness_sql)?;
        ensure_same_transaction(
            transaction,
            original_transaction_id,
            "witness SQL terminated or replaced the PostgreSQL validation transaction",
        )?;
    }
    // External schema and witness text may contain SET or RESET statements.
    // Reassert the language-level session settings immediately before any
    // validation query.
    // Physical planner choices, including parallel aggregation, are
    // deliberately left to PostgreSQL and remain diagnostic evidence only.
    apply_validation_profile(
        transaction,
        schema_name,
        statement_timeout_ms,
        sql_time_zone,
    )?;
    Ok(())
}

fn reject_schema_transaction_control(sql: &str) -> Result<()> {
    let keywords = top_level_statement_keywords(sql).ok_or_else(|| {
        Error::InvalidSchemaSql(
            "schema SQL has malformed or unsupported lexical structure".to_owned(),
        )
    })?;
    if let Some(keyword) = keywords.iter().find(|keyword| {
        matches!(
            keyword.as_str(),
            "BEGIN"
                | "START"
                | "COMMIT"
                | "END"
                | "ROLLBACK"
                | "ABORT"
                | "SAVEPOINT"
                | "RELEASE"
                | "PREPARE"
                | "CALL"
        )
    }) {
        return Err(Error::InvalidSchemaSql(format!(
            "top-level {keyword} is not allowed inside the managed validation transaction"
        )));
    }
    Ok(())
}

fn validate_database_environment(
    transaction: &mut Transaction<'_>,
    expected: SqlEnvironment,
) -> Result<()> {
    let row = transaction.query_one(
        "SELECT datcollate, datctype, \
                CASE datlocprovider \
                  WHEN 'c' THEN 'libc' \
                  WHEN 'i' THEN 'icu' \
                  WHEN 'b' THEN 'builtin' \
                  ELSE datlocprovider::text \
                END, \
                pg_catalog.pg_encoding_to_char(encoding) \
         FROM pg_catalog.pg_database WHERE datname = pg_catalog.current_database()",
        &[],
    )?;
    let actual_collation: String = row.get(0);
    let actual_character_classification: String = row.get(1);
    let actual_locale_provider: String = row.get(2);
    let actual_encoding: String = row.get(3);
    database_environment_matches(
        expected,
        &actual_collation,
        &actual_character_classification,
        &actual_locale_provider,
        &actual_encoding,
    )
}

fn database_environment_matches(
    expected: SqlEnvironment,
    actual_collation: &str,
    actual_character_classification: &str,
    actual_locale_provider: &str,
    actual_encoding: &str,
) -> Result<()> {
    if !matches!(expected.default_collation, SqlDefaultCollation::Unspecified)
        && actual_collation != expected.default_collation_label()
    {
        return Err(Error::PostgresEnvironmentMismatch(format!(
            "database default collation is {actual_collation:?}, expected {:?}",
            expected.default_collation_label()
        )));
    }
    if !matches!(
        expected.character_classification,
        SqlCharacterClassification::Unspecified
    ) && actual_character_classification != expected.character_classification_label()
    {
        return Err(Error::PostgresEnvironmentMismatch(format!(
            "database character classification is {actual_character_classification:?}, expected {:?}",
            expected.character_classification_label()
        )));
    }
    if !matches!(expected.locale_provider, SqlLocaleProvider::Unspecified)
        && actual_locale_provider != expected.locale_provider_label()
    {
        return Err(Error::PostgresEnvironmentMismatch(format!(
            "database locale provider is {actual_locale_provider:?}, expected {:?}",
            expected.locale_provider_label()
        )));
    }
    if !matches!(expected.server_encoding, SqlServerEncoding::Unspecified)
        && !actual_encoding.eq_ignore_ascii_case(expected.server_encoding_label())
    {
        return Err(Error::PostgresEnvironmentMismatch(format!(
            "database server encoding is {actual_encoding:?}, expected {:?}",
            expected.server_encoding_label()
        )));
    }
    Ok(())
}

fn current_transaction_id(transaction: &mut Transaction<'_>) -> Result<i64> {
    Ok(transaction
        .query_one("SELECT pg_catalog.txid_current()", &[])?
        .get(0))
}

fn ensure_same_transaction(
    transaction: &mut Transaction<'_>,
    expected: i64,
    message: &str,
) -> Result<()> {
    if current_transaction_id(transaction)? == expected {
        Ok(())
    } else {
        Err(Error::InvalidCandidate(message.to_owned()))
    }
}

pub(crate) fn witness_uses_only_allowed_dml(sql: &str) -> bool {
    top_level_statement_keywords(sql).is_some_and(|keywords| {
        !keywords.is_empty()
            && keywords
                .iter()
                .all(|keyword| matches!(keyword.as_str(), "INSERT" | "UPDATE" | "DELETE"))
    })
}

/// Extract the first keyword of every top-level SQL statement while ignoring
/// PostgreSQL quoted strings, quoted identifiers, dollar strings, and nested
/// comments. Returning `None` is a conservative rejection for malformed or
/// unsupported text. Witnesses are deliberately restricted to the direct DML
/// form promised by the counterexample protocol.
fn top_level_statement_keywords(sql: &str) -> Option<Vec<String>> {
    #[derive(Debug)]
    enum State {
        Normal,
        SingleQuoted { backslash_escapes: bool },
        DoubleQuoted,
        LineComment,
        BlockComment(usize),
        DollarQuoted(Vec<u8>),
    }

    let bytes = sql.as_bytes();
    let mut index = 0;
    let mut state = State::Normal;
    let mut statement_start = true;
    let mut keywords = Vec::new();
    while index < bytes.len() {
        match &mut state {
            State::Normal => {
                if bytes[index].is_ascii_whitespace() {
                    index += 1;
                } else if bytes[index..].starts_with(b"--") {
                    state = State::LineComment;
                    index += 2;
                } else if bytes[index..].starts_with(b"/*") {
                    state = State::BlockComment(1);
                    index += 2;
                } else if bytes[index] == b'\'' {
                    if unicode_escape_prefix_at(bytes, index) {
                        return None;
                    }
                    state = State::SingleQuoted {
                        backslash_escapes: quoted_string_uses_backslash_escapes(bytes, index),
                    };
                    index += 1;
                } else if bytes[index] == b'"' {
                    if unicode_escape_prefix_at(bytes, index) {
                        return None;
                    }
                    state = State::DoubleQuoted;
                    index += 1;
                } else if bytes[index] == b'$'
                    && (index == 0 || !postgres_identifier_continuation(bytes[index - 1]))
                {
                    match dollar_quote_delimiter(&bytes[index..]) {
                        Ok(Some(delimiter)) => {
                            index += delimiter.len();
                            state = State::DollarQuoted(delimiter);
                        }
                        Ok(None) if statement_start => return None,
                        Ok(None) => index += 1,
                        Err(()) => return None,
                    }
                } else if bytes[index] == b';' {
                    statement_start = true;
                    index += 1;
                } else if statement_start {
                    if !bytes[index].is_ascii_alphabetic() {
                        return None;
                    }
                    let start = index;
                    index += 1;
                    while index < bytes.len()
                        && (bytes[index].is_ascii_alphanumeric() || bytes[index] == b'_')
                    {
                        index += 1;
                    }
                    keywords.push(sql[start..index].to_ascii_uppercase());
                    statement_start = false;
                } else {
                    index += 1;
                }
            }
            State::SingleQuoted { backslash_escapes } => {
                if *backslash_escapes && bytes[index] == b'\\' {
                    // E/e and U& strings give the next character escape
                    // significance. Skipping the pair is sufficient for
                    // quote/boundary recognition; PostgreSQL performs the
                    // detailed escape validation when executing the witness.
                    index += 1;
                    if index < bytes.len() {
                        index += 1;
                    }
                } else if bytes[index] == b'\'' {
                    if bytes.get(index + 1) == Some(&b'\'') {
                        index += 2;
                    } else {
                        state = State::Normal;
                        index += 1;
                    }
                } else {
                    index += 1;
                }
            }
            State::DoubleQuoted => {
                if bytes[index] == b'"' {
                    if bytes.get(index + 1) == Some(&b'"') {
                        index += 2;
                    } else {
                        state = State::Normal;
                        index += 1;
                    }
                } else {
                    index += 1;
                }
            }
            State::LineComment => {
                if matches!(bytes[index], b'\n' | b'\r') {
                    state = State::Normal;
                }
                index += 1;
            }
            State::BlockComment(depth) => {
                if bytes[index..].starts_with(b"/*") {
                    *depth += 1;
                    index += 2;
                } else if bytes[index..].starts_with(b"*/") {
                    *depth -= 1;
                    index += 2;
                    if *depth == 0 {
                        state = State::Normal;
                    }
                } else {
                    index += 1;
                }
            }
            State::DollarQuoted(delimiter) => {
                if bytes[index..].starts_with(delimiter) {
                    index += delimiter.len();
                    state = State::Normal;
                } else {
                    index += 1;
                }
            }
        }
    }
    match state {
        State::Normal | State::LineComment => Some(keywords),
        _ => None,
    }
}

fn quoted_string_uses_backslash_escapes(input: &[u8], quote_index: usize) -> bool {
    quote_index >= 1
        && matches!(input[quote_index - 1], b'E' | b'e')
        && (quote_index == 1 || !postgres_identifier_continuation(input[quote_index - 2]))
}

fn unicode_escape_prefix_at(input: &[u8], quote_index: usize) -> bool {
    quote_index >= 2
        && input[quote_index - 1] == b'&'
        && matches!(input[quote_index - 2], b'U' | b'u')
        && (quote_index == 2 || !postgres_identifier_continuation(input[quote_index - 3]))
}

fn postgres_identifier_continuation(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'$') || !byte.is_ascii()
}

/// Return `Err` when a delimiter uses high-bit bytes. PostgreSQL accepts
/// locale-dependent non-ASCII identifier characters in tags; the validation
/// protocol rejects that rare surface rather than approximating its lexer.
fn dollar_quote_delimiter(input: &[u8]) -> std::result::Result<Option<Vec<u8>>, ()> {
    if input.first() != Some(&b'$') {
        return Ok(None);
    }
    if input.get(1) == Some(&b'$') {
        return Ok(Some(b"$$".to_vec()));
    }
    let Some(&first) = input.get(1) else {
        return Ok(None);
    };
    if !first.is_ascii() {
        return Err(());
    }
    if !(first.is_ascii_alphabetic() || first == b'_') {
        return Ok(None);
    }
    let mut end = 2;
    while let Some(byte) = input.get(end) {
        if *byte == b'$' {
            return Ok(Some(input[..=end].to_vec()));
        }
        if !byte.is_ascii() {
            return Err(());
        }
        if !(byte.is_ascii_alphanumeric() || *byte == b'_') {
            return Ok(None);
        }
        end += 1;
    }
    Ok(None)
}

fn apply_validation_profile(
    transaction: &mut Transaction<'_>,
    schema_name: &str,
    statement_timeout_ms: u64,
    sql_time_zone: &SqlTimeZone,
) -> Result<()> {
    transaction.batch_execute(&validation_profile_sql(
        schema_name,
        statement_timeout_ms,
        sql_time_zone,
    ))?;
    Ok(())
}

fn validation_profile_sql(
    schema_name: &str,
    statement_timeout_ms: u64,
    sql_time_zone: &SqlTimeZone,
) -> String {
    let set_time_zone = sql_time_zone
        .postgres_set_time_zone_sql()
        .expect("SQL time zone is validated before witness checking")
        .replacen("SET ", "SET LOCAL ", 1);
    format!(
        "RESET ALL; SET LOCAL statement_timeout = {}; {}; SET LOCAL standard_conforming_strings = on; SET LOCAL transform_null_equals = off; SET LOCAL search_path TO {}, public;",
        statement_timeout_ms,
        set_time_zone,
        quote_ident(schema_name)
    )
}

fn quote_ident(value: &str) -> String {
    format!("\"{}\"", value.replace('"', "\"\""))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn quotes_schema_identifier() {
        assert_eq!(quote_ident("a\"b"), "\"a\"\"b\"");
    }

    #[test]
    fn validation_profile_reasserts_declarative_local_settings_after_witness_sql() {
        let sql = validation_profile_sql("attempted_reset", 3210, &SqlTimeZone::utc());
        assert!(sql.contains("SET LOCAL statement_timeout = 3210"));
        assert!(sql.contains("SET LOCAL TIME ZONE"));
        assert!(sql.contains("SET LOCAL standard_conforming_strings = on"));
        assert!(sql.contains("RESET ALL"));
        assert!(sql.contains("SET LOCAL transform_null_equals = off"));
        assert!(sql.contains("SET LOCAL search_path TO \"attempted_reset\", public"));
        assert!(!sql.contains("max_parallel_workers_per_gather"));
    }

    #[test]
    fn exact_postgres_utf8_libc_c_environment_matches_database_catalog() {
        database_environment_matches(SqlEnvironment::postgres_utf8_c(), "C", "C", "libc", "UTF8")
            .unwrap();
    }

    #[test]
    fn postgres_environment_rejects_character_classification_mismatch() {
        let error = database_environment_matches(
            SqlEnvironment::postgres_utf8_c(),
            "C",
            "C.UTF-8",
            "libc",
            "UTF8",
        )
        .unwrap_err();
        assert!(error.to_string().contains("character classification"));
    }

    #[test]
    fn postgres_environment_rejects_default_collation_mismatch() {
        let error = database_environment_matches(
            SqlEnvironment::postgres_utf8_c(),
            "C.UTF-8",
            "C",
            "libc",
            "UTF8",
        )
        .unwrap_err();
        assert!(error.to_string().contains("default collation"));
    }

    #[test]
    fn postgres_environment_rejects_locale_provider_mismatch() {
        let error = database_environment_matches(
            SqlEnvironment::postgres_utf8_c(),
            "C",
            "C",
            "icu",
            "UTF8",
        )
        .unwrap_err();
        assert!(error.to_string().contains("locale provider"));
    }

    #[test]
    fn postgres_environment_rejects_server_encoding_mismatch() {
        let error = database_environment_matches(
            SqlEnvironment::postgres_utf8_c(),
            "C",
            "C",
            "libc",
            "LATIN1",
        )
        .unwrap_err();
        assert!(error.to_string().contains("server encoding"));
    }

    #[test]
    fn unspecified_postgres_environment_remains_fail_closed_for_lowering_but_unconstrained_here() {
        database_environment_matches(
            SqlEnvironment::default(),
            "arbitrary-collation",
            "arbitrary-ctype",
            "arbitrary-provider",
            "arbitrary-encoding",
        )
        .unwrap();
        assert!(!SqlEnvironment::default().has_postgres_utf8_c_text_semantics());
    }

    #[test]
    fn witness_protocol_accepts_only_direct_dml_statements() {
        assert!(witness_uses_only_allowed_dml(
            "-- data only\nINSERT INTO t VALUES ('COMMIT; is data', $$a;b$$);\n\
             /* nested /* comment */ */ UPDATE t SET x = 2; DELETE FROM u;"
        ));
        assert!(!witness_uses_only_allowed_dml(
            "INSERT INTO t VALUES (1); COMMIT; SET max_parallel_workers_per_gather = 8;"
        ));
        assert!(!witness_uses_only_allowed_dml(
            r"INSERT INTO t VALUES (E'\''); COMMIT; INSERT INTO t VALUES (E'\'');"
        ));
        assert!(!witness_uses_only_allowed_dml(
            r"INSERT INTO t VALUES (E'a\'b'); SET transform_null_equals = on; INSERT INTO t VALUES (E'c\'d');"
        ));
        assert!(!witness_uses_only_allowed_dml(
            "INSERT INTO foo$tag$bar VALUES (1); ALTER TABLE t ADD COLUMN z int; INSERT INTO baz$tag$qux VALUES (1);"
        ));
        assert!(!witness_uses_only_allowed_dml(
            "INSERT INTO t VALUES ($é$non-ascii tag$é$);"
        ));
        assert!(!witness_uses_only_allowed_dml(
            r"INSERT INTO t VALUES (U&'a\' UESCAPE '!'); SET transform_null_equals=on; INSERT INTO t VALUES (E'c\'d');"
        ));
        assert!(!witness_uses_only_allowed_dml(
            r#"INSERT INTO U&"a\" UESCAPE '!' VALUES (1); ALTER TABLE t ADD COLUMN z int; INSERT INTO t VALUES (2);"#
        ));
        assert!(!witness_uses_only_allowed_dml(
            "WITH values AS (SELECT 1) INSERT INTO t SELECT * FROM values;"
        ));
        assert!(!witness_uses_only_allowed_dml("SET ROLE postgres;"));
        assert!(!witness_uses_only_allowed_dml(""));
    }

    #[test]
    fn schema_setup_rejects_transaction_escape_before_execution() {
        for statement in [
            "BEGIN",
            "START TRANSACTION",
            "COMMIT",
            "END",
            "ROLLBACK",
            "ABORT",
            "SAVEPOINT s",
            "RELEASE SAVEPOINT s",
            "PREPARE TRANSACTION 'x'",
            "CALL transaction_controlling_procedure()",
        ] {
            let error = reject_schema_transaction_control(statement)
                .expect_err("transaction control must be rejected");
            assert!(
                error.to_string().contains("managed validation transaction"),
                "{statement}"
            );
        }

        reject_schema_transaction_control(
            "CREATE TABLE t (note text DEFAULT 'COMMIT'); -- ROLLBACK\n\
             CREATE FUNCTION f() RETURNS text LANGUAGE sql AS $$ SELECT 'BEGIN' $$;",
        )
        .expect("protected transaction words are data, not statements");
    }
}
