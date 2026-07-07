use std::time::{SystemTime, UNIX_EPOCH};

use postgres::Transaction;

use crate::error::Result;

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
    schema_sql: &str,
    witness_sql: &str,
) -> Result<()> {
    transaction.batch_execute(&format!(
        "SET statement_timeout = {}; CREATE SCHEMA {}; SET search_path TO {}, public;",
        statement_timeout_ms,
        quote_ident(schema_name),
        quote_ident(schema_name)
    ))?;
    transaction.batch_execute(schema_sql)?;
    transaction.batch_execute(witness_sql)?;
    Ok(())
}

pub(super) fn trim_query(sql: &str) -> &str {
    sql.trim().trim_end_matches(';').trim()
}

fn quote_ident(value: &str) -> String {
    format!("\"{}\"", value.replace('"', "\"\""))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn trims_trailing_semicolon() {
        assert_eq!(trim_query(" select 1; \n"), "select 1");
    }

    #[test]
    fn quotes_schema_identifier() {
        assert_eq!(quote_ident("a\"b"), "\"a\"\"b\"");
    }
}
