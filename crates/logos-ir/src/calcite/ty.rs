use crate::error::{Error, Result};
use crate::ir::SqlType;

pub fn parse_calcite_sql_type(value: &str) -> Result<SqlType> {
    let upper = value.trim().to_ascii_uppercase();
    if upper == "ANY" {
        Ok(SqlType::Any)
    } else if upper == "NULL" {
        Ok(SqlType::Null)
    } else if upper.starts_with("INTEGER") {
        Ok(SqlType::Integer)
    } else if upper.starts_with("BIGINT") {
        Ok(SqlType::BigInt)
    } else if upper.starts_with("FLOAT") || upper.starts_with("REAL") {
        Ok(SqlType::Float)
    } else if upper.starts_with("DOUBLE") {
        Ok(SqlType::Double)
    } else if upper.starts_with("DECIMAL") {
        Ok(SqlType::Decimal)
    } else if upper.starts_with("VARCHAR") || upper.starts_with("CHAR") {
        Ok(SqlType::Varchar)
    } else if upper.starts_with("BOOLEAN") {
        Ok(SqlType::Boolean)
    } else if type_head_is(&upper, "DATE") {
        Ok(SqlType::Date)
    } else if type_head_is(&upper, "TIME") && !upper.contains("WITH") {
        Ok(SqlType::Time)
    } else if type_head_is(&upper, "TIMESTAMP") && !upper.contains("WITH") {
        Ok(SqlType::Timestamp)
    } else {
        Err(Error::UnsupportedSqlType(value.to_owned()))
    }
}

fn type_head_is(value: &str, head: &str) -> bool {
    value == head
        || value.starts_with(&format!("{head}("))
        || value.starts_with(&format!("{head} "))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_calcite_core_types() {
        assert_eq!(parse_calcite_sql_type("INTEGER").unwrap(), SqlType::Integer);
        assert_eq!(
            parse_calcite_sql_type("VARCHAR(20)").unwrap(),
            SqlType::Varchar
        );
        assert_eq!(
            parse_calcite_sql_type("TIMESTAMP(0)").unwrap(),
            SqlType::Timestamp
        );
        assert_eq!(parse_calcite_sql_type("ANY").unwrap(), SqlType::Any);
        assert_eq!(parse_calcite_sql_type("NULL").unwrap(), SqlType::Null);
    }

    #[test]
    fn rejects_timezone_types_until_modeled() {
        assert!(matches!(
            parse_calcite_sql_type("TIMESTAMP WITH LOCAL TIME ZONE"),
            Err(Error::UnsupportedSqlType(value))
            if value == "TIMESTAMP WITH LOCAL TIME ZONE"
        ));
    }
}
