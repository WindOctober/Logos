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
    } else if timestamp_with_time_zone(&upper) {
        Ok(SqlType::TimestampTz)
    } else {
        Err(Error::UnsupportedSqlType(value.to_owned()))
    }
}

fn type_head_is(value: &str, head: &str) -> bool {
    value == head
        || value.starts_with(&format!("{head}("))
        || value.starts_with(&format!("{head} "))
}

fn timestamp_with_time_zone(value: &str) -> bool {
    value.starts_with("TIMESTAMPTZ")
        || value.starts_with("TIMESTAMPZ")
        || value.starts_with("TIMESTAMP_TZ")
        || (type_head_is(value, "TIMESTAMP")
            && value.contains("WITH")
            && value.contains("TIME ZONE"))
        || value.starts_with("TIMESTAMP_WITH_TIME_ZONE")
        || value.starts_with("TIMESTAMP_WITH_LOCAL_TIME_ZONE")
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
    fn parses_timezone_timestamp_types() {
        assert_eq!(
            parse_calcite_sql_type("TIMESTAMP WITH LOCAL TIME ZONE").unwrap(),
            SqlType::TimestampTz
        );
        assert_eq!(
            parse_calcite_sql_type("TIMESTAMPTZ(6)").unwrap(),
            SqlType::TimestampTz
        );
        assert_eq!(
            parse_calcite_sql_type("TIMESTAMP_TZ(3)").unwrap(),
            SqlType::TimestampTz
        );
    }
}
