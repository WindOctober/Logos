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
    } else if upper.starts_with("DECIMAL") || upper.starts_with("NUMERIC") {
        Ok(SqlType::decimal(
            parse_type_precision(&upper),
            decimal_scale(&upper),
        ))
    } else if upper.starts_with("VARCHAR") || upper.starts_with("CHAR") {
        Ok(SqlType::Varchar)
    } else if upper.starts_with("BOOLEAN") {
        Ok(SqlType::Boolean)
    } else if type_head_is(&upper, "DATE") {
        Ok(SqlType::Date)
    } else if type_head_is(&upper, "TIME") && !upper.contains("WITH") {
        Ok(SqlType::Time)
    } else if type_head_is(&upper, "TIMESTAMP") && !upper.contains("WITH") {
        Ok(SqlType::timestamp(parse_type_precision(&upper)))
    } else if timestamp_with_time_zone(&upper) {
        Ok(SqlType::timestamptz(parse_type_precision(&upper)))
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

fn parse_type_precision(ty: &str) -> Option<u32> {
    let start = ty.find('(')? + 1;
    let end = ty[start..].find(')')? + start;
    ty[start..end].split(',').next()?.trim().parse().ok()
}

fn parse_type_scale(ty: &str) -> Option<u32> {
    u32::try_from(parse_type_scale_i32(ty)?).ok()
}

fn parse_type_scale_i32(ty: &str) -> Option<i32> {
    let start = ty.find('(')? + 1;
    let end = ty[start..].find(')')? + start;
    let mut parts = ty[start..end].split(',');
    parts.next()?;
    parts.next()?.trim().parse().ok()
}

fn decimal_scale(ty: &str) -> Option<u32> {
    if parse_type_scale_i32(ty).is_some_and(|scale| scale < 0) {
        return None;
    }
    parse_type_scale(ty).or_else(|| parse_type_precision(ty).map(|_| 0))
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
            parse_calcite_sql_type("NUMERIC(10, 2)").unwrap(),
            SqlType::decimal(Some(10), Some(2))
        );
        assert_eq!(
            parse_calcite_sql_type("DECIMAL(2, -3)").unwrap(),
            SqlType::decimal(Some(2), None)
        );
        assert_eq!(
            parse_calcite_sql_type("TIMESTAMP(0)").unwrap(),
            SqlType::timestamp(Some(0))
        );
        assert_eq!(parse_calcite_sql_type("ANY").unwrap(), SqlType::Any);
        assert_eq!(parse_calcite_sql_type("NULL").unwrap(), SqlType::Null);
    }

    #[test]
    fn parses_timezone_timestamp_types() {
        assert_eq!(
            parse_calcite_sql_type("TIMESTAMP WITH LOCAL TIME ZONE").unwrap(),
            SqlType::timestamptz(None)
        );
        assert_eq!(
            parse_calcite_sql_type("TIMESTAMPTZ(6)").unwrap(),
            SqlType::timestamptz(Some(6))
        );
        assert_eq!(
            parse_calcite_sql_type("TIMESTAMP_TZ(3)").unwrap(),
            SqlType::timestamptz(Some(3))
        );
    }
}
