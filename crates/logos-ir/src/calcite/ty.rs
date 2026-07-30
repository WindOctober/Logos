use crate::error::{Error, Result};
use crate::ir::SqlType;

/// Structural view of the parenthesized argument list in a SQL type
/// annotation.  The parser deliberately keeps any suffix separate: callers
/// that accept forms such as `TIMESTAMP(3) WITH TIME ZONE` can inspect it,
/// while source-closed lowering paths can require an empty suffix.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct TypeAnnotation<'a> {
    prefix: &'a str,
    arguments: Option<&'a str>,
    suffix: &'a str,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TimestampTypeKind {
    WithoutTimeZone,
    WithTimeZone,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IntervalTypeKind {
    Unqualified,
    Year,
    YearMonth,
    Month,
    Day,
    DayHour,
    DayMinute,
    DaySecond,
    Hour,
    HourMinute,
    HourSecond,
    Minute,
    MinuteSecond,
    Second,
}

impl IntervalTypeKind {
    pub fn canonical_name(self) -> &'static str {
        match self {
            Self::Unqualified => "INTERVAL",
            Self::Year => "INTERVAL YEAR",
            Self::YearMonth => "INTERVAL YEAR MONTH",
            Self::Month => "INTERVAL MONTH",
            Self::Day => "INTERVAL DAY",
            Self::DayHour => "INTERVAL DAY HOUR",
            Self::DayMinute => "INTERVAL DAY MINUTE",
            Self::DaySecond => "INTERVAL DAY SECOND",
            Self::Hour => "INTERVAL HOUR",
            Self::HourMinute => "INTERVAL HOUR MINUTE",
            Self::HourSecond => "INTERVAL HOUR SECOND",
            Self::Minute => "INTERVAL MINUTE",
            Self::MinuteSecond => "INTERVAL MINUTE SECOND",
            Self::Second => "INTERVAL SECOND",
        }
    }

    pub fn terminal_unit(self) -> Option<&'static str> {
        match self {
            Self::Unqualified => None,
            Self::Year => Some("YEAR"),
            Self::YearMonth | Self::Month => Some("MONTH"),
            Self::Day => Some("DAY"),
            Self::DayHour | Self::Hour => Some("HOUR"),
            Self::DayMinute | Self::HourMinute | Self::Minute => Some("MINUTE"),
            Self::DaySecond | Self::HourSecond | Self::MinuteSecond | Self::Second => {
                Some("SECOND")
            }
        }
    }
}

/// The complete set of SQL type annotations understood by the active Calcite
/// importer and FormalSQL lowering. Classification is deliberately closed:
/// arguments, signs, and suffixes are validated once before any caller can
/// project a family name or typmod from the annotation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SqlTypeAnnotation {
    Any,
    Null,
    Integer,
    BigInt,
    Real,
    Float {
        precision: Option<u32>,
    },
    Double,
    Decimal {
        precision: Option<u32>,
        scale: Option<u32>,
    },
    Text,
    Varchar {
        length: Option<u32>,
    },
    Char {
        length: Option<u32>,
    },
    Bpchar {
        length: Option<u32>,
    },
    Boolean,
    Date,
    Time {
        precision: Option<u32>,
    },
    Timestamp {
        precision: Option<u32>,
        kind: TimestampTypeKind,
    },
    Interval(IntervalTypeKind),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeAnnotationErrorKind {
    DecimalTypmod,
    Unsupported,
}

impl SqlTypeAnnotation {
    pub fn precision(self) -> Option<u32> {
        match self {
            Self::Float { precision }
            | Self::Decimal { precision, .. }
            | Self::Time { precision }
            | Self::Timestamp { precision, .. } => precision,
            Self::Varchar { length } | Self::Bpchar { length } => length,
            Self::Char { length } => length,
            _ => None,
        }
    }

    pub fn scale(self) -> Option<u32> {
        match self {
            Self::Decimal { scale, .. } => scale,
            _ => None,
        }
    }
}

impl<'a> TypeAnnotation<'a> {
    fn parse(value: &'a str) -> Option<Self> {
        let value = value.trim();
        if value.is_empty() {
            return None;
        }

        let Some(open) = value.find('(') else {
            return (!value.contains(')')).then_some(Self {
                prefix: value,
                arguments: None,
                suffix: "",
            });
        };
        if value[..open].contains(')') {
            return None;
        }
        let close = value[open + 1..].find(')')? + open + 1;
        let arguments = &value[open + 1..close];
        let suffix = value[close + 1..].trim();
        if value[..open].trim().is_empty()
            || arguments.contains(['(', ')'])
            || suffix.contains(['(', ')'])
        {
            return None;
        }
        Some(Self {
            prefix: value[..open].trim(),
            arguments: Some(arguments),
            suffix,
        })
    }

    fn prefix(self) -> &'a str {
        self.prefix
    }

    fn has_arguments(self) -> bool {
        self.arguments.is_some()
    }

    fn suffix(self) -> &'a str {
        self.suffix
    }

    /// Return the complete parenthesized argument list while leaving suffix
    /// policy to the caller. Empty or partially specified lists are rejected.
    fn arguments(self) -> Option<Vec<&'a str>> {
        let Some(arguments) = self.arguments else {
            return Some(Vec::new());
        };
        let arguments = arguments.split(',').map(str::trim).collect::<Vec<_>>();
        (!arguments.iter().any(|argument| argument.is_empty())).then_some(arguments)
    }
}

fn annotation_words_eq(left: &str, right: &str) -> bool {
    let mut left = left.split_ascii_whitespace();
    let mut right = right.split_ascii_whitespace();
    loop {
        match (left.next(), right.next()) {
            (Some(left), Some(right)) if left.eq_ignore_ascii_case(right) => {}
            (None, None) => return true,
            _ => return false,
        }
    }
}

fn unsigned_annotation_argument(raw: &str) -> Option<u32> {
    if raw.starts_with(['+', '-']) || !raw.bytes().all(|byte| byte.is_ascii_digit()) {
        return None;
    }
    raw.parse().ok()
}

fn optional_unsigned_argument(arguments: &[&str], maximum: Option<u32>) -> Option<Option<u32>> {
    match arguments {
        [] => Some(None),
        [argument] => {
            let value = unsigned_annotation_argument(argument)?;
            if maximum.is_some_and(|maximum| value > maximum) {
                return None;
            }
            Some(Some(value))
        }
        _ => None,
    }
}

fn positive_length(arguments: &[&str]) -> Option<Option<u32>> {
    let length = optional_unsigned_argument(arguments, None)?;
    SqlType::try_varchar(length).ok()?;
    Some(length)
}

fn classify_interval(prefix: &str, arguments: &[&str], suffix: &str) -> Option<IntervalTypeKind> {
    if !arguments.is_empty() || !suffix.is_empty() {
        return None;
    }
    let normalized = prefix
        .replace('_', " ")
        .split_ascii_whitespace()
        .map(str::to_ascii_uppercase)
        .collect::<Vec<_>>();
    let words = normalized.iter().map(String::as_str).collect::<Vec<_>>();
    Some(match words.as_slice() {
        ["INTERVAL"] => IntervalTypeKind::Unqualified,
        ["INTERVAL", "YEAR"] => IntervalTypeKind::Year,
        ["INTERVAL", "YEAR", "MONTH"] | ["INTERVAL", "YEAR", "TO", "MONTH"] => {
            IntervalTypeKind::YearMonth
        }
        ["INTERVAL", "MONTH"] => IntervalTypeKind::Month,
        ["INTERVAL", "DAY"] => IntervalTypeKind::Day,
        ["INTERVAL", "DAY", "HOUR"] | ["INTERVAL", "DAY", "TO", "HOUR"] => {
            IntervalTypeKind::DayHour
        }
        ["INTERVAL", "DAY", "MINUTE"] | ["INTERVAL", "DAY", "TO", "MINUTE"] => {
            IntervalTypeKind::DayMinute
        }
        ["INTERVAL", "DAY", "SECOND"] | ["INTERVAL", "DAY", "TO", "SECOND"] => {
            IntervalTypeKind::DaySecond
        }
        ["INTERVAL", "HOUR"] => IntervalTypeKind::Hour,
        ["INTERVAL", "HOUR", "MINUTE"] | ["INTERVAL", "HOUR", "TO", "MINUTE"] => {
            IntervalTypeKind::HourMinute
        }
        ["INTERVAL", "HOUR", "SECOND"] | ["INTERVAL", "HOUR", "TO", "SECOND"] => {
            IntervalTypeKind::HourSecond
        }
        ["INTERVAL", "MINUTE"] => IntervalTypeKind::Minute,
        ["INTERVAL", "MINUTE", "SECOND"] | ["INTERVAL", "MINUTE", "TO", "SECOND"] => {
            IntervalTypeKind::MinuteSecond
        }
        ["INTERVAL", "SECOND"] => IntervalTypeKind::Second,
        _ => return None,
    })
}

fn classify_timestamp(annotation: TypeAnnotation<'_>) -> Option<SqlTypeAnnotation> {
    let precision = optional_unsigned_argument(&annotation.arguments()?, None)?;
    SqlType::try_timestamp(precision).ok()?;
    let prefix = annotation.prefix();
    let suffix = annotation.suffix();
    let kind = if annotation_words_eq(prefix, "TIMESTAMP") {
        if annotation_words_eq(suffix, "") || annotation_words_eq(suffix, "WITHOUT TIME ZONE") {
            TimestampTypeKind::WithoutTimeZone
        } else if annotation_words_eq(suffix, "WITH TIME ZONE")
            || annotation_words_eq(suffix, "WITH LOCAL TIME ZONE")
        {
            TimestampTypeKind::WithTimeZone
        } else {
            return None;
        }
    } else {
        if !annotation_words_eq(suffix, "") {
            return None;
        }
        if annotation_words_eq(prefix, "TIMESTAMP WITHOUT TIME ZONE") {
            if annotation.has_arguments() {
                return None;
            }
            TimestampTypeKind::WithoutTimeZone
        } else if annotation_words_eq(prefix, "TIMESTAMP WITH TIME ZONE")
            || annotation_words_eq(prefix, "TIMESTAMP WITH LOCAL TIME ZONE")
        {
            if annotation.has_arguments() {
                return None;
            }
            TimestampTypeKind::WithTimeZone
        } else if matches!(
            prefix.to_ascii_uppercase().as_str(),
            "TIMESTAMPTZ"
                | "TIMESTAMPZ"
                | "TIMESTAMP_TZ"
                | "TIMESTAMP_WITH_TIME_ZONE"
                | "TIMESTAMP_WITH_LOCAL_TIME_ZONE"
        ) {
            TimestampTypeKind::WithTimeZone
        } else {
            return None;
        }
    };
    Some(SqlTypeAnnotation::Timestamp { precision, kind })
}

/// Parse and validate one complete type annotation. Unlike the former family
/// helpers, this never accepts an annotation merely because its first word or
/// first argument looks familiar.
pub fn classify_type_annotation(value: &str) -> Option<SqlTypeAnnotation> {
    let annotation = TypeAnnotation::parse(value)?;
    if let Some(timestamp) = classify_timestamp(annotation) {
        return Some(timestamp);
    }
    let arguments = annotation.arguments()?;
    if !annotation.suffix().is_empty() {
        return None;
    }
    if let Some(interval) = classify_interval(annotation.prefix(), &arguments, annotation.suffix())
    {
        return Some(SqlTypeAnnotation::Interval(interval));
    }

    let no_arguments = || arguments.is_empty().then_some(());
    let prefix = annotation.prefix();
    if annotation_words_eq(prefix, "ANY") {
        no_arguments()?;
        Some(SqlTypeAnnotation::Any)
    } else if annotation_words_eq(prefix, "NULL") {
        no_arguments()?;
        Some(SqlTypeAnnotation::Null)
    } else if matches!(
        prefix.to_ascii_uppercase().as_str(),
        "INTEGER" | "INT" | "INT4"
    ) {
        no_arguments()?;
        Some(SqlTypeAnnotation::Integer)
    } else if matches!(prefix.to_ascii_uppercase().as_str(), "BIGINT" | "INT8") {
        no_arguments()?;
        Some(SqlTypeAnnotation::BigInt)
    } else if matches!(prefix.to_ascii_uppercase().as_str(), "REAL" | "FLOAT4") {
        no_arguments()?;
        Some(SqlTypeAnnotation::Real)
    } else if annotation_words_eq(prefix, "FLOAT") {
        let precision = optional_unsigned_argument(&arguments, Some(53))?;
        if precision == Some(0) {
            return None;
        }
        Some(SqlTypeAnnotation::Float { precision })
    } else if annotation_words_eq(prefix, "DOUBLE PRECISION")
        || matches!(prefix.to_ascii_uppercase().as_str(), "DOUBLE" | "FLOAT8")
    {
        no_arguments()?;
        Some(SqlTypeAnnotation::Double)
    } else if matches!(prefix.to_ascii_uppercase().as_str(), "DECIMAL" | "NUMERIC") {
        let (precision, scale) = match arguments.as_slice() {
            [] => (None, None),
            [precision] => {
                let precision = unsigned_annotation_argument(precision)?;
                (Some(precision), Some(0))
            }
            [precision, scale] => {
                let precision = unsigned_annotation_argument(precision)?;
                let scale = unsigned_annotation_argument(scale)?;
                (Some(precision), Some(scale))
            }
            _ => return None,
        };
        SqlType::try_decimal(precision, scale).ok()?;
        Some(SqlTypeAnnotation::Decimal { precision, scale })
    } else if annotation_words_eq(prefix, "TEXT") {
        no_arguments()?;
        Some(SqlTypeAnnotation::Text)
    } else if annotation_words_eq(prefix, "VARCHAR")
        || annotation_words_eq(prefix, "CHARACTER VARYING")
        || annotation_words_eq(prefix, "CHAR VARYING")
    {
        Some(SqlTypeAnnotation::Varchar {
            length: positive_length(&arguments)?,
        })
    } else if annotation_words_eq(prefix, "CHAR") || annotation_words_eq(prefix, "CHARACTER") {
        Some(SqlTypeAnnotation::Char {
            length: positive_length(&arguments)?,
        })
    } else if annotation_words_eq(prefix, "BPCHAR") {
        Some(SqlTypeAnnotation::Bpchar {
            length: positive_length(&arguments)?,
        })
    } else if matches!(prefix.to_ascii_uppercase().as_str(), "BOOLEAN" | "BOOL") {
        no_arguments()?;
        Some(SqlTypeAnnotation::Boolean)
    } else if annotation_words_eq(prefix, "DATE") {
        no_arguments()?;
        Some(SqlTypeAnnotation::Date)
    } else if annotation_words_eq(prefix, "TIME") {
        let precision = optional_unsigned_argument(&arguments, Some(6))?;
        Some(SqlTypeAnnotation::Time { precision })
    } else if annotation_words_eq(prefix, "TIME WITHOUT TIME ZONE") {
        if annotation.has_arguments() {
            return None;
        }
        Some(SqlTypeAnnotation::Time { precision: None })
    } else {
        None
    }
}

/// Return the same closed classification while preserving the one diagnostic
/// distinction lowering needs: a DECIMAL/NUMERIC spelling whose complete
/// typmod is outside the modeled boundary. No partial typmod value escapes.
pub fn classify_type_annotation_checked(
    value: &str,
) -> std::result::Result<SqlTypeAnnotation, TypeAnnotationErrorKind> {
    if let Some(annotation) = classify_type_annotation(value) {
        return Ok(annotation);
    }
    let is_decimal = TypeAnnotation::parse(value).is_some_and(|annotation| {
        matches!(
            annotation.prefix().to_ascii_uppercase().as_str(),
            "DECIMAL" | "NUMERIC"
        )
    });
    Err(if is_decimal {
        TypeAnnotationErrorKind::DecimalTypmod
    } else {
        TypeAnnotationErrorKind::Unsupported
    })
}

pub fn type_annotation_precision(value: &str) -> Option<u32> {
    classify_type_annotation(value)?.precision()
}

pub fn parse_calcite_sql_type(value: &str) -> Result<SqlType> {
    let annotation = classify_type_annotation(value)
        .ok_or_else(|| Error::UnsupportedSqlType(value.to_owned()))?;
    match annotation {
        SqlTypeAnnotation::Any => Ok(SqlType::Any),
        SqlTypeAnnotation::Null => Ok(SqlType::Null),
        SqlTypeAnnotation::Integer => Ok(SqlType::Integer),
        SqlTypeAnnotation::BigInt => Ok(SqlType::BigInt),
        SqlTypeAnnotation::Real => Ok(SqlType::Float),
        SqlTypeAnnotation::Float { precision: None } => Ok(SqlType::Double),
        SqlTypeAnnotation::Float {
            precision: Some(1..=24),
        } => Ok(SqlType::Float),
        SqlTypeAnnotation::Float {
            precision: Some(25..=53),
        } => Ok(SqlType::Double),
        SqlTypeAnnotation::Float { .. } => Err(Error::UnsupportedSqlType(value.to_owned())),
        SqlTypeAnnotation::Double => Ok(SqlType::Double),
        SqlTypeAnnotation::Decimal { precision, scale } => SqlType::try_decimal(precision, scale)
            .map_err(|_| Error::UnsupportedSqlType(value.to_owned())),
        SqlTypeAnnotation::Text => Ok(SqlType::text()),
        SqlTypeAnnotation::Varchar { length } => {
            SqlType::try_varchar(length).map_err(|_| Error::UnsupportedSqlType(value.to_owned()))
        }
        SqlTypeAnnotation::Char { length } => SqlType::try_character(length.unwrap_or(1))
            .map_err(|_| Error::UnsupportedSqlType(value.to_owned())),
        SqlTypeAnnotation::Bpchar { length: None } => Ok(SqlType::bpchar()),
        SqlTypeAnnotation::Bpchar {
            length: Some(length),
        } => {
            SqlType::try_character(length).map_err(|_| Error::UnsupportedSqlType(value.to_owned()))
        }
        SqlTypeAnnotation::Boolean => Ok(SqlType::Boolean),
        SqlTypeAnnotation::Date => Ok(SqlType::Date),
        SqlTypeAnnotation::Time {
            precision: None | Some(6),
        } => Ok(SqlType::Time),
        SqlTypeAnnotation::Time { .. } | SqlTypeAnnotation::Interval(_) => {
            Err(Error::UnsupportedSqlType(value.to_owned()))
        }
        SqlTypeAnnotation::Timestamp {
            precision,
            kind: TimestampTypeKind::WithoutTimeZone,
        } => SqlType::try_timestamp(precision)
            .map_err(|_| Error::UnsupportedSqlType(value.to_owned())),
        SqlTypeAnnotation::Timestamp {
            precision,
            kind: TimestampTypeKind::WithTimeZone,
        } => SqlType::try_timestamptz(precision)
            .map_err(|_| Error::UnsupportedSqlType(value.to_owned())),
    }
}

/// Validate Calcite's `fullType` transport decoration and return the bare SQL
/// type. `NOT NULL` is transport metadata, never part of the SQL type grammar.
pub fn calcite_full_type_base(value: &str, nullable: bool) -> Result<&str> {
    if value.is_empty() || value.trim() != value {
        return Err(Error::UnsupportedSqlType(value.to_owned()));
    }
    let base = value.strip_suffix(" NOT NULL");
    if nullable == base.is_some() {
        return Err(Error::UnsupportedSqlType(value.to_owned()));
    }
    let base = base.unwrap_or(value);
    if base.is_empty() || base.ends_with(" NOT NULL") {
        return Err(Error::UnsupportedSqlType(value.to_owned()));
    }
    Ok(base)
}

/// Compare the SQL-type portion of two optional Calcite `fullType` values.
/// Present values must each agree with their independently transported
/// nullability bit before their bases can compare equal.
pub(super) fn calcite_full_type_bases_equal(
    left: Option<&str>,
    left_nullable: bool,
    right: Option<&str>,
    right_nullable: bool,
) -> bool {
    match (left, right) {
        (None, None) => true,
        (Some(left), Some(right)) => matches!(
            (
                calcite_full_type_base(left, left_nullable),
                calcite_full_type_base(right, right_nullable),
            ),
            (Ok(left), Ok(right)) if left == right
        ),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_calcite_core_types() {
        assert_eq!(parse_calcite_sql_type("INTEGER").unwrap(), SqlType::Integer);
        assert_eq!(parse_calcite_sql_type("INT").unwrap(), SqlType::Integer);
        assert_eq!(parse_calcite_sql_type("INT4").unwrap(), SqlType::Integer);
        assert_eq!(parse_calcite_sql_type("INT8").unwrap(), SqlType::BigInt);
        assert_eq!(parse_calcite_sql_type("BOOL").unwrap(), SqlType::Boolean);
        assert_eq!(
            parse_calcite_sql_type("VARCHAR(20)").unwrap(),
            SqlType::varchar(Some(20))
        );
        assert_eq!(parse_calcite_sql_type("TEXT").unwrap(), SqlType::text());
        assert_eq!(
            parse_calcite_sql_type("CHARACTER VARYING(20)").unwrap(),
            SqlType::varchar(Some(20))
        );
        assert_eq!(
            parse_calcite_sql_type("VARCHAR").unwrap(),
            SqlType::varchar(None)
        );
        assert_eq!(
            parse_calcite_sql_type("CHAR").unwrap(),
            SqlType::character(1)
        );
        assert_eq!(
            parse_calcite_sql_type("CHAR(3)").unwrap(),
            SqlType::character(3)
        );
        assert_eq!(
            parse_calcite_sql_type("CHARACTER(5)").unwrap(),
            SqlType::character(5)
        );
        assert_eq!(parse_calcite_sql_type("BPCHAR").unwrap(), SqlType::bpchar());
        assert_eq!(
            parse_calcite_sql_type("BPCHAR(5)").unwrap(),
            SqlType::character(5)
        );
        assert_eq!(
            parse_calcite_sql_type("NUMERIC(10, 2)").unwrap(),
            SqlType::decimal(Some(10), Some(2))
        );
        assert!(parse_calcite_sql_type("DECIMAL(2, -3)").is_err());
        assert_eq!(parse_calcite_sql_type("REAL").unwrap(), SqlType::Float);
        assert_eq!(parse_calcite_sql_type("FLOAT4").unwrap(), SqlType::Float);
        assert_eq!(parse_calcite_sql_type("FLOAT(24)").unwrap(), SqlType::Float);
        assert_eq!(parse_calcite_sql_type("FLOAT").unwrap(), SqlType::Double);
        assert_eq!(
            parse_calcite_sql_type("FLOAT(25)").unwrap(),
            SqlType::Double
        );
        assert_eq!(parse_calcite_sql_type("FLOAT8").unwrap(), SqlType::Double);
        assert_eq!(
            parse_calcite_sql_type("DOUBLE PRECISION").unwrap(),
            SqlType::Double
        );
        assert!(parse_calcite_sql_type("FLOAT(54)").is_err());
        assert!(parse_calcite_sql_type("SMALLINT").is_err());
        assert!(parse_calcite_sql_type("TINYINT").is_err());
        assert_eq!(classify_type_annotation("SMALLINT"), None);
        assert_eq!(classify_type_annotation("TINYINT"), None);
        assert!(parse_calcite_sql_type("CHAR(0)").is_err());
        assert!(parse_calcite_sql_type("INTEGERISH").is_err());
        assert!(parse_calcite_sql_type("BIGINTEGER").is_err());
        assert_eq!(
            parse_calcite_sql_type("TIMESTAMP(0)").unwrap(),
            SqlType::timestamp(Some(0))
        );
        assert_eq!(parse_calcite_sql_type("ANY").unwrap(), SqlType::Any);
        assert_eq!(parse_calcite_sql_type("NULL").unwrap(), SqlType::Null);
        assert_eq!(parse_calcite_sql_type("TIME(6)").unwrap(), SqlType::Time);
        assert!(parse_calcite_sql_type("TIME(0)").is_err());
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
        assert_eq!(
            parse_calcite_sql_type("TIMESTAMP WITHOUT TIME ZONE").unwrap(),
            SqlType::timestamp(None)
        );
        assert_eq!(
            parse_calcite_sql_type("TIMESTAMP(3) WITH TIME ZONE").unwrap(),
            SqlType::timestamptz(Some(3))
        );
        assert_eq!(
            parse_calcite_sql_type("TIMESTAMP_WITH_TIME_ZONE(3)").unwrap(),
            SqlType::timestamptz(Some(3))
        );
        for malformed in [
            "TIMESTAMP(3) trailing",
            "TIMESTAMP(+3)",
            "TIMESTAMP(-1)",
            "TIMESTAMP(7)",
            "TIMESTAMP(3,4)",
            "TIMESTAMPTZ(3) trailing",
            "TIMESTAMPTZ(7)",
            "TIMESTAMP(7) WITH TIME ZONE",
            "TIMESTAMP_WITH_TIME_ZONE(7)",
            "TIMESTAMP WITH TIME ZONE(3)",
            "TIMESTAMP WITHOUT TIME ZONE(3)",
            "TIMESTAMP WITH LOCAL TIME ZONE(3)",
        ] {
            assert!(
                parse_calcite_sql_type(malformed).is_err(),
                "malformed timestamp annotation was accepted: {malformed}"
            );
        }
    }

    #[test]
    fn structural_parser_preserves_scale_sign_and_suffix_for_closed_classification() {
        let annotation = TypeAnnotation::parse(" NUMERIC(10, -2) trailing ").unwrap();
        assert_eq!(annotation.arguments(), Some(vec!["10", "-2"]));
        assert_eq!(annotation.suffix(), "trailing");
        assert_eq!(classify_type_annotation("NUMERIC(10, -2) trailing"), None);
        assert_eq!(type_annotation_precision("NUMERIC(10, -2) trailing"), None);

        assert_eq!(
            TypeAnnotation::parse("TIMESTAMP(3) WITH TIME ZONE")
                .unwrap()
                .suffix(),
            "WITH TIME ZONE"
        );
        assert!(TypeAnnotation::parse("DECIMAL(10, 2").is_none());
        assert!(TypeAnnotation::parse("DECIMAL10, 2)").is_none());
    }

    #[test]
    fn closed_classifier_rejects_partial_type_matches() {
        for malformed in [
            "INTEGER(9)",
            "NUMERIC(10,2,999)",
            "DECIMAL(10,2) trailing",
            "FLOAT(24) trailing",
            "TIME(6,7)",
            "NUMERIC(10,-2)",
            "NUMERIC(10,+2)",
            "NUMERIC(+10,2)",
            "INTERVALGARBAGE",
            "INTERVAL DAY GARBAGE",
        ] {
            assert_eq!(
                classify_type_annotation(malformed),
                None,
                "partial type annotation was accepted: {malformed}"
            );
            assert!(
                parse_calcite_sql_type(malformed).is_err(),
                "partial SQL type was accepted: {malformed}"
            );
        }
        assert_eq!(
            classify_type_annotation("INTERVAL_DAY_TO_SECOND"),
            Some(SqlTypeAnnotation::Interval(IntervalTypeKind::DaySecond))
        );
        assert_eq!(
            classify_type_annotation("INTERVAL YEAR TO MONTH"),
            Some(SqlTypeAnnotation::Interval(IntervalTypeKind::YearMonth))
        );
    }

    #[test]
    fn closed_classifier_uses_the_sql_type_typmod_boundary() {
        for accepted in [
            "NUMERIC",
            "NUMERIC(1,0)",
            "NUMERIC(10)",
            "NUMERIC(1000,1000)",
            "VARCHAR",
            "VARCHAR(1)",
            "VARCHAR(10485760)",
            "CHAR(1)",
            "CHAR(10485760)",
            "TIMESTAMP(0)",
            "TIMESTAMP(6)",
            "TIMESTAMPTZ(0)",
            "TIMESTAMPTZ(6)",
        ] {
            assert!(
                parse_calcite_sql_type(accepted).is_ok(),
                "valid SQL type was rejected: {accepted}"
            );
        }

        for rejected in [
            "NUMERIC(0,0)",
            "NUMERIC(1001,0)",
            "NUMERIC(10,1001)",
            "VARCHAR(0)",
            "VARCHAR(10485761)",
            "CHAR(0)",
            "CHAR(10485761)",
            "TIMESTAMP(7)",
            "TIMESTAMPTZ(7)",
            "SMALLINT",
            "TINYINT",
        ] {
            assert!(
                parse_calcite_sql_type(rejected).is_err(),
                "out-of-boundary SQL type was accepted: {rejected}"
            );
        }
    }

    #[test]
    fn full_type_nullability_is_transport_only_and_exact() {
        assert_eq!(
            calcite_full_type_base("DECIMAL(10,2) NOT NULL", false).unwrap(),
            "DECIMAL(10,2)"
        );
        assert_eq!(
            calcite_full_type_base("DECIMAL(10,2)", true).unwrap(),
            "DECIMAL(10,2)"
        );
        assert!(calcite_full_type_base("INTEGER NOT NULL", true).is_err());
        assert!(calcite_full_type_base("INTEGER", false).is_err());
        assert!(calcite_full_type_base("INTEGER NOT NULL NOT NULL", false).is_err());
        assert!(calcite_full_type_base("INTEGER not null", false).is_err());
        assert!(calcite_full_type_base(" INTEGER NOT NULL", false).is_err());
        assert!(calcite_full_type_base("INTEGER NOT NULL ", false).is_err());
        assert!(parse_calcite_sql_type("INTEGER NOT NULL").is_err());

        assert!(calcite_full_type_bases_equal(
            Some("INTEGER NOT NULL"),
            false,
            Some("INTEGER"),
            true,
        ));
        assert!(!calcite_full_type_bases_equal(
            Some("INTEGER"),
            false,
            Some("INTEGER"),
            true,
        ));
        assert!(!calcite_full_type_bases_equal(
            Some("INTEGER NOT NULL"),
            false,
            None,
            true,
        ));
    }
}
