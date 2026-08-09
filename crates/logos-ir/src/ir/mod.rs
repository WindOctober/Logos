use serde::de::{self, Deserializer};
use serde::ser::{SerializeStruct, Serializer};
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LogosIrFile {
    #[serde(default)]
    pub environment: SqlEnvironment,
    pub schema: Schema,
    pub queries: Vec<Query>,
}

/// Observable PostgreSQL text environment attested by the SQL frontend.
///
/// `Unspecified` is deliberately not an alias for the database default: it
/// keeps locale-sensitive lowering closed until the caller selects and the
/// frontend records an exact environment.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SqlEnvironment {
    #[serde(default)]
    pub default_collation: SqlDefaultCollation,
    #[serde(default)]
    pub character_classification: SqlCharacterClassification,
    #[serde(default)]
    pub locale_provider: SqlLocaleProvider,
    #[serde(default)]
    pub server_encoding: SqlServerEncoding,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
pub enum SqlDefaultCollation {
    #[default]
    #[serde(rename = "unspecified")]
    Unspecified,
    #[serde(rename = "C")]
    PostgresC,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
pub enum SqlCharacterClassification {
    #[default]
    #[serde(rename = "unspecified")]
    Unspecified,
    #[serde(rename = "C")]
    PostgresC,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
pub enum SqlLocaleProvider {
    #[default]
    #[serde(rename = "unspecified")]
    Unspecified,
    #[serde(rename = "libc")]
    Libc,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
pub enum SqlServerEncoding {
    #[default]
    #[serde(rename = "unspecified")]
    Unspecified,
    #[serde(rename = "UTF8")]
    Utf8,
}

impl SqlEnvironment {
    pub const fn postgres_utf8_c() -> Self {
        Self {
            default_collation: SqlDefaultCollation::PostgresC,
            character_classification: SqlCharacterClassification::PostgresC,
            locale_provider: SqlLocaleProvider::Libc,
            server_encoding: SqlServerEncoding::Utf8,
        }
    }

    pub const fn has_postgres_utf8_c_text_semantics(self) -> bool {
        matches!(self.default_collation, SqlDefaultCollation::PostgresC)
            && matches!(
                self.character_classification,
                SqlCharacterClassification::PostgresC
            )
            && matches!(self.locale_provider, SqlLocaleProvider::Libc)
            && matches!(self.server_encoding, SqlServerEncoding::Utf8)
    }

    pub const fn default_collation_label(self) -> &'static str {
        match self.default_collation {
            SqlDefaultCollation::Unspecified => "unspecified",
            SqlDefaultCollation::PostgresC => "C",
        }
    }

    pub const fn server_encoding_label(self) -> &'static str {
        match self.server_encoding {
            SqlServerEncoding::Unspecified => "unspecified",
            SqlServerEncoding::Utf8 => "UTF8",
        }
    }

    pub const fn character_classification_label(self) -> &'static str {
        match self.character_classification {
            SqlCharacterClassification::Unspecified => "unspecified",
            SqlCharacterClassification::PostgresC => "C",
        }
    }

    pub const fn locale_provider_label(self) -> &'static str {
        match self.locale_provider {
            SqlLocaleProvider::Unspecified => "unspecified",
            SqlLocaleProvider::Libc => "libc",
        }
    }

    pub fn try_parse(
        default_collation: &str,
        character_classification: &str,
        locale_provider: &str,
        server_encoding: &str,
    ) -> Result<Self, String> {
        let default_collation = match default_collation.trim() {
            value if value.eq_ignore_ascii_case("unspecified") => SqlDefaultCollation::Unspecified,
            value if value.eq_ignore_ascii_case("C") => SqlDefaultCollation::PostgresC,
            other => {
                return Err(format!(
                    "unsupported SQL default collation {other:?}; expected unspecified or C"
                ));
            }
        };
        let character_classification = match character_classification.trim() {
            value if value.eq_ignore_ascii_case("unspecified") => {
                SqlCharacterClassification::Unspecified
            }
            value if value.eq_ignore_ascii_case("C") => SqlCharacterClassification::PostgresC,
            other => {
                return Err(format!(
                    "unsupported SQL character classification {other:?}; expected unspecified or C"
                ));
            }
        };
        let locale_provider = match locale_provider.trim() {
            value if value.eq_ignore_ascii_case("unspecified") => SqlLocaleProvider::Unspecified,
            value if value.eq_ignore_ascii_case("libc") => SqlLocaleProvider::Libc,
            other => {
                return Err(format!(
                    "unsupported SQL locale provider {other:?}; expected unspecified or libc"
                ));
            }
        };
        let server_encoding = match server_encoding.trim() {
            value if value.eq_ignore_ascii_case("unspecified") => SqlServerEncoding::Unspecified,
            value if value.eq_ignore_ascii_case("UTF8") || value.eq_ignore_ascii_case("UTF-8") => {
                SqlServerEncoding::Utf8
            }
            other => {
                return Err(format!(
                    "unsupported SQL server encoding {other:?}; expected unspecified or UTF8"
                ));
            }
        };
        Ok(Self {
            default_collation,
            character_classification,
            locale_provider,
            server_encoding,
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Schema {
    pub tables: Vec<Table>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Table {
    pub name: String,
    pub columns: Vec<Column>,
    #[serde(default, skip_serializing_if = "TableConstraints::is_empty")]
    pub constraints: TableConstraints,
}

/// Integrity constraints declared by one base table.
///
/// These are kept separate from [`Column::nullable`]: Calcite's relational
/// row types describe expression nullability, while these declarations are
/// properties of stored base rows.  The conversion boundary validates that
/// both lists contain unique, known column names, `not_null` follows column
/// declaration order, and every primary-key column also appears in it.  The
/// order of `primary_key` itself is the key order declared by PostgreSQL.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TableConstraints {
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub not_null: Vec<String>,
    #[serde(
        default,
        skip_serializing_if = "Option::is_none",
        deserialize_with = "deserialize_nonempty_primary_key"
    )]
    pub primary_key: Option<Vec<String>>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub unique: Vec<UniqueConstraint>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub foreign_keys: Vec<ForeignKeyConstraint>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub checks: Vec<CheckConstraint>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub unique_indexes: Vec<UniqueIndexConstraint>,
}

impl TableConstraints {
    pub fn is_empty(&self) -> bool {
        self.not_null.is_empty()
            && self.primary_key.is_none()
            && self.unique.is_empty()
            && self.foreign_keys.is_empty()
            && self.checks.is_empty()
            && self.unique_indexes.is_empty()
    }
}

/// An ordinary PostgreSQL UNIQUE table constraint.  NULL values remain
/// distinct; the ordered column vector is the declared composite-key order.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct UniqueConstraint {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub name: Option<String>,
    pub columns: Vec<String>,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ForeignKeyMatch {
    #[default]
    Simple,
}

/// Snapshot-level referential integrity.  Referential actions are retained
/// as source metadata but are not transition semantics for read-only proofs.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ForeignKeyConstraint {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub name: Option<String>,
    pub columns: Vec<String>,
    pub referenced_table: String,
    pub referenced_columns: Vec<String>,
    #[serde(default)]
    pub match_type: ForeignKeyMatch,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub referential_actions: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CheckConstraint {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub name: Option<String>,
    pub expression: IntegrityPredicate,
    pub source_sql: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct UniqueIndexConstraint {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub name: Option<String>,
    pub terms: Vec<UniqueIndexTerm>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub predicate: Option<IntegrityPredicate>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub predicate_sql: Option<String>,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum IntegritySortDirection {
    #[default]
    Asc,
    Desc,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum IntegrityNullsOrder {
    First,
    Last,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct UniqueIndexTerm {
    pub expression: IntegrityValueExpr,
    pub source_sql: String,
    #[serde(default)]
    pub direction: IntegritySortDirection,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub nulls: Option<IntegrityNullsOrder>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub operator_class: Option<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum IntegrityComparison {
    Equal,
    NotEqual,
}

/// Closed, benchmark-scoped scalar syntax for CHECK and unique-index terms.
/// Every boundary rejects unknown variants; source SQL is retained separately
/// for diagnostics and PostgreSQL validation rendering.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case", tag = "kind", deny_unknown_fields)]
pub enum IntegrityValueExpr {
    Column { name: String },
    Literal { raw: String, ty: SqlType },
    Cast { expression: Box<Self>, ty: SqlType },
    Lower { expression: Box<Self> },
    Coalesce { arguments: Vec<Self> },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case", tag = "kind", deny_unknown_fields)]
pub enum IntegrityPredicate {
    Truth {
        expression: IntegrityValueExpr,
    },
    IsTrue {
        expression: IntegrityValueExpr,
    },
    IsNull {
        expression: IntegrityValueExpr,
    },
    IsNotNull {
        expression: IntegrityValueExpr,
    },
    Comparison {
        comparison: IntegrityComparison,
        left: IntegrityValueExpr,
        right: IntegrityValueExpr,
    },
    Any {
        comparison: IntegrityComparison,
        left: IntegrityValueExpr,
        values: Vec<IntegrityValueExpr>,
    },
    And {
        left: Box<Self>,
        right: Box<Self>,
    },
    Or {
        left: Box<Self>,
        right: Box<Self>,
    },
    Not {
        predicate: Box<Self>,
    },
}

fn deserialize_nonempty_primary_key<'de, D>(
    deserializer: D,
) -> std::result::Result<Option<Vec<String>>, D::Error>
where
    D: Deserializer<'de>,
{
    let primary_key = Option::<Vec<String>>::deserialize(deserializer)?;
    if primary_key.as_ref().is_some_and(Vec::is_empty) {
        return Err(de::Error::custom(
            "primaryKey must contain at least one column when present",
        ));
    }
    Ok(primary_key)
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct Column {
    pub name: String,
    pub ty: SqlType,
    pub nullable: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case", tag = "kind")]
pub enum SqlStringType {
    Text,
    Varchar { length: Option<u32> },
    Char { length: u32 },
    Bpchar,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SqlType {
    Any,
    Null,
    Integer,
    BigInt,
    Float,
    Double,
    Decimal {
        precision: Option<u32>,
        scale: Option<u32>,
    },
    String(SqlStringType),
    Boolean,
    Date,
    Time,
    Timestamp {
        precision: Option<u32>,
    },
    TimestampTz {
        precision: Option<u32>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
pub enum SqlTypeValidationError {
    #[error("decimal precision and scale must either both be absent or both be present")]
    DecimalTypmodPresence,
    #[error("decimal precision must be between 1 and 1000, found {precision}")]
    DecimalPrecision { precision: u32 },
    #[error("decimal scale must be between 0 and 1000, found {scale}")]
    DecimalScale { scale: u32 },
    #[error("{kind} length must be between 1 and 10485760, found {length}")]
    CharacterLength { kind: &'static str, length: u32 },
    #[error("{kind} precision must be between 0 and 6, found {precision}")]
    TimestampPrecision { kind: &'static str, precision: u32 },
    #[error("{kind} does not accept a scale typmod")]
    UnexpectedScale { kind: &'static str },
    #[error("{kind} does not accept precision or scale typmods")]
    UnexpectedTypmod { kind: &'static str },
    #[error("char requires a length typmod")]
    MissingCharacterLength,
}

impl SqlType {
    pub const MAX_DECIMAL_PRECISION: u32 = 1000;
    pub const MAX_DECIMAL_SCALE: u32 = 1000;
    pub const MAX_CHARACTER_LENGTH: u32 = 10_485_760;
    pub const MAX_TIMESTAMP_PRECISION: u32 = 6;

    pub fn validate(&self) -> std::result::Result<(), SqlTypeValidationError> {
        match self {
            Self::Decimal {
                precision: None,
                scale: None,
            } => Ok(()),
            Self::Decimal {
                precision: Some(precision),
                scale: Some(scale),
            } => {
                if !(1..=Self::MAX_DECIMAL_PRECISION).contains(precision) {
                    return Err(SqlTypeValidationError::DecimalPrecision {
                        precision: *precision,
                    });
                }
                if *scale > Self::MAX_DECIMAL_SCALE {
                    return Err(SqlTypeValidationError::DecimalScale { scale: *scale });
                }
                Ok(())
            }
            Self::Decimal { .. } => Err(SqlTypeValidationError::DecimalTypmodPresence),
            Self::String(SqlStringType::Varchar {
                length: Some(length),
            }) => Self::validate_character_length("varchar", *length),
            Self::String(SqlStringType::Char { length }) => {
                Self::validate_character_length("char", *length)
            }
            Self::Timestamp {
                precision: Some(precision),
            } => Self::validate_timestamp_precision("timestamp", *precision),
            Self::TimestampTz {
                precision: Some(precision),
            } => Self::validate_timestamp_precision("timestampTz", *precision),
            _ => Ok(()),
        }
    }

    fn validate_character_length(
        kind: &'static str,
        length: u32,
    ) -> std::result::Result<(), SqlTypeValidationError> {
        if !(1..=Self::MAX_CHARACTER_LENGTH).contains(&length) {
            return Err(SqlTypeValidationError::CharacterLength { kind, length });
        }
        Ok(())
    }

    fn validate_timestamp_precision(
        kind: &'static str,
        precision: u32,
    ) -> std::result::Result<(), SqlTypeValidationError> {
        if precision > Self::MAX_TIMESTAMP_PRECISION {
            return Err(SqlTypeValidationError::TimestampPrecision { kind, precision });
        }
        Ok(())
    }

    pub fn try_decimal(
        precision: Option<u32>,
        scale: Option<u32>,
    ) -> std::result::Result<Self, SqlTypeValidationError> {
        let ty = Self::Decimal { precision, scale };
        ty.validate()?;
        Ok(ty)
    }

    /// Construct a validated decimal type for trusted, already-checked values.
    ///
    /// Prefer [`Self::try_decimal`] when either typmod comes from input.
    #[track_caller]
    pub fn decimal(precision: Option<u32>, scale: Option<u32>) -> Self {
        Self::try_decimal(precision, scale)
            .unwrap_or_else(|error| panic!("invalid decimal SQL type: {error}"))
    }

    pub fn try_timestamp(
        precision: Option<u32>,
    ) -> std::result::Result<Self, SqlTypeValidationError> {
        let ty = Self::Timestamp { precision };
        ty.validate()?;
        Ok(ty)
    }

    /// Construct a validated timestamp type for trusted, already-checked values.
    ///
    /// Prefer [`Self::try_timestamp`] when precision comes from input.
    #[track_caller]
    pub fn timestamp(precision: Option<u32>) -> Self {
        Self::try_timestamp(precision)
            .unwrap_or_else(|error| panic!("invalid timestamp SQL type: {error}"))
    }

    pub fn try_timestamptz(
        precision: Option<u32>,
    ) -> std::result::Result<Self, SqlTypeValidationError> {
        let ty = Self::TimestampTz { precision };
        ty.validate()?;
        Ok(ty)
    }

    /// Construct a validated timestamp-with-time-zone type for trusted values.
    ///
    /// Prefer [`Self::try_timestamptz`] when precision comes from input.
    #[track_caller]
    pub fn timestamptz(precision: Option<u32>) -> Self {
        Self::try_timestamptz(precision)
            .unwrap_or_else(|error| panic!("invalid timestamptz SQL type: {error}"))
    }

    pub fn text() -> Self {
        Self::String(SqlStringType::Text)
    }

    pub fn try_varchar(length: Option<u32>) -> std::result::Result<Self, SqlTypeValidationError> {
        let ty = Self::String(SqlStringType::Varchar { length });
        ty.validate()?;
        Ok(ty)
    }

    /// Construct a validated VARCHAR type for a trusted, already-checked length.
    ///
    /// Prefer [`Self::try_varchar`] when length comes from input.
    #[track_caller]
    pub fn varchar(length: Option<u32>) -> Self {
        Self::try_varchar(length)
            .unwrap_or_else(|error| panic!("invalid varchar SQL type: {error}"))
    }

    pub fn try_character(length: u32) -> std::result::Result<Self, SqlTypeValidationError> {
        let ty = Self::String(SqlStringType::Char { length });
        ty.validate()?;
        Ok(ty)
    }

    /// Construct a validated CHAR type for a trusted, already-checked length.
    ///
    /// Prefer [`Self::try_character`] when length comes from input.
    #[track_caller]
    pub fn character(length: u32) -> Self {
        Self::try_character(length).unwrap_or_else(|error| panic!("invalid char SQL type: {error}"))
    }

    pub fn bpchar() -> Self {
        Self::String(SqlStringType::Bpchar)
    }

    pub fn try_with_typmod(
        self,
        precision: Option<u32>,
        scale: Option<u32>,
    ) -> std::result::Result<Self, SqlTypeValidationError> {
        match self {
            Self::Decimal { .. } => Self::try_decimal(precision, scale),
            Self::Timestamp { .. } => {
                if scale.is_some() {
                    return Err(SqlTypeValidationError::UnexpectedScale { kind: "timestamp" });
                }
                Self::try_timestamp(precision)
            }
            Self::TimestampTz { .. } => {
                if scale.is_some() {
                    return Err(SqlTypeValidationError::UnexpectedScale {
                        kind: "timestampTz",
                    });
                }
                Self::try_timestamptz(precision)
            }
            Self::String(SqlStringType::Varchar { .. }) => {
                if scale.is_some() {
                    return Err(SqlTypeValidationError::UnexpectedScale { kind: "varchar" });
                }
                Self::try_varchar(precision)
            }
            Self::String(SqlStringType::Char { .. }) => {
                if scale.is_some() {
                    return Err(SqlTypeValidationError::UnexpectedScale { kind: "char" });
                }
                Self::try_character(
                    precision.ok_or(SqlTypeValidationError::MissingCharacterLength)?,
                )
            }
            other if precision.is_none() && scale.is_none() => {
                other.validate()?;
                Ok(other)
            }
            other => Err(SqlTypeValidationError::UnexpectedTypmod {
                kind: other.kind_name(),
            }),
        }
    }

    pub fn precision(&self) -> Option<u32> {
        match self {
            Self::Decimal { precision, .. }
            | Self::Timestamp { precision }
            | Self::TimestampTz { precision } => *precision,
            _ => None,
        }
    }

    pub fn scale(&self) -> Option<u32> {
        match self {
            Self::Decimal { scale, .. } => *scale,
            _ => None,
        }
    }

    pub fn length(&self) -> Option<u32> {
        match self {
            Self::String(SqlStringType::Varchar { length }) => *length,
            Self::String(SqlStringType::Char { length }) => Some(*length),
            Self::String(SqlStringType::Bpchar) => None,
            _ => None,
        }
    }

    fn kind_name(&self) -> &'static str {
        match self {
            Self::Any => "any",
            Self::Null => "null",
            Self::Integer => "integer",
            Self::BigInt => "bigInt",
            Self::Float => "float",
            Self::Double => "double",
            Self::Decimal { .. } => "decimal",
            Self::String(SqlStringType::Text) => "text",
            Self::String(SqlStringType::Varchar { .. }) => "varchar",
            Self::String(SqlStringType::Char { .. }) => "char",
            Self::String(SqlStringType::Bpchar) => "bpchar",
            Self::Boolean => "boolean",
            Self::Date => "date",
            Self::Time => "time",
            Self::Timestamp { .. } => "timestamp",
            Self::TimestampTz { .. } => "timestampTz",
        }
    }

    fn from_typmodless_name(kind: &str) -> Option<Self> {
        match kind {
            "any" => Some(Self::Any),
            "null" => Some(Self::Null),
            "integer" => Some(Self::Integer),
            "bigInt" => Some(Self::BigInt),
            "float" => Some(Self::Float),
            "double" => Some(Self::Double),
            "decimal" => Some(Self::Decimal {
                precision: None,
                scale: None,
            }),
            "text" => Some(Self::text()),
            "varchar" => Some(Self::varchar(None)),
            "bpchar" => Some(Self::bpchar()),
            "boolean" => Some(Self::Boolean),
            "date" => Some(Self::Date),
            "time" => Some(Self::Time),
            "timestamp" => Some(Self::Timestamp { precision: None }),
            "timestampTz" => Some(Self::TimestampTz { precision: None }),
            _ => None,
        }
    }

    fn from_canonical_typmod(
        kind: &str,
        precision: Option<Option<u32>>,
        scale: Option<Option<u32>>,
        length: Option<Option<u32>>,
    ) -> Option<Self> {
        match (kind, precision, scale, length) {
            ("decimal", Some(Some(precision)), Some(Some(scale)), None) => {
                Self::try_decimal(Some(precision), Some(scale)).ok()
            }
            ("timestamp", Some(Some(precision)), None, None) => {
                Self::try_timestamp(Some(precision)).ok()
            }
            ("timestampTz", Some(Some(precision)), None, None) => {
                Self::try_timestamptz(Some(precision)).ok()
            }
            ("varchar", None, None, Some(Some(length))) => Self::try_varchar(Some(length)).ok(),
            ("char", None, None, Some(Some(length))) => Self::try_character(length).ok(),
            _ => None,
        }
    }

    fn has_typmod(&self) -> bool {
        match self {
            Self::Decimal { precision, scale } => precision.is_some() || scale.is_some(),
            Self::Timestamp { precision } | Self::TimestampTz { precision } => precision.is_some(),
            Self::String(SqlStringType::Varchar { length }) => length.is_some(),
            Self::String(SqlStringType::Char { .. }) => true,
            Self::String(SqlStringType::Bpchar) => false,
            _ => false,
        }
    }
}

fn deserialize_present_optional_u32<'de, D>(
    deserializer: D,
) -> std::result::Result<Option<Option<u32>>, D::Error>
where
    D: Deserializer<'de>,
{
    Option::<u32>::deserialize(deserializer).map(Some)
}

impl Serialize for SqlType {
    fn serialize<S>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.validate().map_err(serde::ser::Error::custom)?;
        if !self.has_typmod() {
            return serializer.serialize_str(self.kind_name());
        }

        let mut state = serializer.serialize_struct("SqlType", 4)?;
        state.serialize_field("kind", self.kind_name())?;
        if let Some(precision) = self.precision() {
            state.serialize_field("precision", &precision)?;
        }
        if let Some(scale) = self.scale() {
            state.serialize_field("scale", &scale)?;
        }
        if let Some(length) = self.length() {
            state.serialize_field("length", &length)?;
        }
        state.end()
    }
}

impl<'de> Deserialize<'de> for SqlType {
    fn deserialize<D>(deserializer: D) -> std::result::Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        #[derive(Deserialize)]
        #[serde(deny_unknown_fields)]
        struct SqlTypeTypmodWire {
            kind: String,
            #[serde(default, deserialize_with = "deserialize_present_optional_u32")]
            precision: Option<Option<u32>>,
            #[serde(default, deserialize_with = "deserialize_present_optional_u32")]
            scale: Option<Option<u32>>,
            #[serde(default, deserialize_with = "deserialize_present_optional_u32")]
            length: Option<Option<u32>>,
        }

        #[derive(Deserialize)]
        #[serde(untagged)]
        enum SqlTypeWire {
            Name(String),
            Typmod(SqlTypeTypmodWire),
        }

        let ty =
            match SqlTypeWire::deserialize(deserializer)? {
                SqlTypeWire::Name(kind) => SqlType::from_typmodless_name(&kind)
                    .ok_or_else(|| de::Error::custom(format!("unsupported SQL type `{kind}`"))),
                SqlTypeWire::Typmod(SqlTypeTypmodWire {
                    kind,
                    precision,
                    scale,
                    length,
                }) => SqlType::from_canonical_typmod(&kind, precision, scale, length).ok_or_else(
                    || de::Error::custom(format!("noncanonical SQL type object for `{kind}`")),
                ),
            }?;
        ty.validate().map_err(de::Error::custom)?;
        Ok(ty)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct Query {
    pub source_sql: Option<String>,
    pub rel: RelExpr,
    pub analysis_errors: Vec<QueryAnalysisError>,
}

impl Query {
    pub fn output(&self) -> &[Column] {
        self.rel.output()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct QueryBinding {
    /// Opaque statement-local identity. Consumers must not infer SQL names or
    /// scopes from this value.
    pub id: String,
    /// Original lexical name retained only for diagnostics.
    pub source_name: String,
    /// The complete relation-valued definition evaluated once before its
    /// references are scanned.
    pub rel: RelExpr,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", tag = "kind", deny_unknown_fields)]
pub enum RelExpr {
    /// Query-local relation definitions reconstructed from exact lexical CTE
    /// provenance. This is a query-program wrapper, not a row-level relational
    /// algebra operator; lowering removes it before producing FormalSQL terms.
    Bindings {
        bindings: Vec<QueryBinding>,
        body: Box<RelExpr>,
        output: Vec<Column>,
    },
    TableScan {
        table: Vec<String>,
        output: Vec<Column>,
    },
    /// Reference to one query-local relation binding. This is a relation
    /// source leaf, not a relational algebra operator and not a base table.
    QueryRef {
        binding: String,
        output: Vec<Column>,
    },
    Project {
        input: Box<RelExpr>,
        exprs: Vec<ScalarExpr>,
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        correlations: Vec<CorrelationBinding>,
        output: Vec<Column>,
    },
    Filter {
        input: Box<RelExpr>,
        predicate: ScalarExpr,
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        correlations: Vec<CorrelationBinding>,
        output: Vec<Column>,
    },
    /// A source-attested native PostgreSQL HAVING Filter immediately over its
    /// Aggregate. All registered Aggrefs are finalized before the
    /// qualification is tested.
    NativeHaving {
        input: Box<RelExpr>,
        predicate: ScalarExpr,
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        correlations: Vec<CorrelationBinding>,
        output: Vec<Column>,
    },
    Join {
        left: Box<RelExpr>,
        right: Box<RelExpr>,
        join_type: JoinType,
        condition: ScalarExpr,
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        correlations: Vec<CorrelationBinding>,
        output: Vec<Column>,
    },
    Aggregate {
        input: Box<RelExpr>,
        group_keys: Vec<usize>,
        grouping_sets: Vec<Vec<usize>>,
        agg_calls: Vec<AggregateCall>,
        output: Vec<Column>,
    },
    /// Source-attested SELECT DISTINCT.  This is not represented as a
    /// grouping Aggregate because EXISTS may discard its target computation
    /// while a genuine GROUP BY still has aggregate/grouping obligations.
    Distinct {
        input: Box<RelExpr>,
        output: Vec<Column>,
    },
    Sort {
        input: Box<RelExpr>,
        collation: Vec<SortKey>,
        fetch: Option<ScalarExpr>,
        offset: Option<Box<ScalarExpr>>,
        output: Vec<Column>,
    },
    Set {
        op: SetOp,
        all: bool,
        inputs: Vec<RelExpr>,
        output: Vec<Column>,
    },
    Values {
        rows: Vec<Vec<ScalarExpr>>,
        output: Vec<Column>,
    },
}

impl RelExpr {
    pub fn output(&self) -> &[Column] {
        match self {
            RelExpr::Bindings { output, .. }
            | RelExpr::TableScan { output, .. }
            | RelExpr::QueryRef { output, .. }
            | RelExpr::Project { output, .. }
            | RelExpr::Filter { output, .. }
            | RelExpr::NativeHaving { output, .. }
            | RelExpr::Join { output, .. }
            | RelExpr::Aggregate { output, .. }
            | RelExpr::Distinct { output, .. }
            | RelExpr::Sort { output, .. }
            | RelExpr::Set { output, .. }
            | RelExpr::Values { output, .. } => output,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct CorrelationBinding {
    pub correlation: String,
    pub output: Vec<Column>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum JoinType {
    Inner,
    Left,
    Right,
    Full,
    Semi,
    Anti,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum SetOp {
    Union,
    Intersect,
    Except,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SortKey {
    pub field_index: usize,
    pub direction: SortDirection,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub null_direction: Option<SortNullDirection>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum SortDirection {
    Ascending,
    Descending,
    StrictlyAscending,
    StrictlyDescending,
    Clustered,
}

impl SortDirection {
    pub fn default_null_direction(self) -> Option<SortNullDirection> {
        match self {
            SortDirection::Ascending | SortDirection::StrictlyAscending => {
                Some(SortNullDirection::Last)
            }
            SortDirection::Descending | SortDirection::StrictlyDescending => {
                Some(SortNullDirection::First)
            }
            SortDirection::Clustered => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum SortNullDirection {
    First,
    Last,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AggregateCall {
    pub raw: String,
    pub function: String,
    pub distinct: bool,
    #[serde(default, skip_serializing_if = "AggregateModifiers::is_wire_empty")]
    pub modifiers: AggregateModifiers,
    pub args: Vec<ScalarExpr>,
    pub filter: Option<ScalarExpr>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AggregateModifiers {
    #[serde(default)]
    pub approximate: bool,
    #[serde(default)]
    pub ignore_nulls: bool,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub distinct_keys: Vec<usize>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub collation: Vec<SortKey>,
    /// Exact source-AST provenance for the aggregate call.  This is not a
    /// semantic modifier: it is carried solely so a downstream PostgreSQL
    /// analysis-error recognizer can bind Calcite's typed AggregateCall to
    /// the one source SqlCall that produced it.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub source: Option<ScalarSourceProvenance>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub source_distinct: Option<bool>,
    /// Query-block-local authority for the exact source ROLLUP/GROUPING SETS
    /// expansion that owns this aggregate call. This is metadata, not an SQL
    /// aggregate modifier.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub source_grouping: Option<SourceGroupingProvenance>,
}

impl AggregateModifiers {
    pub fn is_empty(&self) -> bool {
        !self.approximate
            && !self.ignore_nulls
            && self.distinct_keys.is_empty()
            && self.collation.is_empty()
    }

    pub fn has_semantic_modifiers(&self) -> bool {
        !self.is_empty()
    }

    fn is_wire_empty(&self) -> bool {
        self.is_empty()
            && self.source.is_none()
            && self.source_distinct.is_none()
            && self.source_grouping.is_none()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct SourceGroupingProvenance {
    pub kind: String,
    pub query_block_id: String,
    pub source_select_node_id: String,
    pub source_select_sql: String,
    pub source_group_sql: String,
    pub group_indexes: Vec<usize>,
    pub grouping_sets: Vec<Vec<usize>>,
    pub source_has_where: bool,
    pub source_has_having: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ScalarExpr {
    pub raw: String,
    pub parsed: ScalarAst,
    /// A positional mirror of Calcite's Rex tree annotated with nodes from
    /// the independently parsed source SQL AST.  Missing entries are
    /// deliberate: downstream consumers must fail closed when an exact node
    /// association was unavailable.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub source: Option<ScalarSourceProvenance>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ScalarSourceProvenance {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub sql: Option<String>,
    /// Converter-validated parser-position identity in the original SQL
    /// statement.  `node_id` and `text` are either both present or both
    /// absent; source echoes without this pair are not exact provenance.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub node_id: Option<String>,
    /// Byte-exact original-statement fragment selected by `node_id`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub text: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub kind: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub operator: Option<String>,
    /// Converter-validated ownership of the complete scalar root by one
    /// independently parsed relational source clause. This is deliberately
    /// root-only: operand provenance never inherits relational authority.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub clause_ownership: Option<ScalarSourceClauseOwnership>,
    /// Positions correspond exactly to the owning RexNode's operands.  A
    /// null element means that Calcite had an operand but the wrapper could
    /// not associate it with one exact source node.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub operands: Vec<Option<ScalarSourceProvenance>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum SourceClauseKind {
    Where,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ScalarSourceClauseOwnership {
    pub kind: SourceClauseKind,
    pub query_block_id: String,
    pub source_node_id: String,
    pub source_sql: String,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub analysis_errors: Vec<SourceAnalysisErrorProvenance>,
}

/// Converter-validated evidence that Calcite changed an ill-typed
/// PostgreSQL source operator into a different, well-typed Rex expression.
/// The path is relative to the complete owned source-clause scalar root; it
/// is not meaningful without the enclosing [`ScalarSourceClauseOwnership`].
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", tag = "kind", deny_unknown_fields)]
pub enum SourceAnalysisErrorProvenance {
    PostgresBooleanIntegerEqualityUndefinedFunction {
        rex_path: String,
        identifier_operand: usize,
        literal_operand: usize,
        generated_comparison_sql: String,
        input_index: usize,
        base_table: Vec<String>,
        table_field_index: usize,
        base_field_name: String,
        source_literal_canonical_value: String,
        generated_literal_canonical_value: String,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", tag = "kind", deny_unknown_fields)]
pub enum ScalarAst {
    InputRef {
        index: usize,
    },
    CorrelatedRef {
        correlation: String,
        field: String,
        #[serde(skip_serializing_if = "Option::is_none")]
        index: Option<usize>,
        ty: SqlType,
    },
    Literal {
        raw: String,
    },
    Call {
        operator: String,
        op: ScalarOp,
        args: Vec<ScalarAst>,
    },
    TypeAnnotation {
        expr: Box<ScalarAst>,
        ty: String,
    },
    Flag {
        name: String,
    },
    Window {
        parsed: WindowAst,
    },
    RelSubquery {
        rel: Box<RelExpr>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct WindowAst {
    pub function: String,
    pub args: Vec<ScalarAst>,
    pub partition_by: Vec<ScalarAst>,
    pub order_by: Vec<WindowOrderKey>,
    #[serde(default)]
    pub distinct: bool,
    #[serde(default)]
    pub ignore_nulls: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub exclude: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub frame: Option<WindowFrameAst>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct WindowFrameAst {
    pub units: WindowFrameUnits,
    pub start: WindowFrameBoundAst,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub end: Option<WindowFrameBoundAst>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum WindowFrameUnits {
    Rows,
    Range,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "camelCase")]
pub enum WindowFrameBoundAst {
    UnboundedPreceding,
    OffsetPreceding { raw: String, expr: Box<ScalarAst> },
    CurrentRow,
    OffsetFollowing { raw: String, expr: Box<ScalarAst> },
    UnboundedFollowing,
}

impl WindowFrameAst {
    /// PostgreSQL validates frame-bound kinds in this order.  Equal kinds are
    /// permitted; the offset values themselves are evaluated later.
    pub fn is_valid_postgres(&self) -> bool {
        if matches!(self.start, WindowFrameBoundAst::UnboundedFollowing) {
            return false;
        }
        let Some(end) = self.end.as_ref() else {
            return matches!(
                self.start,
                WindowFrameBoundAst::UnboundedPreceding
                    | WindowFrameBoundAst::OffsetPreceding { .. }
                    | WindowFrameBoundAst::CurrentRow
            );
        };
        !matches!(end, WindowFrameBoundAst::UnboundedPreceding)
            && self.start.order_rank() <= end.order_rank()
    }

    pub fn offset_exprs(&self) -> impl Iterator<Item = &ScalarAst> {
        self.start
            .offset_expr()
            .into_iter()
            .chain(self.end.as_ref().and_then(WindowFrameBoundAst::offset_expr))
    }

    pub fn to_calcite_string(&self) -> String {
        let units = match self.units {
            WindowFrameUnits::Rows => "ROWS",
            WindowFrameUnits::Range => "RANGE",
        };
        match &self.end {
            Some(end) => format!(
                "{units} BETWEEN {} AND {}",
                self.start.to_calcite_string(),
                end.to_calcite_string()
            ),
            None => format!("{units} {}", self.start.to_calcite_string()),
        }
    }
}

impl WindowFrameBoundAst {
    fn order_rank(&self) -> u8 {
        match self {
            Self::UnboundedPreceding => 0,
            Self::OffsetPreceding { .. } => 1,
            Self::CurrentRow => 2,
            Self::OffsetFollowing { .. } => 3,
            Self::UnboundedFollowing => 4,
        }
    }

    pub fn offset_expr(&self) -> Option<&ScalarAst> {
        match self {
            Self::OffsetPreceding { expr, .. } | Self::OffsetFollowing { expr, .. } => Some(expr),
            Self::UnboundedPreceding | Self::CurrentRow | Self::UnboundedFollowing => None,
        }
    }

    pub fn to_calcite_string(&self) -> String {
        match self {
            Self::UnboundedPreceding => "UNBOUNDED PRECEDING".to_owned(),
            Self::OffsetPreceding { raw, .. } => format!("{raw} PRECEDING"),
            Self::CurrentRow => "CURRENT ROW".to_owned(),
            Self::OffsetFollowing { raw, .. } => format!("{raw} FOLLOWING"),
            Self::UnboundedFollowing => "UNBOUNDED FOLLOWING".to_owned(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct WindowOrderKey {
    pub expr: ScalarAst,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub direction: Option<SortDirection>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub null_direction: Option<SortNullDirection>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum ScalarOp {
    Eq,
    NotEq,
    Lt,
    Lte,
    Gt,
    Gte,
    And,
    Or,
    Not,
    IsNull,
    IsNotNull,
    IsTrue,
    IsNotTrue,
    IsFalse,
    IsNotFalse,
    IsNotDistinctFrom,
    Like,
    Plus,
    Minus,
    Multiply,
    Divide,
    StringConcat,
    Cast,
    Case,
    Lower,
    Upper,
    Substring,
    Exp,
    Power,
    Extract,
    In,
    Exists,
    ScalarQuery,
    Other(String),
}

impl ScalarOp {
    /// Every binary comparison in the shared IR, including PostgreSQL's
    /// NULL-safe equality predicate.
    pub fn is_comparison(&self) -> bool {
        self.is_ordinary_comparison() || matches!(self, Self::IsNotDistinctFrom)
    }

    /// Ordinary SQL equality/inequality/ordering comparisons.  This excludes
    /// `IS NOT DISTINCT FROM`, whose NULL behavior requires separate gates.
    pub fn is_ordinary_comparison(&self) -> bool {
        matches!(
            self,
            Self::Eq | Self::NotEq | Self::Lt | Self::Lte | Self::Gt | Self::Gte
        )
    }

    pub fn is_ordering_comparison(&self) -> bool {
        matches!(self, Self::Lt | Self::Lte | Self::Gt | Self::Gte)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub enum QueryAnalysisError {
    /// Independently parsed source evidence that PostgreSQL resolves a
    /// nested use of a SELECT output alias as an input-column reference and
    /// therefore reports SQLSTATE 42703. The frontend emits this only after
    /// proving that the same name is absent from the query block's input
    /// scope; downstream consumers retain the complete lexical identity.
    PostgresOrderByAliasExpressionUndefinedColumn {
        sql_state: String,
        query_block_id: String,
        source_order_item_node_id: String,
        source_order_item_sql: String,
        output_alias: String,
    },
    /// Independently parsed source evidence that one unqualified SELECT
    /// identifier names at least two columns in the public namespace of its
    /// sole derived-table input. PostgreSQL rejects the query during parse
    /// analysis with SQLSTATE 42702; Calcite's arbitrary chosen InputRef is
    /// retained only as dead typed metadata and never becomes query meaning.
    PostgresAmbiguousDerivedOutputColumn {
        sql_state: String,
        query_block_id: String,
        source_identifier_node_id: String,
        source_identifier_sql: String,
        source_relation_node_id: String,
        source_relation_sql: String,
        identifier_name: String,
        identifier_quoted: bool,
        duplicate_count: usize,
        matching_outputs: Vec<PostgresAmbiguousColumnOutputEvidence>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct PostgresAmbiguousColumnOutputEvidence {
    pub output_index: usize,
    pub output_name: String,
    pub source_output_item_node_id: String,
    pub source_output_item_sql: String,
    pub source_origin_relation_node_id: String,
    pub source_origin_relation_sql: String,
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn scalar_comparison_families_preserve_null_safe_and_ordering_boundaries() {
        assert!(ScalarOp::Eq.is_comparison());
        assert!(ScalarOp::Eq.is_ordinary_comparison());
        assert!(!ScalarOp::Eq.is_ordering_comparison());

        assert!(ScalarOp::Lt.is_comparison());
        assert!(ScalarOp::Lt.is_ordinary_comparison());
        assert!(ScalarOp::Lt.is_ordering_comparison());

        assert!(ScalarOp::IsNotDistinctFrom.is_comparison());
        assert!(!ScalarOp::IsNotDistinctFrom.is_ordinary_comparison());
        assert!(!ScalarOp::IsNotDistinctFrom.is_ordering_comparison());

        assert!(!ScalarOp::And.is_comparison());
    }

    #[test]
    fn postgres_utf8_libc_c_environment_round_trips_all_observable_dimensions() {
        let environment = SqlEnvironment::postgres_utf8_c();
        let encoded = serde_json::to_value(environment).unwrap();
        assert_eq!(
            encoded,
            json!({
                "defaultCollation": "C",
                "characterClassification": "C",
                "localeProvider": "libc",
                "serverEncoding": "UTF8"
            })
        );
        assert_eq!(
            serde_json::from_value::<SqlEnvironment>(encoded).unwrap(),
            environment
        );
        assert!(environment.has_postgres_utf8_c_text_semantics());
    }

    #[test]
    fn incomplete_environment_stays_fail_closed() {
        let environment: SqlEnvironment = serde_json::from_value(json!({
            "defaultCollation": "C",
            "serverEncoding": "UTF8"
        }))
        .unwrap();
        assert!(!environment.has_postgres_utf8_c_text_semantics());
    }

    #[test]
    fn parses_only_the_exact_supported_locale_contract() {
        assert_eq!(
            SqlEnvironment::try_parse("C", "C", "libc", "UTF-8").unwrap(),
            SqlEnvironment::postgres_utf8_c()
        );
        assert!(SqlEnvironment::try_parse("C", "C.UTF-8", "libc", "UTF8").is_err());
        assert!(SqlEnvironment::try_parse("C", "C", "icu", "UTF8").is_err());
    }

    #[test]
    fn table_json_defaults_and_omits_empty_constraints() {
        let table: Table = serde_json::from_value(json!({
            "name": "t",
            "columns": []
        }))
        .unwrap();

        assert!(table.constraints.is_empty());
        assert_eq!(
            serde_json::to_value(table).unwrap(),
            json!({"name": "t", "columns": []})
        );
    }

    #[test]
    fn table_constraints_round_trip_with_postgres_key_order() {
        let table = Table {
            name: "t".to_owned(),
            columns: vec![],
            constraints: TableConstraints {
                not_null: vec!["a".to_owned(), "b".to_owned()],
                primary_key: Some(vec!["b".to_owned(), "a".to_owned()]),
                ..TableConstraints::default()
            },
        };
        let value = serde_json::to_value(&table).unwrap();

        assert_eq!(
            value,
            json!({
                "name": "t",
                "columns": [],
                "constraints": {
                    "notNull": ["a", "b"],
                    "primaryKey": ["b", "a"]
                }
            })
        );
        assert_eq!(serde_json::from_value::<Table>(value).unwrap(), table);
    }

    #[test]
    fn boxed_sort_offset_preserves_the_rel_expr_json_shape() {
        let rel = RelExpr::Sort {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: Vec::new(),
            }),
            collation: Vec::new(),
            fetch: None,
            offset: Some(Box::new(ScalarExpr {
                raw: "2".to_owned(),
                parsed: ScalarAst::Literal {
                    raw: "2".to_owned(),
                },
                source: None,
            })),
            output: Vec::new(),
        };
        let value = serde_json::to_value(&rel).unwrap();

        assert_eq!(
            value,
            json!({
                "kind": "sort",
                "input": {"kind": "tableScan", "table": ["t"], "output": []},
                "collation": [],
                "fetch": null,
                "offset": {"raw": "2", "parsed": {"kind": "literal", "raw": "2"}},
                "output": []
            })
        );
        assert_eq!(serde_json::from_value::<RelExpr>(value).unwrap(), rel);
    }

    #[test]
    fn rejects_explicitly_empty_primary_key_in_logos_ir_json() {
        assert!(
            serde_json::from_value::<Table>(json!({
                "name": "t",
                "columns": [],
                "constraints": {"primaryKey": []}
            }))
            .is_err()
        );
    }

    #[test]
    fn rejects_obsolete_column_level_typmod_fields() {
        assert!(
            serde_json::from_value::<Column>(json!({
                "name": "amount",
                "ty": "decimal",
                "nullable": true,
                "precision": 10,
                "scale": 2
            }))
            .is_err()
        );
    }

    #[test]
    fn rejects_retired_query_output_field() {
        assert!(
            serde_json::from_value::<Query>(json!({
                "sourceSql": null,
                "rel": {
                    "kind": "values",
                    "rows": [],
                    "output": []
                },
                "analysisErrors": [],
                "output": []
            }))
            .is_err()
        );
    }

    #[test]
    fn rejects_retired_query_features_field() {
        assert!(
            serde_json::from_value::<Query>(json!({
                "sourceSql": null,
                "rel": {
                    "kind": "values",
                    "rows": [],
                    "output": []
                },
                "analysisErrors": [],
                "features": []
            }))
            .is_err()
        );
    }

    #[test]
    fn query_analysis_errors_round_trip_through_the_authoritative_field() {
        let query = Query {
            source_sql: Some("select 1 as x order by x + 1".to_owned()),
            rel: RelExpr::Values {
                rows: Vec::new(),
                output: Vec::new(),
            },
            analysis_errors: vec![
                QueryAnalysisError::PostgresOrderByAliasExpressionUndefinedColumn {
                    sql_state: "42703".to_owned(),
                    query_block_id: "1:1-1:13".to_owned(),
                    source_order_item_node_id: "1:24-1:28".to_owned(),
                    source_order_item_sql: "x + 1".to_owned(),
                    output_alias: "x".to_owned(),
                },
            ],
        };

        let value = serde_json::to_value(&query).unwrap();
        assert!(value.get("analysisErrors").is_some());
        assert!(value.get("features").is_none());
        assert_eq!(serde_json::from_value::<Query>(value).unwrap(), query);

        let mut error_value = serde_json::to_value(&query.analysis_errors[0]).unwrap();
        error_value
            .as_object_mut()
            .unwrap()
            .values_mut()
            .next()
            .unwrap()
            .as_object_mut()
            .unwrap()
            .insert("unexpected".to_owned(), json!(true));
        assert!(serde_json::from_value::<QueryAnalysisError>(error_value).is_err());
    }

    #[test]
    fn rejects_retired_values_tuples_alongside_authoritative_rows() {
        assert!(
            serde_json::from_value::<RelExpr>(json!({
                "kind": "values",
                "rows": [],
                "tuples": {"kind": "rows", "rows": []},
                "output": []
            }))
            .is_err()
        );
    }

    #[test]
    fn rejects_retired_scalar_class_field() {
        assert!(
            serde_json::from_value::<ScalarExpr>(json!({
                "raw": "$0",
                "parsed": {"kind": "inputRef", "index": 0},
                "class": "inputRef"
            }))
            .is_err()
        );
    }

    #[test]
    fn rejects_retired_source_provenance_echoes() {
        let grouping = SourceGroupingProvenance {
            kind: "ROLLUP".to_owned(),
            query_block_id: "1:1-1:40".to_owned(),
            source_select_node_id: "1:1-1:40".to_owned(),
            source_select_sql: "SELECT a FROM t GROUP BY ROLLUP(a)".to_owned(),
            source_group_sql: "ROLLUP(a)".to_owned(),
            group_indexes: vec![0],
            grouping_sets: vec![vec![0], Vec::new()],
            source_has_where: false,
            source_has_having: false,
        };
        let mut grouping_value = serde_json::to_value(grouping).unwrap();
        grouping_value
            .as_object_mut()
            .unwrap()
            .insert("sourceIsRootQueryBlock".to_owned(), json!(true));
        assert!(serde_json::from_value::<SourceGroupingProvenance>(grouping_value).is_err());

        let marker =
            SourceAnalysisErrorProvenance::PostgresBooleanIntegerEqualityUndefinedFunction {
                rex_path: "$".to_owned(),
                identifier_operand: 0,
                literal_operand: 1,
                generated_comparison_sql: "=($0, false)".to_owned(),
                input_index: 0,
                base_table: vec!["t".to_owned()],
                table_field_index: 0,
                base_field_name: "a".to_owned(),
                source_literal_canonical_value: "0".to_owned(),
                generated_literal_canonical_value: "false".to_owned(),
            };
        let mut marker_value = serde_json::to_value(marker).unwrap();
        marker_value
            .as_object_mut()
            .unwrap()
            .insert("sourceComparisonSql".to_owned(), json!("a = 0"));
        assert!(serde_json::from_value::<SourceAnalysisErrorProvenance>(marker_value).is_err());
    }

    #[test]
    fn rejects_retired_window_raw_and_structured_fields() {
        let window = json!({
            "kind": "window",
            "parsed": {
                "function": "ROW_NUMBER",
                "args": [],
                "partitionBy": [],
                "orderBy": []
            }
        });
        assert!(serde_json::from_value::<ScalarAst>(window.clone()).is_ok());

        let mut with_raw = window.clone();
        with_raw["raw"] = json!("ROW_NUMBER() OVER ()");
        assert!(serde_json::from_value::<ScalarAst>(with_raw).is_err());

        let mut with_structured = window;
        with_structured["structured"] = json!(true);
        assert!(serde_json::from_value::<ScalarAst>(with_structured).is_err());
    }

    #[test]
    fn serializes_typmod_as_sql_type_not_column_fields() {
        let value = serde_json::to_value(Column {
            name: "amount".to_owned(),
            ty: SqlType::decimal(Some(10), Some(2)),
            nullable: true,
        })
        .unwrap();

        assert_eq!(
            value,
            json!({
                "name": "amount",
                "ty": {
                    "kind": "decimal",
                    "precision": 10,
                    "scale": 2
                },
                "nullable": true
            })
        );
    }

    #[test]
    fn deserializes_serialized_column_typmod_without_losing_sql_type_typmod() {
        let column = Column {
            name: "amount".to_owned(),
            ty: SqlType::decimal(Some(10), Some(2)),
            nullable: true,
        };
        let value = serde_json::to_value(&column).unwrap();

        let round_tripped: Column = serde_json::from_value(value).unwrap();

        assert_eq!(round_tripped, column);
    }

    #[test]
    fn deserializes_serialized_timestamp_typmod_without_losing_precision() {
        let column = Column {
            name: "ts".to_owned(),
            ty: SqlType::timestamp(Some(3)),
            nullable: true,
        };
        let value = serde_json::to_value(&column).unwrap();

        let round_tripped: Column = serde_json::from_value(value).unwrap();

        assert_eq!(round_tripped, column);
    }

    #[test]
    fn serializes_string_typmods_without_collapsing_sql_types() {
        for (ty, expected) in [
            (SqlType::text(), json!("text")),
            (SqlType::varchar(None), json!("varchar")),
            (SqlType::bpchar(), json!("bpchar")),
            (
                SqlType::varchar(Some(12)),
                json!({"kind": "varchar", "length": 12}),
            ),
            (SqlType::character(8), json!({"kind": "char", "length": 8})),
        ] {
            let encoded = serde_json::to_value(&ty).unwrap();
            assert_eq!(encoded, expected);
            assert_eq!(serde_json::from_value::<SqlType>(encoded).unwrap(), ty);
        }
    }

    #[test]
    fn sql_type_wire_round_trips_only_canonical_serializer_shapes() {
        for (ty, expected) in [
            (SqlType::Any, json!("any")),
            (SqlType::Null, json!("null")),
            (SqlType::Integer, json!("integer")),
            (SqlType::BigInt, json!("bigInt")),
            (SqlType::Float, json!("float")),
            (SqlType::Double, json!("double")),
            (SqlType::decimal(None, None), json!("decimal")),
            (SqlType::text(), json!("text")),
            (SqlType::varchar(None), json!("varchar")),
            (SqlType::bpchar(), json!("bpchar")),
            (SqlType::Boolean, json!("boolean")),
            (SqlType::Date, json!("date")),
            (SqlType::Time, json!("time")),
            (SqlType::timestamp(None), json!("timestamp")),
            (SqlType::timestamptz(None), json!("timestampTz")),
            (
                SqlType::decimal(Some(1), Some(0)),
                json!({"kind": "decimal", "precision": 1, "scale": 0}),
            ),
            (
                SqlType::decimal(Some(1000), Some(1000)),
                json!({"kind": "decimal", "precision": 1000, "scale": 1000}),
            ),
            (
                SqlType::varchar(Some(1)),
                json!({"kind": "varchar", "length": 1}),
            ),
            (
                SqlType::varchar(Some(10_485_760)),
                json!({"kind": "varchar", "length": 10_485_760}),
            ),
            (SqlType::character(1), json!({"kind": "char", "length": 1})),
            (
                SqlType::character(10_485_760),
                json!({"kind": "char", "length": 10_485_760}),
            ),
            (
                SqlType::timestamp(Some(0)),
                json!({"kind": "timestamp", "precision": 0}),
            ),
            (
                SqlType::timestamp(Some(6)),
                json!({"kind": "timestamp", "precision": 6}),
            ),
            (
                SqlType::timestamptz(Some(0)),
                json!({"kind": "timestampTz", "precision": 0}),
            ),
            (
                SqlType::timestamptz(Some(6)),
                json!({"kind": "timestampTz", "precision": 6}),
            ),
        ] {
            let encoded = serde_json::to_value(&ty).unwrap();
            assert_eq!(
                encoded, expected,
                "unexpected canonical encoding for {ty:?}"
            );
            assert_eq!(
                serde_json::from_value::<SqlType>(encoded).unwrap(),
                ty,
                "canonical encoding did not round-trip"
            );
        }
    }

    #[test]
    fn sql_type_validation_is_the_public_typmod_authority() {
        let invalid = [
            SqlType::Decimal {
                precision: Some(10),
                scale: None,
            },
            SqlType::Decimal {
                precision: None,
                scale: Some(2),
            },
            SqlType::Decimal {
                precision: Some(0),
                scale: Some(0),
            },
            SqlType::Decimal {
                precision: Some(1001),
                scale: Some(0),
            },
            SqlType::Decimal {
                precision: Some(10),
                scale: Some(1001),
            },
            SqlType::String(SqlStringType::Varchar { length: Some(0) }),
            SqlType::String(SqlStringType::Varchar {
                length: Some(10_485_761),
            }),
            SqlType::String(SqlStringType::Char { length: 0 }),
            SqlType::String(SqlStringType::Char { length: 10_485_761 }),
            SqlType::Timestamp { precision: Some(7) },
            SqlType::TimestampTz { precision: Some(7) },
        ];

        for ty in invalid {
            assert!(ty.validate().is_err(), "invalid SQL type validated: {ty:?}");
            assert!(
                serde_json::to_value(&ty).is_err(),
                "invalid SQL type serialized: {ty:?}"
            );
        }

        assert!(SqlType::try_decimal(Some(10), None).is_err());
        assert!(SqlType::try_decimal(None, Some(2)).is_err());
        assert!(SqlType::try_decimal(Some(0), Some(0)).is_err());
        assert!(SqlType::try_decimal(Some(1001), Some(0)).is_err());
        assert!(SqlType::try_decimal(Some(10), Some(1001)).is_err());
        assert!(SqlType::try_varchar(Some(0)).is_err());
        assert!(SqlType::try_varchar(Some(10_485_761)).is_err());
        assert!(SqlType::try_character(0).is_err());
        assert!(SqlType::try_character(10_485_761).is_err());
        assert!(SqlType::try_timestamp(Some(7)).is_err());
        assert!(SqlType::try_timestamptz(Some(7)).is_err());

        assert!(
            SqlType::decimal(None, None)
                .try_with_typmod(Some(10), None)
                .is_err()
        );
        assert!(
            SqlType::timestamp(None)
                .try_with_typmod(Some(3), Some(0))
                .is_err()
        );
        assert!(SqlType::character(3).try_with_typmod(None, None).is_err());
        assert!(SqlType::Integer.try_with_typmod(Some(10), Some(0)).is_err());
        assert_eq!(
            SqlType::decimal(None, None)
                .try_with_typmod(Some(10), Some(2))
                .unwrap(),
            SqlType::decimal(Some(10), Some(2))
        );
        assert_eq!(
            SqlType::varchar(None)
                .try_with_typmod(Some(12), None)
                .unwrap(),
            SqlType::varchar(Some(12))
        );

        assert!(
            std::panic::catch_unwind(|| SqlType::decimal(Some(10), None)).is_err(),
            "the convenience constructor returned a partial decimal typmod"
        );
        assert!(
            std::panic::catch_unwind(|| SqlType::timestamp(Some(7))).is_err(),
            "the convenience constructor returned an out-of-range timestamp"
        );
    }

    #[test]
    fn sql_type_wire_rejects_forged_noncanonical_shapes() {
        let mut forged = vec![
            json!("char"),
            json!({"kind": "char"}),
            json!({"kind": "decimal"}),
            json!({"kind": "varchar"}),
            json!({"kind": "timestamp"}),
            json!({"kind": "timestampTz"}),
            json!({"kind": "decimal", "scale": 2}),
            json!({"kind": "decimal", "precision": 10}),
            json!({"kind": "decimal", "precision": null, "scale": 2}),
            json!({"kind": "decimal", "precision": 10, "scale": null}),
            json!({"kind": "decimal", "precision": 10, "scale": 2, "length": 10}),
            json!({"kind": "decimal", "precision": 10, "scale": 2, "length": null}),
            json!({"kind": "timestamp", "precision": 3, "scale": 0}),
            json!({"kind": "timestampTz", "precision": 3, "length": 3}),
            json!({"kind": "varchar", "precision": 12}),
            json!({"kind": "varchar", "length": 12, "precision": 12}),
            json!({"kind": "varchar", "length": null}),
            json!({"kind": "char", "precision": 8}),
            json!({"kind": "char", "length": 8, "precision": 8}),
            json!({"kind": "char", "length": null}),
            json!({"kind": "text", "length": 12}),
            json!({"kind": "bpchar", "length": 12}),
            json!({"kind": "integer", "precision": 10}),
            json!({"kind": "decimal", "precision": 10, "scale": 2, "unknown": true}),
            json!({"kind": "char", "length": 8, "unknown": true}),
            json!({"kind": "decimal", "precision": 0, "scale": 0}),
            json!({"kind": "decimal", "precision": 1001, "scale": 0}),
            json!({"kind": "decimal", "precision": 10, "scale": 1001}),
            json!({"kind": "varchar", "length": 0}),
            json!({"kind": "varchar", "length": 10_485_761}),
            json!({"kind": "char", "length": 0}),
            json!({"kind": "char", "length": 10_485_761}),
            json!({"kind": "timestamp", "precision": 7}),
            json!({"kind": "timestampTz", "precision": 7}),
        ];
        forged.extend(
            [
                "any", "null", "integer", "bigInt", "float", "double", "text", "bpchar", "boolean",
                "date", "time",
            ]
            .into_iter()
            .map(|kind| json!({"kind": kind})),
        );

        for value in forged {
            assert!(
                serde_json::from_value::<SqlType>(value.clone()).is_err(),
                "forged SQL type wire shape was accepted: {value}"
            );
        }
    }
}
