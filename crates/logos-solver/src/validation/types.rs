use serde::Serialize;

use crate::core::{FormalAttributeType, FormalQueryError};

#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct OutputSchemaPreflight {
    pub schema_name: String,
    pub result: OutputSchemaPreflightResult,
}

#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase", tag = "kind")]
pub enum OutputSchemaPreflightResult {
    Compatible {
        source: Vec<StatementOutput>,
        target: Vec<StatementOutput>,
    },
    Mismatch {
        mismatch: SchemaMismatch,
    },
    ValidationError {
        message: String,
    },
}

#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct WitnessCheck {
    pub schema_name: String,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub warnings: Vec<ValidationWarning>,
    pub result: CheckResult,
}

/// A PostgreSQL validation result paired with an optional, typed copy of the
/// exact database state on which the result was observed.
///
/// The snapshot is evidence input for a later FormalSQL countermodel.  It is
/// deliberately separate from [`WitnessCheck`]: successfully decoding a
/// database does not make one PostgreSQL execution a non-equivalence
/// certificate, and callers must still construct and kernel-check that
/// countermodel.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct WitnessValidation {
    pub check: WitnessCheck,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub snapshot: Option<FormalWitnessSnapshot>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct FormalWitnessSnapshot {
    pub schema_version: u32,
    pub tables: Vec<FormalWitnessTable>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct FormalWitnessTable {
    pub relation: String,
    pub columns: Vec<FormalWitnessColumn>,
    pub rows: Vec<FormalWitnessRow>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct FormalWitnessColumn {
    pub name: String,
    pub ty: FormalAttributeType,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct FormalWitnessRow {
    pub cells: Vec<FormalWitnessValue>,
}

/// Canonical typed values supported by the trusted snapshot boundary.
///
/// Null is interpreted at the enclosing column type.  Unsupported
/// FormalSQL/PostgreSQL type pairs cause snapshot extraction to fail closed;
/// they are never converted through PostgreSQL's text rendering.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "camelCase", tag = "kind", content = "value")]
pub enum FormalWitnessValue {
    Null,
    Bool(bool),
    Int32(i32),
    Int64(i64),
    String(String),
    Float32Bits(u32),
    Float64Bits(u64),
    /// Exact finite decimal value.  The coefficient is stored as a decimal
    /// string rather than a machine integer so PostgreSQL's full NUMERIC
    /// range remains representable at the trusted snapshot boundary.
    NumericFinite {
        coefficient: String,
        scale: i32,
    },
    NumericNegInfinity,
    NumericPosInfinity,
    NumericNaN,
    /// Signed count of civil days from 1970-01-01, matching FormalSQL DATE.
    Date(i32),
    /// Signed count of microseconds from midnight.
    Time(i64),
    /// Signed decimal microseconds from 1970-01-01.  A string retains the full
    /// PostgreSQL timestamp range, whose positive endpoint exceeds `i64` once
    /// translated from PostgreSQL's 2000 epoch to FormalSQL's Unix epoch.
    Timestamp(String),
    Timestamptz(String),
}

#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase", tag = "kind")]
pub enum CheckResult {
    /// PostgreSQL accepted the schema and candidate DML, the benchmark
    /// integrity contract held, and the complete database was exported into
    /// the typed FormalSQL witness representation. No query was executed and
    /// this result makes no equivalence or non-equivalence claim.
    WitnessMaterialized {
        table_count: usize,
        row_count: usize,
    },
    #[cfg(test)]
    DataDifference {
        statement: usize,
        source_result: String,
        target_result: String,
        diff_sample: String,
        certificate: ObservationCertificateUse,
    },
    #[cfg(test)]
    RowSequenceDifference {
        statement: usize,
        first_differing_row: usize,
        source_result: String,
        target_result: String,
        certificate: ObservationCertificateUse,
    },
    /// PostgreSQL produced two different concrete executions, but the host
    /// could not prove that either execution denotes the complete possible-
    /// observation relation.  This is a hint for a FormalSQL countermodel,
    /// never evidence of non-equivalence by itself.
    #[cfg(test)]
    InconclusiveObservation {
        statement: usize,
        comparison: ObservationComparison,
        reason: String,
        source_result: String,
        target_result: String,
    },
    #[cfg(test)]
    OutputSchemaMismatch {
        mismatch: SchemaMismatch,
    },
    #[cfg(test)]
    NoDifference,
    ValidationError {
        message: String,
    },
}

#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum ObservationComparison {
    Bag,
    Sequence,
}

#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ObservationCertificateUse {
    pub schema_version: u32,
    pub verification_input_key: String,
    pub verification_input_sha256: String,
    pub lowering_sha256: String,
    pub statement: usize,
    pub comparison: ObservationComparison,
    pub source_derivation: String,
    pub target_derivation: String,
}

#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase", tag = "kind")]
pub enum SchemaMismatch {
    ProgramLength {
        reason: String,
        source_statement_count: usize,
        target_statement_count: usize,
    },
    StatementOutput {
        reason: String,
        statement: usize,
        source: OutputSchema,
        target: OutputSchema,
    },
    StatementOutcome {
        reason: String,
        statement: usize,
        source: StatementOutput,
        target: StatementOutput,
    },
}

impl SchemaMismatch {
    pub fn reason(&self) -> &str {
        match self {
            Self::ProgramLength { reason, .. }
            | Self::StatementOutput { reason, .. }
            | Self::StatementOutcome { reason, .. } => reason,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase", tag = "kind")]
pub enum StatementOutput {
    Success {
        schema: OutputSchema,
    },
    AnalysisError {
        error: FormalQueryError,
        sql_state: String,
        message: String,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct OutputSchema {
    pub columns: Vec<OutputColumn>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct OutputColumn {
    pub ordinal: usize,
    pub name: String,
    pub type_oid: u32,
    pub type_modifier: i32,
    pub type_name: String,
}

#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ValidationWarning {
    pub code: String,
    pub message: String,
}
