use serde::{Deserialize, Serialize};

use super::observation::ValidationWarning;

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct WitnessCheck {
    pub schema_name: String,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub warnings: Vec<ValidationWarning>,
    pub result: CheckResult,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", tag = "kind")]
pub enum CheckResult {
    DataDifference {
        source_result: String,
        target_result: String,
        diff_sample: String,
    },
    OutputSchemaMismatch {
        mismatch: SchemaMismatch,
    },
    NoDifference,
    ValidationError {
        message: String,
    },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SchemaMismatch {
    pub reason: String,
    pub source: OutputSchema,
    pub target: OutputSchema,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct OutputSchema {
    pub columns: Vec<OutputColumn>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct OutputColumn {
    pub ordinal: usize,
    pub name: String,
    pub type_oid: u32,
    pub type_name: String,
}
