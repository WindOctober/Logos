use serde::Serialize;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum CoreScalarUnsupported {
    BadArity,
    ExpectedPredicate,
    ExpectedValue,
    UnsupportedOperator,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct CoreScalarFailure {
    pub reason: CoreScalarUnsupported,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub operator: Option<String>,
}
