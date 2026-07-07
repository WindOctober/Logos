use std::path::PathBuf;

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("failed to read {path}: {source}")]
    Read {
        path: PathBuf,
        source: std::io::Error,
    },
    #[error("failed to write {path}: {source}")]
    Write {
        path: PathBuf,
        source: std::io::Error,
    },
    #[error("failed to parse JSON from {path}: {source}")]
    Json {
        path: PathBuf,
        source: serde_json::Error,
    },
    #[error("SQL IR frontend command failed: {0}")]
    SqlIrFrontendCommand(String),
    #[error("failed to parse SQL IR frontend output as Calcite JSON: {0}")]
    SqlIrFrontendJson(#[source] serde_json::Error),
    #[error("Calcite query contains frontend error: {0}")]
    CalciteQueryError(String),
    #[error("unsupported Calcite relational node: {0}")]
    UnsupportedRelNode(String),
    #[error("unsupported Calcite join type: {0}")]
    UnsupportedJoinType(String),
    #[error("unsupported Calcite set operation: {0}")]
    UnsupportedSetOp(String),
    #[error("unsupported Calcite sort direction: {0}")]
    UnsupportedSortDirection(String),
    #[error("unsupported Calcite SQL type: {0}")]
    UnsupportedSqlType(String),
    #[error("invalid Calcite scalar expression: {0}")]
    InvalidScalar(String),
    #[error("invalid Calcite aggregate call: {0}")]
    InvalidAggregateCall(String),
    #[error("{node} expected {expected} input(s), found {actual}")]
    Arity {
        node: &'static str,
        expected: &'static str,
        actual: usize,
    },
    #[error("{node} is missing required Calcite field `{field}`")]
    MissingField {
        node: &'static str,
        field: &'static str,
    },
    #[error("invalid Calcite groupSet: {0}")]
    InvalidGroupSet(String),
}
