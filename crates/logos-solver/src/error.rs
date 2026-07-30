use std::path::PathBuf;

use thiserror::Error;

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, Error)]
pub enum Error {
    #[error("failed to spawn the bounded-stack solver worker: {0}")]
    WorkerThread(#[source] std::io::Error),
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
    #[error("failed to create directory {path}: {source}")]
    CreateDir {
        path: PathBuf,
        source: std::io::Error,
    },
    #[error("failed to read LLM assessment cache {path}: {source}")]
    ReadAssessmentCache {
        path: PathBuf,
        source: std::io::Error,
    },
    #[error("failed to write LLM assessment cache {path}: {source}")]
    WriteAssessmentCache {
        path: PathBuf,
        source: std::io::Error,
    },
    #[error("failed to parse LLM assessment cache {path}: {source}")]
    ParseAssessmentCache {
        path: PathBuf,
        source: serde_json::Error,
    },
    #[error("invalid LLM assessment cache {path}: {reason}")]
    InvalidAssessmentCache { path: PathBuf, reason: String },
    #[error("invalid Logos IR input: {0}")]
    InvalidLogosIrInput(String),
    #[error("invalid SQL time zone: {0}")]
    InvalidSqlTimeZone(String),
    #[error("invalid SQL text environment: {0}")]
    InvalidSqlEnvironment(String),
    #[error("Logos IR error: {0}")]
    LogosIr(#[from] logos_ir::Error),
    #[error("proposal command failed: {0}")]
    ProposalCommand(String),
    #[error("proof agent command failed: {0}")]
    ProofAgentCommand(String),
    #[error("trusted Rocq environment failed before certificate checking: {0}")]
    TrustedRocqEnvironment(String),
    #[error("invalid counterexample proposal: {0}")]
    InvalidCandidate(String),
    #[error("invalid schema SQL for PostgreSQL validation: {0}")]
    InvalidSchemaSql(String),
    #[error(
        "PostgreSQL connection string is required for output analysis and witness materialization"
    )]
    MissingPostgresUrl,
    // `postgres::Error` deliberately renders server errors as only `db error`
    // through Display.  Preserve its structured Debug payload here so failed
    // benchmark preflights retain the SQLSTATE and server message needed to
    // distinguish an input/frontend failure from infrastructure trouble.
    #[error("PostgreSQL error: {0:?}")]
    Postgres(#[from] postgres::Error),
    #[error("PostgreSQL validation environment mismatch: {0}")]
    PostgresEnvironmentMismatch(String),
    #[error("FormalSQL verification does not admit PostgreSQL-volatile queries: {0}")]
    NonDeterministicQuery(String),
    #[error("failed to inspect the PostgreSQL analyzed query: {0}")]
    PostgresQueryInspection(String),
    #[error("PostgreSQL output-schema preflight failed: {0}")]
    OutputSchemaPreflight(String),
    #[error("serialization error: {0}")]
    Serde(#[from] serde_json::Error),
    #[error("authoritative LLM usage error: {0}")]
    LlmUsage(#[from] crate::usage::UsageError),
}
