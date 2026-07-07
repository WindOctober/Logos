use std::path::PathBuf;

use thiserror::Error;

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, Error)]
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
    #[error("invalid Logos IR input: {0}")]
    InvalidLogosIrInput(String),
    #[error("Logos IR error: {0}")]
    LogosIr(#[from] logos_ir::Error),
    #[error("proposal command failed: {0}")]
    ProposalCommand(String),
    #[error("proof agent command failed: {0}")]
    ProofAgentCommand(String),
    #[error("invalid counterexample proposal: {0}")]
    InvalidCandidate(String),
    #[error("PostgreSQL connection string is required for witness validation")]
    MissingPostgresUrl,
    #[error("PostgreSQL error: {0}")]
    Postgres(#[from] postgres::Error),
    #[error("serialization error: {0}")]
    Serde(#[from] serde_json::Error),
}
