#[cfg(test)]
mod bag_semantics;
mod determinism;
#[cfg(test)]
mod observation;
mod postgres;
mod postgres_session;
mod schema;
mod types;

pub use postgres::PostgresValidator;
pub(crate) use postgres_session::witness_uses_only_allowed_dml;
#[allow(unused_imports)]
pub use types::{
    CheckResult, FormalWitnessColumn, FormalWitnessRow, FormalWitnessSnapshot, FormalWitnessTable,
    FormalWitnessValue, OutputSchemaPreflight, OutputSchemaPreflightResult, SchemaMismatch,
    ValidationWarning, WitnessCheck, WitnessValidation,
};
#[cfg(test)]
pub(crate) use types::{
    ObservationCertificateUse, ObservationComparison, OutputColumn, OutputSchema,
};
