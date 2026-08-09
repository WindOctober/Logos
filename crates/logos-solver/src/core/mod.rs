mod input;
mod lowering;
mod observation;
mod syntax;
mod verification;

#[cfg(test)]
pub(crate) use input::{PostgresStructureToken, postgres_structure_tokens};
pub use input::{VerificationInput, VerificationIr};
pub use logos_ir::ir::SqlEnvironment;
#[cfg(test)]
pub(crate) use lowering::emit_rocq_query_expr_proof_module_for_mode;
pub use lowering::{LoweringConfig, SqlTimeZone, lower_verification_input_with_mode};
#[cfg(test)]
pub(crate) use observation::{CertificateStatus, StatementObservationFacts};
pub(crate) use observation::{ObservationCertificateReport, analyze_observation_certificates};
pub(crate) use syntax::{
    FormalAttribute, FormalAttributeType, FormalProofModule, FormalQueryDefinitionGraph,
    FormalQueryError, FormalQueryExpr, FormalQueryStatementSymbols, FormalScalarExpr,
    FormalScalarSelectItem, FormalSchema, LoweredProgram, LoweredQuery, ProofInputBindings,
    ProofLoweringReport, query_expr_output_signature,
};
#[cfg(test)]
pub(crate) use syntax::{FormalTable, FormalTableConstraints, LoweringStatus};
pub use verification::VerificationMode;
