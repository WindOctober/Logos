mod ast;
mod error;
mod lower;
mod ops;

#[cfg(test)]
mod tests;

pub use ast::{
    CoreArithmeticOp, CoreCaseBranch, CoreComparisonOp, CoreNumericFunctionOp,
    CorePredicateCaseBranch, CorePredicateExpr, CoreScalarExpr, CoreStringFunctionOp,
    CoreValueExpr,
};
pub use error::{CoreScalarFailure, CoreScalarUnsupported};
pub use lower::{diagnose_core_scalar_failure, lower_core_scalar};
