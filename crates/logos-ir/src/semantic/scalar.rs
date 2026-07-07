use serde::Serialize;

use crate::ir::ScalarAst;
use crate::semantic::core_scalar::{CoreScalarExpr, lower_core_scalar};

pub use crate::semantic::core_scalar::CoreScalarUnsupported as SemanticScalarUnsupported;

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase", tag = "kind")]
pub enum SemanticScalarClass {
    CoreValue,
    CorePredicate,
    Unsupported { reason: SemanticScalarUnsupported },
}

pub fn classify_semantic_scalar(ast: &ScalarAst) -> SemanticScalarClass {
    match lower_core_scalar(ast) {
        Ok(CoreScalarExpr::Value { .. }) => SemanticScalarClass::CoreValue,
        Ok(CoreScalarExpr::Predicate { .. }) => SemanticScalarClass::CorePredicate,
        Err(reason) => SemanticScalarClass::Unsupported { reason },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::calcite::scalar::calcite_scalar;

    #[test]
    fn classifies_core_predicate_shape() {
        let expr = calcite_scalar("AND(=($0, 1), IS NOT NULL($1))");
        assert_eq!(
            classify_semantic_scalar(&expr.parsed),
            SemanticScalarClass::CorePredicate
        );
    }

    #[test]
    fn classifies_core_value_shape() {
        let expr = calcite_scalar("+($0, 1)");
        assert_eq!(
            classify_semantic_scalar(&expr.parsed),
            SemanticScalarClass::CoreValue
        );
    }

    #[test]
    fn rejects_non_core_operator_shape() {
        let expr = calcite_scalar("CAST('1998-08-04')");
        assert_eq!(
            classify_semantic_scalar(&expr.parsed),
            SemanticScalarClass::Unsupported {
                reason: SemanticScalarUnsupported::UnsupportedOperator
            }
        );
    }

    #[test]
    fn classifies_boolean_value_predicate_shape() {
        let expr = calcite_scalar("AND($0, $1)");
        assert_eq!(
            classify_semantic_scalar(&expr.parsed),
            SemanticScalarClass::CorePredicate
        );
    }
}
