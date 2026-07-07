use crate::ir::ScalarOp;

use super::ast::CoreComparisonOp;

pub(super) fn is_value_op(op: &ScalarOp) -> bool {
    matches!(
        op,
        ScalarOp::Plus
            | ScalarOp::Minus
            | ScalarOp::Multiply
            | ScalarOp::Divide
            | ScalarOp::Case
            | ScalarOp::StringConcat
            | ScalarOp::Lower
            | ScalarOp::Upper
            | ScalarOp::Substring
            | ScalarOp::Exp
            | ScalarOp::Power
            | ScalarOp::Extract
            | ScalarOp::ScalarQuery
    )
}

pub(super) fn is_predicate_op(op: &ScalarOp) -> bool {
    matches!(
        op,
        ScalarOp::Eq
            | ScalarOp::NotEq
            | ScalarOp::Lt
            | ScalarOp::Lte
            | ScalarOp::Gt
            | ScalarOp::Gte
            | ScalarOp::IsNotDistinctFrom
            | ScalarOp::IsNull
            | ScalarOp::IsNotNull
            | ScalarOp::IsTrue
            | ScalarOp::IsNotTrue
            | ScalarOp::IsFalse
            | ScalarOp::IsNotFalse
            | ScalarOp::Like
            | ScalarOp::In
            | ScalarOp::Exists
            | ScalarOp::Search
            | ScalarOp::And
            | ScalarOp::Or
            | ScalarOp::Not
    )
}

pub(super) fn comparison_op(op: &ScalarOp) -> CoreComparisonOp {
    match op {
        ScalarOp::Eq => CoreComparisonOp::Eq,
        ScalarOp::NotEq => CoreComparisonOp::NotEq,
        ScalarOp::Lt => CoreComparisonOp::Lt,
        ScalarOp::Lte => CoreComparisonOp::Lte,
        ScalarOp::Gt => CoreComparisonOp::Gt,
        ScalarOp::Gte => CoreComparisonOp::Gte,
        ScalarOp::IsNotDistinctFrom => CoreComparisonOp::IsNotDistinctFrom,
        _ => unreachable!("comparison_op called for non-comparison operator"),
    }
}
