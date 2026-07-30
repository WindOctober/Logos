use crate::ir::ScalarOp;

pub fn classify_scalar_op(operator: &str) -> ScalarOp {
    match operator.trim().to_ascii_uppercase().as_str() {
        "=" => ScalarOp::Eq,
        "<>" | "!=" => ScalarOp::NotEq,
        "<" => ScalarOp::Lt,
        "<=" => ScalarOp::Lte,
        ">" => ScalarOp::Gt,
        ">=" => ScalarOp::Gte,
        "AND" => ScalarOp::And,
        "OR" => ScalarOp::Or,
        "NOT" => ScalarOp::Not,
        "IS NULL" => ScalarOp::IsNull,
        "IS NOT NULL" => ScalarOp::IsNotNull,
        "IS TRUE" => ScalarOp::IsTrue,
        "IS NOT TRUE" => ScalarOp::IsNotTrue,
        "IS FALSE" => ScalarOp::IsFalse,
        "IS NOT FALSE" => ScalarOp::IsNotFalse,
        "IS NOT DISTINCT FROM" => ScalarOp::IsNotDistinctFrom,
        "LIKE" => ScalarOp::Like,
        "+" => ScalarOp::Plus,
        "-" => ScalarOp::Minus,
        "*" => ScalarOp::Multiply,
        "/" => ScalarOp::Divide,
        "||" => ScalarOp::StringConcat,
        "CAST" => ScalarOp::Cast,
        "CASE" => ScalarOp::Case,
        "LOWER" => ScalarOp::Lower,
        "UPPER" => ScalarOp::Upper,
        "SUBSTRING" => ScalarOp::Substring,
        "EXP" => ScalarOp::Exp,
        "POWER" => ScalarOp::Power,
        "EXTRACT" => ScalarOp::Extract,
        "IN" => ScalarOp::In,
        "EXISTS" => ScalarOp::Exists,
        "$SCALAR_QUERY" => ScalarOp::ScalarQuery,
        _ => ScalarOp::Other(operator.trim().to_owned()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn classifies_scalar_operators_without_parsing_display_text() {
        for (operator, expected) in [
            ("=", ScalarOp::Eq),
            ("<>", ScalarOp::NotEq),
            ("is not null", ScalarOp::IsNotNull),
            ("is not distinct from", ScalarOp::IsNotDistinctFrom),
            ("LIKE", ScalarOp::Like),
            ("||", ScalarOp::StringConcat),
            ("substring", ScalarOp::Substring),
            ("IN", ScalarOp::In),
            ("EXISTS", ScalarOp::Exists),
            ("$SCALAR_QUERY", ScalarOp::ScalarQuery),
            ("IS FALSE", ScalarOp::IsFalse),
            ("IS NOT FALSE", ScalarOp::IsNotFalse),
            ("+", ScalarOp::Plus),
        ] {
            assert_eq!(classify_scalar_op(operator), expected);
        }
        assert_eq!(
            classify_scalar_op("ITEM"),
            ScalarOp::Other("ITEM".to_owned())
        );
        assert_eq!(
            classify_scalar_op("SEARCH"),
            ScalarOp::Other("SEARCH".to_owned())
        );
    }
}
