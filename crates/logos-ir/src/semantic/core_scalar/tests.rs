use super::*;
use crate::calcite::scalar::calcite_scalar;

#[test]
fn lowers_core_predicate_shape() {
    let expr = calcite_scalar("AND(=($0, 1), IS NOT NULL($1))");
    assert_eq!(
        lower_core_scalar(&expr.parsed),
        Ok(CoreScalarExpr::Predicate {
            expr: CorePredicateExpr::And {
                predicates: vec![
                    CorePredicateExpr::Comparison {
                        op: CoreComparisonOp::Eq,
                        left: Box::new(CoreValueExpr::InputRef { index: 0 }),
                        right: Box::new(CoreValueExpr::Literal {
                            raw: "1".to_owned()
                        }),
                    },
                    CorePredicateExpr::IsNotNull {
                        expr: Box::new(CoreValueExpr::InputRef { index: 1 }),
                    },
                ],
            },
        })
    );
}

#[test]
fn lowers_core_arithmetic_value_shape() {
    let expr = calcite_scalar("-(*($0, 2))");
    assert_eq!(
        lower_core_scalar(&expr.parsed),
        Ok(CoreScalarExpr::Value {
            expr: CoreValueExpr::Arithmetic {
                op: CoreArithmeticOp::UnaryMinus,
                args: vec![CoreValueExpr::Arithmetic {
                    op: CoreArithmeticOp::Multiply,
                    args: vec![
                        CoreValueExpr::InputRef { index: 0 },
                        CoreValueExpr::Literal {
                            raw: "2".to_owned()
                        },
                    ],
                }],
            },
        })
    );
}

#[test]
fn lowers_typed_cast_shape() {
    let expr = calcite_scalar("CAST(+($0, /(10, 2))):INTEGER NOT NULL");
    assert_eq!(
        lower_core_scalar(&expr.parsed),
        Ok(CoreScalarExpr::Value {
            expr: CoreValueExpr::Cast {
                expr: Box::new(CoreValueExpr::Arithmetic {
                    op: CoreArithmeticOp::Plus,
                    args: vec![
                        CoreValueExpr::InputRef { index: 0 },
                        CoreValueExpr::Arithmetic {
                            op: CoreArithmeticOp::Divide,
                            args: vec![
                                CoreValueExpr::Literal {
                                    raw: "10".to_owned()
                                },
                                CoreValueExpr::Literal {
                                    raw: "2".to_owned()
                                },
                            ],
                        },
                    ],
                }),
                ty: "INTEGER NOT NULL".to_owned(),
            },
        })
    );
}

#[test]
fn lowers_searched_case_value_and_predicate_shapes() {
    let value_case = calcite_scalar("CASE(IS NOT NULL($0), CAST($0):INTEGER NOT NULL, 0)");
    assert_eq!(
        lower_core_scalar(&value_case.parsed),
        Ok(CoreScalarExpr::Value {
            expr: CoreValueExpr::Case {
                branches: vec![CoreCaseBranch {
                    when: CorePredicateExpr::IsNotNull {
                        expr: Box::new(CoreValueExpr::InputRef { index: 0 }),
                    },
                    then: CoreValueExpr::Cast {
                        expr: Box::new(CoreValueExpr::InputRef { index: 0 }),
                        ty: "INTEGER NOT NULL".to_owned(),
                    },
                }],
                else_expr: Box::new(CoreValueExpr::Literal {
                    raw: "0".to_owned(),
                }),
            },
        })
    );

    let predicate_case = calcite_scalar("CASE(=($0, 1), IS NULL($1), IS NOT NULL($2))");
    assert_eq!(
        lower_core_scalar(&predicate_case.parsed),
        Ok(CoreScalarExpr::Predicate {
            expr: CorePredicateExpr::Case {
                branches: vec![CorePredicateCaseBranch {
                    when: CorePredicateExpr::Comparison {
                        op: CoreComparisonOp::Eq,
                        left: Box::new(CoreValueExpr::InputRef { index: 0 }),
                        right: Box::new(CoreValueExpr::Literal {
                            raw: "1".to_owned(),
                        }),
                    },
                    then: CorePredicateExpr::IsNull {
                        expr: Box::new(CoreValueExpr::InputRef { index: 1 }),
                    },
                }],
                else_predicate: Box::new(CorePredicateExpr::IsNotNull {
                    expr: Box::new(CoreValueExpr::InputRef { index: 2 }),
                }),
            },
        })
    );
}

#[test]
fn lowers_function_and_like_shapes() {
    let substring = calcite_scalar("SUBSTRING($4, 1, 2)");
    assert_eq!(
        lower_core_scalar(&substring.parsed),
        Ok(CoreScalarExpr::Value {
            expr: CoreValueExpr::StringFunction {
                op: CoreStringFunctionOp::Substring,
                args: vec![
                    CoreValueExpr::InputRef { index: 4 },
                    CoreValueExpr::Literal {
                        raw: "1".to_owned(),
                    },
                    CoreValueExpr::Literal {
                        raw: "2".to_owned(),
                    },
                ],
            },
        })
    );

    let like = calcite_scalar("LIKE($1, 'abc!%', '!')");
    assert_eq!(
        lower_core_scalar(&like.parsed),
        Ok(CoreScalarExpr::Predicate {
            expr: CorePredicateExpr::Like {
                value: Box::new(CoreValueExpr::InputRef { index: 1 }),
                pattern: Box::new(CoreValueExpr::Literal {
                    raw: "'abc!%'".to_owned(),
                }),
                escape: Some(Box::new(CoreValueExpr::Literal {
                    raw: "'!'".to_owned(),
                })),
            },
        })
    );
}

#[test]
fn rejects_search_predicate_shape_until_sarg_lowering_exists() {
    let search = calcite_scalar("SEARCH(-($23, $0), Sarg[(30..60]])");
    assert_eq!(
        lower_core_scalar(&search.parsed),
        Err(CoreScalarUnsupported::UnsupportedOperator)
    );
}

#[test]
fn rejects_type_role_and_arity_errors() {
    let lower = calcite_scalar("LOWER($0, $1)");
    assert_eq!(
        lower_core_scalar(&lower.parsed),
        Err(CoreScalarUnsupported::BadArity)
    );

    let string_function = calcite_scalar("UPPER(=($0, 1))");
    assert_eq!(
        lower_core_scalar(&string_function.parsed),
        Err(CoreScalarUnsupported::ExpectedValue)
    );

    let context = calcite_scalar("AND(+($9, 1), =($38, 8861))");
    assert_eq!(
        lower_core_scalar(&context.parsed),
        Err(CoreScalarUnsupported::ExpectedPredicate)
    );
}

#[test]
fn diagnoses_first_failing_inner_operator() {
    let expr = calcite_scalar("AND(=($0, 1), =(CAST('x'), 'abc'))");
    assert_eq!(
        diagnose_core_scalar_failure(&expr.parsed),
        Some(CoreScalarFailure {
            reason: CoreScalarUnsupported::UnsupportedOperator,
            operator: Some("Cast".to_owned()),
        })
    );
}
