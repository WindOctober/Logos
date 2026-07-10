use super::*;
use logos_ir::ir::ScalarOp;

use logos_ir::ir::{
    AggregateCall, AggregateModifiers, Column, CorrelationBinding, Feature, JoinType, Query,
    RelExpr, ScalarAst, ScalarClass, ScalarExpr, Schema, SetOp, SortDirection, SortNullDirection,
    SqlType, Table, ValuesTuples,
};

#[test]
fn sql_time_zone_canonicalizes_fixed_offsets_for_postgres() {
    let zone = SqlTimeZone::try_parse("+08:00").unwrap();
    assert_eq!(
        zone.postgres_set_time_zone_sql().unwrap(),
        "SET TIME ZONE INTERVAL '+08:00' HOUR TO MINUTE"
    );

    let zone = SqlTimeZone::try_parse("-05:30").unwrap();
    assert_eq!(
        zone.postgres_set_time_zone_sql().unwrap(),
        "SET TIME ZONE INTERVAL '-05:30' HOUR TO MINUTE"
    );
}

#[test]
fn sql_time_zone_rejects_prefixed_posix_style_offsets() {
    assert!(SqlTimeZone::try_parse("UTC+08:00").is_err());
    assert!(SqlTimeZone::try_parse("GMT-05:00").is_err());
    assert!(SqlTimeZone::try_parse("+8").is_err());
}

#[test]
fn sql_time_zone_accepts_iana_names() {
    let zone = SqlTimeZone::try_parse("Asia/Shanghai").unwrap();
    assert_eq!(
        zone.postgres_set_time_zone_sql().unwrap(),
        "SET TIME ZONE 'Asia/Shanghai'"
    );
}

#[test]
fn lowers_project_filter_table_subset() {
    let table_output = vec![column("a"), column("b")];
    let rel = RelExpr::Project {
        input: Box::new(RelExpr::Filter {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: table_output.clone(),
            }),
            predicate: scalar(ScalarAst::Call {
                operator: "=".to_owned(),
                op: ScalarOp::Eq,
                args: vec![
                    ScalarAst::InputRef { index: 0 },
                    ScalarAst::Literal {
                        raw: "1".to_owned(),
                    },
                ],
            }),
            correlations: Vec::new(),
            output: table_output.clone(),
        }),
        exprs: vec![scalar(ScalarAst::InputRef { index: 1 })],
        correlations: Vec::new(),
        output: vec![column("b")],
    };
    let query = Query {
        source_sql: None,
        rel,
        output: vec![column("b")],
        features: vec![Feature::TableScan, Feature::Selection, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert!(lowered.query.is_some());
    assert!(
        lowered
            .diagnostics
            .iter()
            .all(|diagnostic| diagnostic.severity == DiagnosticSeverity::Warning)
    );
}

#[test]
fn lowers_builtin_value_expressions_without_external_symbol_warning() {
    let table_output = vec![
        column("a"),
        column("b"),
        typed_column("name", SqlType::Varchar),
    ];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: table_output,
            }),
            exprs: vec![
                scalar(ScalarAst::Call {
                    operator: "AND".to_owned(),
                    op: ScalarOp::And,
                    args: vec![
                        ScalarAst::Call {
                            operator: "<".to_owned(),
                            op: ScalarOp::Lt,
                            args: vec![
                                ScalarAst::InputRef { index: 0 },
                                ScalarAst::InputRef { index: 1 },
                            ],
                        },
                        ScalarAst::Call {
                            operator: "IS NULL".to_owned(),
                            op: ScalarOp::IsNull,
                            args: vec![ScalarAst::InputRef { index: 0 }],
                        },
                    ],
                }),
                scalar(ScalarAst::Call {
                    operator: "UPPER".to_owned(),
                    op: ScalarOp::Upper,
                    args: vec![ScalarAst::InputRef { index: 2 }],
                }),
            ],
            correlations: Vec::new(),
            output: vec![
                typed_column("ok", SqlType::Boolean),
                typed_column("upper_name", SqlType::Varchar),
            ],
        },
        output: vec![
            typed_column("ok", SqlType::Boolean),
            typed_column("upper_name", SqlType::Varchar),
        ],
        features: vec![Feature::TableScan, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);
    let module = emit_rocq_query_module(
        lowered
            .list_query
            .as_ref()
            .expect("boolean value expression should lower"),
        lowered
            .list_query
            .as_ref()
            .expect("boolean value expression should lower"),
    );

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert!(
        !lowered.diagnostics.iter().any(|diagnostic| {
            diagnostic.code == "aggregate_term_symbol_interpretation_required"
        })
    );
    assert!(module.rocq_module.contains("AFunction \"and\""));
    assert!(module.rocq_module.contains("AFunction \"<\""));
    assert!(module.rocq_module.contains("AFunction \"is_null\""));
    assert!(module.rocq_module.contains("AFunction \"upper\""));
}

#[test]
fn distinguishes_float_and_double_schema_attributes() {
    let schema = Schema {
        tables: vec![Table {
            name: "measurements".to_owned(),
            columns: vec![
                typed_column("f", SqlType::Float),
                typed_column("d", SqlType::Double),
            ],
        }],
    };

    let lowered = lower_schema(&schema);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let schema = lowered.schema.as_ref().expect("schema should lower");
    assert!(schema.rocq_create_schema.contains("Attr_float \"f\""));
    assert!(schema.rocq_create_schema.contains("Attr_double \"d\""));
}

#[test]
fn lowers_double_arithmetic_with_double_symbol() {
    let input = vec![
        typed_column("left_value", SqlType::Double),
        typed_column("right_value", SqlType::Double),
    ];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["measurements".to_owned()],
                output: input,
            }),
            exprs: vec![scalar(ScalarAst::Call {
                operator: "+".to_owned(),
                op: ScalarOp::Plus,
                args: vec![
                    ScalarAst::InputRef { index: 0 },
                    ScalarAst::InputRef { index: 1 },
                ],
            })],
            correlations: Vec::new(),
            output: vec![typed_column("sum_value", SqlType::Double)],
        },
        output: vec![typed_column("sum_value", SqlType::Double)],
        features: vec![Feature::TableScan, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.list_query.as_ref().unwrap(),
        lowered.list_query.as_ref().unwrap(),
    );
    assert!(module.rocq_module.contains("AFunction \"plus_double\""));
    assert!(!module.rocq_module.contains("AFunction \"plus.\""));
}

#[test]
fn rejects_double_arithmetic_projected_as_float() {
    let input = vec![
        typed_column("left_value", SqlType::Double),
        typed_column("right_value", SqlType::Double),
    ];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["measurements".to_owned()],
                output: input,
            }),
            exprs: vec![scalar(ScalarAst::Call {
                operator: "+".to_owned(),
                op: ScalarOp::Plus,
                args: vec![
                    ScalarAst::InputRef { index: 0 },
                    ScalarAst::InputRef { index: 1 },
                ],
            })],
            correlations: Vec::new(),
            output: vec![typed_column("sum_value", SqlType::Float)],
        },
        output: vec![typed_column("sum_value", SqlType::Float)],
        features: vec![Feature::TableScan, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "floating_output_type_not_supported")
    );
}

#[test]
fn rejects_floating_expression_annotation_that_changes_type() {
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["measurements".to_owned()],
                output: vec![typed_column("value", SqlType::Float)],
            }),
            exprs: vec![scalar(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::InputRef { index: 0 }),
                ty: "DOUBLE".to_owned(),
            })],
            correlations: Vec::new(),
            output: vec![typed_column("value", SqlType::Double)],
        },
        output: vec![typed_column("value", SqlType::Double)],
        features: vec![Feature::TableScan, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "floating_cast_not_supported")
    );
}

#[test]
fn lowers_double_integer_literal_with_ieee_bits() {
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["measurements".to_owned()],
                output: vec![column("id")],
            }),
            exprs: vec![scalar(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "7".to_owned(),
                }),
                ty: "DOUBLE".to_owned(),
            })],
            correlations: Vec::new(),
            output: vec![typed_column("value", SqlType::Double)],
        },
        output: vec![typed_column("value", SqlType::Double)],
        features: vec![Feature::TableScan, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.list_query.as_ref().unwrap(),
        lowered.list_query.as_ref().unwrap(),
    );
    assert!(
        module
            .rocq_module
            .contains("CstDoubleBits (4619567317775286272)")
    );
}

#[test]
fn lowers_non_integer_double_literal_with_ieee_bits() {
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["measurements".to_owned()],
                output: vec![column("id")],
            }),
            exprs: vec![scalar(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "7.5".to_owned(),
                }),
                ty: "DOUBLE".to_owned(),
            })],
            correlations: Vec::new(),
            output: vec![typed_column("value", SqlType::Double)],
        },
        output: vec![typed_column("value", SqlType::Double)],
        features: vec![Feature::TableScan, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.list_query.as_ref().unwrap(),
        lowered.list_query.as_ref().unwrap(),
    );
    assert!(
        module
            .rocq_module
            .contains("CstDoubleBits (4620130267728707584)")
    );
}

#[test]
fn lowers_non_integer_float_literal_with_ieee_bits() {
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["measurements".to_owned()],
                output: vec![column("id")],
            }),
            exprs: vec![scalar(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "7.5".to_owned(),
                }),
                ty: "REAL".to_owned(),
            })],
            correlations: Vec::new(),
            output: vec![typed_column("value", SqlType::Float)],
        },
        output: vec![typed_column("value", SqlType::Float)],
        features: vec![Feature::TableScan, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.list_query.as_ref().unwrap(),
        lowered.list_query.as_ref().unwrap(),
    );
    assert!(module.rocq_module.contains("CstFloatBits (1089470464)"));
}

#[test]
fn lowers_bare_float_annotation_as_postgres_double() {
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["measurements".to_owned()],
                output: vec![column("id")],
            }),
            exprs: vec![scalar(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "7.5".to_owned(),
                }),
                ty: "FLOAT".to_owned(),
            })],
            correlations: Vec::new(),
            output: vec![typed_column("value", SqlType::Double)],
        },
        output: vec![typed_column("value", SqlType::Double)],
        features: vec![Feature::TableScan, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.list_query.as_ref().unwrap(),
        lowered.list_query.as_ref().unwrap(),
    );
    assert!(
        module
            .rocq_module
            .contains("CstDoubleBits (4620130267728707584)")
    );
}

#[test]
fn rejects_non_finite_float_literals() {
    for raw in ["NaN", "Infinity", "inf", "1e9999"] {
        let query = Query {
            source_sql: None,
            rel: RelExpr::Project {
                input: Box::new(RelExpr::TableScan {
                    table: vec!["measurements".to_owned()],
                    output: vec![column("id")],
                }),
                exprs: vec![scalar(ScalarAst::TypeAnnotation {
                    expr: Box::new(ScalarAst::Literal {
                        raw: raw.to_owned(),
                    }),
                    ty: "DOUBLE".to_owned(),
                })],
                correlations: Vec::new(),
                output: vec![typed_column("value", SqlType::Double)],
            },
            output: vec![typed_column("value", SqlType::Double)],
            features: vec![Feature::TableScan, Feature::Projection],
            calcite_rel_text: None,
            calcite_rel_plan: None,
        };

        let lowered = lower_query(&query);

        assert_eq!(lowered.status, LoweringStatus::Blocked, "{raw}");
        assert!(
            lowered
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "float_literal_not_supported"),
            "{raw}"
        );
    }
}

#[test]
fn lowers_negative_zero_float_literal() {
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["measurements".to_owned()],
                output: vec![column("id")],
            }),
            exprs: vec![scalar(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "-0.0".to_owned(),
                }),
                ty: "DOUBLE".to_owned(),
            })],
            correlations: Vec::new(),
            output: vec![typed_column("value", SqlType::Double)],
        },
        output: vec![typed_column("value", SqlType::Double)],
        features: vec![Feature::TableScan, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.list_query.as_ref().unwrap(),
        lowered.list_query.as_ref().unwrap(),
    );
    assert!(
        module
            .rocq_module
            .contains("CstDoubleBits (9223372036854775808)")
    );
}

#[test]
fn lowers_bare_non_integer_double_literal_output_annotation() {
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["measurements".to_owned()],
                output: vec![column("id")],
            }),
            exprs: vec![scalar(ScalarAst::Literal {
                raw: "7.5".to_owned(),
            })],
            correlations: Vec::new(),
            output: vec![typed_column("value", SqlType::Double)],
        },
        output: vec![typed_column("value", SqlType::Double)],
        features: vec![Feature::TableScan, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.list_query.as_ref().unwrap(),
        lowered.list_query.as_ref().unwrap(),
    );
    assert!(
        module
            .rocq_module
            .contains("CstDoubleBits (4620130267728707584)")
    );
}

#[test]
fn lowers_non_integer_double_literal_in_formula_context() {
    let output = vec![typed_column("value", SqlType::Double)];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Filter {
            input: Box::new(RelExpr::TableScan {
                table: vec!["measurements".to_owned()],
                output: output.clone(),
            }),
            predicate: scalar(ScalarAst::Call {
                operator: "=".to_owned(),
                op: ScalarOp::Eq,
                args: vec![
                    ScalarAst::InputRef { index: 0 },
                    ScalarAst::TypeAnnotation {
                        expr: Box::new(ScalarAst::Literal {
                            raw: "7.5".to_owned(),
                        }),
                        ty: "DOUBLE".to_owned(),
                    },
                ],
            }),
            correlations: Vec::new(),
            output: output.clone(),
        },
        output,
        features: vec![Feature::TableScan, Feature::Selection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.list_query.as_ref().unwrap(),
        lowered.list_query.as_ref().unwrap(),
    );
    assert!(
        module
            .rocq_module
            .contains("CstDoubleBits (4620130267728707584)")
    );
}

#[test]
fn lowers_float_and_double_order_predicates_with_matching_symbols() {
    let float_output = vec![
        typed_column("left_value", SqlType::Float),
        typed_column("right_value", SqlType::Float),
    ];
    let float_query = Query {
        source_sql: None,
        rel: RelExpr::Filter {
            input: Box::new(RelExpr::TableScan {
                table: vec!["measurements".to_owned()],
                output: float_output.clone(),
            }),
            predicate: scalar(ScalarAst::Call {
                operator: ">".to_owned(),
                op: ScalarOp::Gt,
                args: vec![
                    ScalarAst::InputRef { index: 0 },
                    ScalarAst::InputRef { index: 1 },
                ],
            }),
            correlations: Vec::new(),
            output: float_output.clone(),
        },
        output: float_output,
        features: vec![Feature::TableScan, Feature::Selection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };
    let double_output = vec![
        typed_column("left_value", SqlType::Double),
        typed_column("right_value", SqlType::Double),
    ];
    let double_query = Query {
        source_sql: None,
        rel: RelExpr::Filter {
            input: Box::new(RelExpr::TableScan {
                table: vec!["measurements".to_owned()],
                output: double_output.clone(),
            }),
            predicate: scalar(ScalarAst::Call {
                operator: "<".to_owned(),
                op: ScalarOp::Lt,
                args: vec![
                    ScalarAst::InputRef { index: 0 },
                    ScalarAst::InputRef { index: 1 },
                ],
            }),
            correlations: Vec::new(),
            output: double_output.clone(),
        },
        output: double_output,
        features: vec![Feature::TableScan, Feature::Selection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered_float = lower_query(&float_query);
    let lowered_double = lower_query(&double_query);

    assert_eq!(lowered_float.status, LoweringStatus::Lowered);
    assert_eq!(lowered_double.status, LoweringStatus::Lowered);
    let FormalQuery::Selection {
        predicate:
            FormalFormula::Predicate {
                predicate: float_predicate,
                ..
            },
        ..
    } = lowered_float.query.as_ref().unwrap()
    else {
        panic!("expected float selection predicate");
    };
    let FormalQuery::Selection {
        predicate:
            FormalFormula::Predicate {
                predicate: double_predicate,
                ..
            },
        ..
    } = lowered_double.query.as_ref().unwrap()
    else {
        panic!("expected double selection predicate");
    };
    assert_eq!(float_predicate, ">.");
    assert_eq!(double_predicate, "<_double");
}

#[test]
fn rejects_mixed_float_double_equality_predicate() {
    let output = vec![
        typed_column("left_value", SqlType::Float),
        typed_column("right_value", SqlType::Double),
    ];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Filter {
            input: Box::new(RelExpr::TableScan {
                table: vec!["measurements".to_owned()],
                output: output.clone(),
            }),
            predicate: scalar(ScalarAst::Call {
                operator: "=".to_owned(),
                op: ScalarOp::Eq,
                args: vec![
                    ScalarAst::InputRef { index: 0 },
                    ScalarAst::InputRef { index: 1 },
                ],
            }),
            correlations: Vec::new(),
            output: output.clone(),
        },
        output,
        features: vec![Feature::TableScan, Feature::Selection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "floating_comparison_predicate_not_supported")
    );
}

#[test]
fn rejects_floating_order_predicate_in_value_context() {
    let input = vec![
        typed_column("left_value", SqlType::Double),
        typed_column("right_value", SqlType::Double),
    ];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["measurements".to_owned()],
                output: input,
            }),
            exprs: vec![scalar(ScalarAst::Call {
                operator: "<".to_owned(),
                op: ScalarOp::Lt,
                args: vec![
                    ScalarAst::InputRef { index: 0 },
                    ScalarAst::InputRef { index: 1 },
                ],
            })],
            correlations: Vec::new(),
            output: vec![typed_column("is_less", SqlType::Boolean)],
        },
        output: vec![typed_column("is_less", SqlType::Boolean)],
        features: vec![Feature::TableScan, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "floating_order_value_not_supported")
    );
}

#[test]
fn lowers_double_aggregate_with_double_symbol() {
    let input = vec![typed_column("value", SqlType::Double)];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Aggregate {
            input: Box::new(RelExpr::TableScan {
                table: vec!["measurements".to_owned()],
                output: input,
            }),
            group_keys: Vec::new(),
            grouping_sets: Some(vec![Vec::new()]),
            agg_calls: vec![AggregateCall {
                raw: "SUM($0)".to_owned(),
                function: "SUM".to_owned(),
                distinct: false,
                modifiers: AggregateModifiers::default(),
                args: vec![scalar(ScalarAst::InputRef { index: 0 })],
                filter: None,
            }],
            output: vec![typed_column("sum_value", SqlType::Double)],
        },
        output: vec![typed_column("sum_value", SqlType::Double)],
        features: vec![Feature::TableScan, Feature::Aggregation],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.list_query.as_ref().unwrap(),
        lowered.list_query.as_ref().unwrap(),
    );
    assert!(module.rocq_module.contains("AAggregate \"sum_double\""));
}

#[test]
fn rejects_double_aggregate_projected_as_float() {
    let input = vec![typed_column("value", SqlType::Double)];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Aggregate {
            input: Box::new(RelExpr::TableScan {
                table: vec!["measurements".to_owned()],
                output: input,
            }),
            group_keys: Vec::new(),
            grouping_sets: Some(vec![Vec::new()]),
            agg_calls: vec![AggregateCall {
                raw: "SUM($0)".to_owned(),
                function: "SUM".to_owned(),
                distinct: false,
                modifiers: AggregateModifiers::default(),
                args: vec![scalar(ScalarAst::InputRef { index: 0 })],
                filter: None,
            }],
            output: vec![typed_column("sum_value", SqlType::Float)],
        },
        output: vec![typed_column("sum_value", SqlType::Float)],
        features: vec![Feature::TableScan, Feature::Aggregation],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered.diagnostics.iter().any(|diagnostic| {
            diagnostic.code == "floating_aggregate_output_type_not_supported"
        })
    );
}

#[test]
fn rejects_unknown_arg_type_aggregate_projected_as_double() {
    let query = Query {
        source_sql: None,
        rel: RelExpr::Aggregate {
            input: Box::new(RelExpr::TableScan {
                table: vec!["measurements".to_owned()],
                output: vec![column("id")],
            }),
            group_keys: Vec::new(),
            grouping_sets: Some(vec![Vec::new()]),
            agg_calls: vec![AggregateCall {
                raw: "SUM(7)".to_owned(),
                function: "SUM".to_owned(),
                distinct: false,
                modifiers: AggregateModifiers::default(),
                args: vec![scalar(ScalarAst::Literal {
                    raw: "7".to_owned(),
                })],
                filter: None,
            }],
            output: vec![typed_column("sum_value", SqlType::Double)],
        },
        output: vec![typed_column("sum_value", SqlType::Double)],
        features: vec![Feature::TableScan, Feature::Aggregation],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered.diagnostics.iter().any(|diagnostic| {
            diagnostic.code == "floating_aggregate_argument_type_not_supported"
        })
    );
}

#[test]
fn count_over_double_still_returns_integer_count() {
    let input = vec![typed_column("value", SqlType::Double)];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Aggregate {
            input: Box::new(RelExpr::TableScan {
                table: vec!["measurements".to_owned()],
                output: input,
            }),
            group_keys: Vec::new(),
            grouping_sets: Some(vec![Vec::new()]),
            agg_calls: vec![AggregateCall {
                raw: "COUNT($0)".to_owned(),
                function: "COUNT".to_owned(),
                distinct: false,
                modifiers: AggregateModifiers::default(),
                args: vec![scalar(ScalarAst::InputRef { index: 0 })],
                filter: None,
            }],
            output: vec![typed_column("count_value", SqlType::BigInt)],
        },
        output: vec![typed_column("count_value", SqlType::BigInt)],
        features: vec![Feature::TableScan, Feature::Aggregation],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
}

#[test]
fn lowers_case_expression_as_structured_branches() {
    let table_output = vec![column("a")];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: table_output,
            }),
            exprs: vec![scalar(ScalarAst::Call {
                operator: "CASE".to_owned(),
                op: ScalarOp::Case,
                args: vec![
                    ScalarAst::Call {
                        operator: "AND".to_owned(),
                        op: ScalarOp::And,
                        args: vec![
                            ScalarAst::Call {
                                operator: "IS NULL".to_owned(),
                                op: ScalarOp::IsNull,
                                args: vec![ScalarAst::InputRef { index: 0 }],
                            },
                            ScalarAst::Call {
                                operator: "IS NOT NULL".to_owned(),
                                op: ScalarOp::IsNotNull,
                                args: vec![ScalarAst::InputRef { index: 0 }],
                            },
                            ScalarAst::Literal {
                                raw: "true".to_owned(),
                            },
                        ],
                    },
                    ScalarAst::Literal {
                        raw: "1".to_owned(),
                    },
                    ScalarAst::Literal {
                        raw: "0".to_owned(),
                    },
                ],
            })],
            correlations: Vec::new(),
            output: vec![column("case_value")],
        },
        output: vec![column("case_value")],
        features: vec![Feature::TableScan, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);
    let module = emit_rocq_query_module(
        lowered
            .list_query
            .as_ref()
            .expect("CASE expression should lower"),
        lowered
            .list_query
            .as_ref()
            .expect("CASE expression should lower"),
    );

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert!(
        !lowered.diagnostics.iter().any(|diagnostic| {
            diagnostic.code == "aggregate_term_symbol_interpretation_required"
        })
    );
    let project = match lowered.query.as_ref().expect("query should lower") {
        FormalQuery::Projection { select, .. } => &select[0].expr,
        other => panic!("expected projection query, got {other:?}"),
    };
    let FormalAggregateTerm::Case { branches, .. } = project else {
        panic!("expected CASE aggregate term, got {project:?}");
    };
    assert!(matches!(
        &branches[0].when,
        FormalAggregateTerm::Function { symbol, args }
            if symbol == "and"
                && args.len() == 2
                && matches!(&args[0], FormalAggregateTerm::Function { symbol, args } if symbol == "and" && args.len() == 2)
    ));
    assert!(module.rocq_module.contains("AFunction \"case\""));
    assert!(module.rocq_module.contains("AFunction \"is_null\""));
}

#[test]
fn lowers_schema_to_formal_sql_create_table_shape() {
    let schema = Schema {
        tables: vec![Table {
            name: "EMP".to_owned(),
            columns: vec![
                typed_column("EMPNO", SqlType::Integer),
                typed_column("ENAME", SqlType::Varchar),
                typed_column("SLACKER", SqlType::Boolean),
                typed_column("HIREDATE", SqlType::Date),
                decimal_column("BONUS", 10, 2),
                typed_column("SHIFT_START", SqlType::Time),
                timestamp_column("EVENT_TS", Some(6)),
            ],
        }],
    };

    let lowered = lower_schema(&schema);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert_eq!(
        lowered.schema.as_ref().unwrap().tables[0].attributes.len(),
        7
    );
    assert!(
        lowered
            .schema
            .as_ref()
            .unwrap()
            .rocq_create_schema
            .contains("create_table")
    );
    assert!(
            lowered
                .schema
                .as_ref()
                .unwrap()
                .rocq_create_schema
                .contains("Attr_Z \"EMPNO\" :: Attr_string \"ENAME\" :: Attr_bool \"SLACKER\" :: Attr_date \"HIREDATE\" :: Attr_decimal \"BONUS\" 10 2 :: Attr_time \"SHIFT_START\" :: Attr_timestamp \"EVENT_TS\" 6 :: nil")
        );
    assert!(
        lowered
            .schema
            .as_ref()
            .unwrap()
            .rocq_module
            .starts_with("From SQLFS Require Import SqlSyntax GenericInstance.\n")
    );
    assert!(
        lowered
            .schema
            .as_ref()
            .unwrap()
            .rocq_module
            .contains("Definition generated_schema :=\n")
    );
    assert!(
        lowered.diagnostics.is_empty(),
        "schema-only lowering should not warn for supported temporal columns"
    );
}

#[test]
fn lowers_time_schema_attribute() {
    let schema = Schema {
        tables: vec![Table {
            name: "t".to_owned(),
            columns: vec![typed_column("clock_time", SqlType::Time)],
        }],
    };

    let lowered = lower_schema(&schema);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert!(
        lowered
            .schema
            .as_ref()
            .unwrap()
            .rocq_create_schema
            .contains("Attr_time \"clock_time\"")
    );
}

#[test]
fn lowers_time_query_attribute() {
    let output = vec![typed_column("clock_time", SqlType::Time)];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: output.clone(),
            }),
            exprs: vec![scalar(ScalarAst::InputRef { index: 0 })],
            correlations: Vec::new(),
            output: output.clone(),
        },
        output,
        features: vec![Feature::TableScan, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.list_query.as_ref().unwrap(),
        lowered.list_query.as_ref().unwrap(),
    );
    assert!(module.rocq_module.contains("TimeColumn \"clock_time\""));
}

#[test]
fn lowers_time_literals() {
    let output = vec![typed_column("clock_time", SqlType::Time)];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: vec![column("id")],
            }),
            exprs: vec![scalar(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "'12:34:56.123456'".to_owned(),
                }),
                ty: "TIME".to_owned(),
            })],
            correlations: Vec::new(),
            output: output.clone(),
        },
        output,
        features: vec![Feature::TableScan, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.list_query.as_ref().unwrap(),
        lowered.list_query.as_ref().unwrap(),
    );
    assert!(module.rocq_module.contains("CstTime (45296123456)"));
}

#[test]
fn rejects_invalid_project_time_literal() {
    let output = vec![typed_column("clock_time", SqlType::Time)];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: vec![column("id")],
            }),
            exprs: vec![scalar(ScalarAst::Literal {
                raw: "'25:00:00'".to_owned(),
            })],
            correlations: Vec::new(),
            output: output.clone(),
        },
        output,
        features: vec![Feature::TableScan, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "time_literal_not_supported")
    );
}

#[test]
fn rejects_invalid_values_time_literal() {
    let output = vec![typed_column("clock_time", SqlType::Time)];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Values {
            tuples: ValuesTuples::Rows {
                rows: vec![vec![scalar(ScalarAst::Literal {
                    raw: "'25:00:00'".to_owned(),
                })]],
            },
            output: output.clone(),
        },
        output,
        features: vec![Feature::Values],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "time_literal_not_supported")
    );
}

#[test]
fn rejects_decimal_schema_with_zero_precision() {
    let schema = Schema {
        tables: vec![Table {
            name: "t".to_owned(),
            columns: vec![decimal_column("amount", 0, 0)],
        }],
    };

    let lowered = lower_schema(&schema);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "decimal_typmod_not_supported")
    );
}

#[test]
fn lowers_decimal_literal_and_arithmetic() {
    let input = vec![decimal_column("amount", 10, 2)];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: input,
            }),
            exprs: vec![scalar(ScalarAst::Call {
                operator: "+".to_owned(),
                op: ScalarOp::Plus,
                args: vec![
                    ScalarAst::InputRef { index: 0 },
                    ScalarAst::TypeAnnotation {
                        expr: Box::new(ScalarAst::Literal {
                            raw: "1.25".to_owned(),
                        }),
                        ty: "DECIMAL(10, 2)".to_owned(),
                    },
                ],
            })],
            correlations: Vec::new(),
            output: vec![decimal_column("amount_plus", 11, 2)],
        },
        output: vec![decimal_column("amount_plus", 11, 2)],
        features: vec![Feature::TableScan, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered
            .list_query
            .as_ref()
            .expect("decimal query should lower"),
        lowered
            .list_query
            .as_ref()
            .expect("decimal query should lower"),
    );
    assert!(module.rocq_module.contains("AFunction \"plus_decimal\""));
    assert!(module.rocq_module.contains("CstDecimal (10) (2) (125)"));
    assert!(
        module
            .rocq_module
            .contains("AttrDecimal \"amount_plus\" 11 2")
    );
}

#[test]
fn rejects_decimal_arithmetic_output_typmod_mismatch() {
    let input = vec![decimal_column("amount", 10, 2)];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: input,
            }),
            exprs: vec![scalar(ScalarAst::Call {
                operator: "+".to_owned(),
                op: ScalarOp::Plus,
                args: vec![
                    ScalarAst::InputRef { index: 0 },
                    ScalarAst::TypeAnnotation {
                        expr: Box::new(ScalarAst::Literal {
                            raw: "1.25".to_owned(),
                        }),
                        ty: "DECIMAL(10, 2)".to_owned(),
                    },
                ],
            })],
            correlations: Vec::new(),
            output: vec![decimal_column("amount_plus", 10, 2)],
        },
        output: vec![decimal_column("amount_plus", 10, 2)],
        features: vec![Feature::TableScan, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "decimal_output_typmod_not_supported")
    );
}

#[test]
fn rescales_decimal_literals_to_target_scale() {
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: vec![column("id")],
            }),
            exprs: vec![scalar(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "1.2".to_owned(),
                }),
                ty: "DECIMAL(10, 2)".to_owned(),
            })],
            correlations: Vec::new(),
            output: vec![decimal_column("amount", 10, 2)],
        },
        output: vec![decimal_column("amount", 10, 2)],
        features: vec![Feature::TableScan, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered
            .list_query
            .as_ref()
            .expect("decimal query should lower"),
        lowered
            .list_query
            .as_ref()
            .expect("decimal query should lower"),
    );
    assert!(module.rocq_module.contains("CstDecimal (10) (2) (120)"));
}

#[test]
fn rounds_decimal_literals_to_target_scale() {
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: vec![column("id")],
            }),
            exprs: vec![scalar(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "1.235".to_owned(),
                }),
                ty: "DECIMAL(10, 2)".to_owned(),
            })],
            correlations: Vec::new(),
            output: vec![decimal_column("amount", 10, 2)],
        },
        output: vec![decimal_column("amount", 10, 2)],
        features: vec![Feature::TableScan, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.list_query.as_ref().unwrap(),
        lowered.list_query.as_ref().unwrap(),
    );
    assert!(module.rocq_module.contains("CstDecimal (10) (2) (124)"));
}

#[test]
fn rejects_decimal_literal_precision_overflow_after_rounding() {
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: vec![column("id")],
            }),
            exprs: vec![scalar(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "999.95".to_owned(),
                }),
                ty: "DECIMAL(4, 1)".to_owned(),
            })],
            correlations: Vec::new(),
            output: vec![decimal_column("amount", 4, 1)],
        },
        output: vec![decimal_column("amount", 4, 1)],
        features: vec![Feature::TableScan, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "decimal_literal_not_supported")
    );
}

#[test]
fn decimal_annotation_without_scale_defaults_to_zero() {
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: vec![column("id")],
            }),
            exprs: vec![scalar(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "1.2".to_owned(),
                }),
                ty: "DECIMAL(10)".to_owned(),
            })],
            correlations: Vec::new(),
            output: vec![decimal_column("amount", 10, 0)],
        },
        output: vec![decimal_column("amount", 10, 0)],
        features: vec![Feature::TableScan, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.list_query.as_ref().unwrap(),
        lowered.list_query.as_ref().unwrap(),
    );
    assert!(module.rocq_module.contains("CstDecimal (10) (0) (1)"));
}

#[test]
fn rejects_malformed_decimal_annotation() {
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: vec![column("id")],
            }),
            exprs: vec![scalar(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "1.2".to_owned(),
                }),
                ty: "DECIMAL(10, -2)".to_owned(),
            })],
            correlations: Vec::new(),
            output: vec![decimal_column("amount", 10, 2)],
        },
        output: vec![decimal_column("amount", 10, 2)],
        features: vec![Feature::TableScan, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "decimal_typmod_not_supported")
    );
}

#[test]
fn rejects_bare_decimal_annotation() {
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: vec![column("id")],
            }),
            exprs: vec![scalar(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "1.2".to_owned(),
                }),
                ty: "DECIMAL".to_owned(),
            })],
            correlations: Vec::new(),
            output: vec![decimal_column("amount", 10, 2)],
        },
        output: vec![decimal_column("amount", 10, 2)],
        features: vec![Feature::TableScan, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "decimal_typmod_not_supported")
    );
}

#[test]
fn rejects_untyped_decimal_literal_overflow_for_output_typmod() {
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: vec![column("id")],
            }),
            exprs: vec![scalar(ScalarAst::Literal {
                raw: "999.95".to_owned(),
            })],
            correlations: Vec::new(),
            output: vec![decimal_column("amount", 4, 1)],
        },
        output: vec![decimal_column("amount", 4, 1)],
        features: vec![Feature::TableScan, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "decimal_literal_not_supported")
    );
}

#[test]
fn rejects_unmodeled_decimal_functions() {
    let input = vec![decimal_column("amount", 10, 2)];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: input,
            }),
            exprs: vec![scalar(ScalarAst::Call {
                operator: "POWER".to_owned(),
                op: ScalarOp::Power,
                args: vec![
                    ScalarAst::InputRef { index: 0 },
                    ScalarAst::Literal {
                        raw: "2".to_owned(),
                    },
                ],
            })],
            correlations: Vec::new(),
            output: vec![decimal_column("amount_squared", 20, 4)],
        },
        output: vec![decimal_column("amount_squared", 20, 4)],
        features: vec![Feature::TableScan, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "decimal_function_not_supported")
    );
}

#[test]
fn lowers_nested_decimal_arithmetic() {
    let input = vec![decimal_column("amount", 10, 2)];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: input,
            }),
            exprs: vec![scalar(ScalarAst::Call {
                operator: "*".to_owned(),
                op: ScalarOp::Multiply,
                args: vec![
                    ScalarAst::Call {
                        operator: "+".to_owned(),
                        op: ScalarOp::Plus,
                        args: vec![
                            ScalarAst::InputRef { index: 0 },
                            ScalarAst::TypeAnnotation {
                                expr: Box::new(ScalarAst::Literal {
                                    raw: "1.25".to_owned(),
                                }),
                                ty: "DECIMAL(10, 2)".to_owned(),
                            },
                        ],
                    },
                    ScalarAst::InputRef { index: 0 },
                ],
            })],
            correlations: Vec::new(),
            output: vec![decimal_column("amount_scaled", 21, 4)],
        },
        output: vec![decimal_column("amount_scaled", 21, 4)],
        features: vec![Feature::TableScan, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered
            .list_query
            .as_ref()
            .expect("decimal query should lower"),
        lowered
            .list_query
            .as_ref()
            .expect("decimal query should lower"),
    );
    assert!(module.rocq_module.contains("AFunction \"plus_decimal\""));
    assert!(module.rocq_module.contains("AFunction \"mult_decimal\""));
}

#[test]
fn lowers_decimal_typmod_cast() {
    let input = vec![decimal_column("amount", 7, 2)];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: input,
            }),
            exprs: vec![scalar(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Call {
                    operator: "CAST".to_owned(),
                    op: ScalarOp::Cast,
                    args: vec![ScalarAst::InputRef { index: 0 }],
                }),
                ty: "DECIMAL(12, 2)".to_owned(),
            })],
            correlations: Vec::new(),
            output: vec![decimal_column("amount_cast", 12, 2)],
        },
        output: vec![decimal_column("amount_cast", 12, 2)],
        features: vec![Feature::TableScan, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.list_query.as_ref().unwrap(),
        lowered.list_query.as_ref().unwrap(),
    );
    assert!(
        module
            .rocq_module
            .contains("AFunction \"cast_decimal_typmod\"")
    );
    assert!(module.rocq_module.contains("CstZ (12)"));
    assert!(module.rocq_module.contains("CstZ (2)"));
}

#[test]
fn lowers_integer_to_decimal_typmod_cast() {
    let input = vec![column("amount_int")];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: input,
            }),
            exprs: vec![scalar(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Call {
                    operator: "CAST".to_owned(),
                    op: ScalarOp::Cast,
                    args: vec![ScalarAst::InputRef { index: 0 }],
                }),
                ty: "DECIMAL(12, 2)".to_owned(),
            })],
            correlations: Vec::new(),
            output: vec![decimal_column("amount_decimal", 12, 2)],
        },
        output: vec![decimal_column("amount_decimal", 12, 2)],
        features: vec![Feature::TableScan, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.list_query.as_ref().unwrap(),
        lowered.list_query.as_ref().unwrap(),
    );
    assert!(
        module
            .rocq_module
            .contains("AFunction \"cast_z_to_decimal_typmod\"")
    );
    assert!(module.rocq_module.contains("CstZ (12)"));
    assert!(module.rocq_module.contains("CstZ (2)"));
}

#[test]
fn infers_integer_cast_source_from_case_division() {
    let input = vec![column("amount"), column("count")];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: input,
            }),
            exprs: vec![scalar(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Call {
                    operator: "CAST".to_owned(),
                    op: ScalarOp::Cast,
                    args: vec![ScalarAst::Call {
                        operator: "/".to_owned(),
                        op: ScalarOp::Divide,
                        args: vec![
                            ScalarAst::Call {
                                operator: "CASE".to_owned(),
                                op: ScalarOp::Case,
                                args: vec![
                                    ScalarAst::Call {
                                        operator: "IS NOT NULL".to_owned(),
                                        op: ScalarOp::IsNotNull,
                                        args: vec![ScalarAst::InputRef { index: 0 }],
                                    },
                                    ScalarAst::TypeAnnotation {
                                        expr: Box::new(ScalarAst::Call {
                                            operator: "CAST".to_owned(),
                                            op: ScalarOp::Cast,
                                            args: vec![ScalarAst::InputRef { index: 0 }],
                                        }),
                                        ty: "INTEGER".to_owned(),
                                    },
                                    ScalarAst::Literal {
                                        raw: "0".to_owned(),
                                    },
                                ],
                            },
                            ScalarAst::InputRef { index: 1 },
                        ],
                    }],
                }),
                ty: "INTEGER".to_owned(),
            })],
            correlations: Vec::new(),
            output: vec![column("average_amount")],
        },
        output: vec![column("average_amount")],
        features: vec![Feature::TableScan, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert!(
        !lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "cast_source_expression_not_supported")
    );
}

#[test]
fn infers_power_cast_source_as_double_before_rejecting_cast_pair() {
    let input = vec![typed_column("amount", SqlType::Double)];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: input,
            }),
            exprs: vec![scalar(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Call {
                    operator: "CAST".to_owned(),
                    op: ScalarOp::Cast,
                    args: vec![ScalarAst::Call {
                        operator: "POWER".to_owned(),
                        op: ScalarOp::Power,
                        args: vec![
                            ScalarAst::InputRef { index: 0 },
                            ScalarAst::TypeAnnotation {
                                expr: Box::new(ScalarAst::Literal {
                                    raw: "2.0".to_owned(),
                                }),
                                ty: "DOUBLE".to_owned(),
                            },
                        ],
                    }],
                }),
                ty: "INTEGER".to_owned(),
            })],
            correlations: Vec::new(),
            output: vec![column("powered_amount")],
        },
        output: vec![column("powered_amount")],
        features: vec![Feature::TableScan, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "cast_not_supported")
    );
    assert!(
        !lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "cast_source_expression_not_supported")
    );
}

#[test]
fn rejects_case_cast_source_with_incompatible_literal_branch() {
    let input = vec![typed_column("date_value", SqlType::Date)];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: input,
            }),
            exprs: vec![scalar(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Call {
                    operator: "CAST".to_owned(),
                    op: ScalarOp::Cast,
                    args: vec![ScalarAst::Call {
                        operator: "CASE".to_owned(),
                        op: ScalarOp::Case,
                        args: vec![
                            ScalarAst::Literal {
                                raw: "true".to_owned(),
                            },
                            ScalarAst::Literal {
                                raw: "'bad-date'".to_owned(),
                            },
                            ScalarAst::InputRef { index: 0 },
                        ],
                    }],
                }),
                ty: "DATE".to_owned(),
            })],
            correlations: Vec::new(),
            output: vec![typed_column("date_cast", SqlType::Date)],
        },
        output: vec![typed_column("date_cast", SqlType::Date)],
        features: vec![Feature::TableScan, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "cast_source_expression_not_supported")
    );
}

#[test]
fn infers_string_literal_cast_source_before_rejecting_cast_pair() {
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: vec![column("id")],
            }),
            exprs: vec![scalar(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Call {
                    operator: "CAST".to_owned(),
                    op: ScalarOp::Cast,
                    args: vec![ScalarAst::Literal {
                        raw: "'SECURITY'".to_owned(),
                    }],
                }),
                ty: "INTEGER".to_owned(),
            })],
            correlations: Vec::new(),
            output: vec![column("bad_cast")],
        },
        output: vec![column("bad_cast")],
        features: vec![Feature::TableScan, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "cast_not_supported")
    );
    assert!(
        !lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "cast_source_type_not_supported")
    );
}

#[test]
fn rejects_bare_decimal_division_projected_to_fixed_typmod() {
    let input = vec![decimal_column("left_amount", 10, 2)];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: input,
            }),
            exprs: vec![scalar(ScalarAst::Call {
                operator: "/".to_owned(),
                op: ScalarOp::Divide,
                args: vec![
                    ScalarAst::InputRef { index: 0 },
                    ScalarAst::TypeAnnotation {
                        expr: Box::new(ScalarAst::Literal {
                            raw: "2.00".to_owned(),
                        }),
                        ty: "DECIMAL(10, 2)".to_owned(),
                    },
                ],
            })],
            correlations: Vec::new(),
            output: vec![decimal_column("ratio", 19, 6)],
        },
        output: vec![decimal_column("ratio", 19, 6)],
        features: vec![Feature::TableScan, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "decimal_division_output_typmod_not_supported")
    );
}

#[test]
fn decimal_division_uses_result_annotation_scale() {
    let input = vec![decimal_column("left_amount", 4, 2)];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: input,
            }),
            exprs: vec![scalar(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Call {
                    operator: "/".to_owned(),
                    op: ScalarOp::Divide,
                    args: vec![
                        ScalarAst::InputRef { index: 0 },
                        ScalarAst::TypeAnnotation {
                            expr: Box::new(ScalarAst::Literal {
                                raw: "2.00".to_owned(),
                            }),
                            ty: "DECIMAL(4, 2)".to_owned(),
                        },
                    ],
                }),
                ty: "DECIMAL(10, 2)".to_owned(),
            })],
            correlations: Vec::new(),
            output: vec![decimal_column("ratio", 10, 2)],
        },
        output: vec![decimal_column("ratio", 10, 2)],
        features: vec![Feature::TableScan, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.list_query.as_ref().unwrap(),
        lowered.list_query.as_ref().unwrap(),
    );
    assert!(
        module
            .rocq_module
            .contains("AFunction \"divide_decimal_typmod\"")
    );
    assert!(module.rocq_module.contains("CstZ (10)"));
    assert!(module.rocq_module.contains("CstZ (2)"));
}

#[test]
fn rejects_decimal_division_without_static_nonzero_divisor() {
    let input = vec![
        decimal_column("left_amount", 10, 2),
        decimal_column("right_amount", 10, 2),
    ];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: input,
            }),
            exprs: vec![scalar(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Call {
                    operator: "/".to_owned(),
                    op: ScalarOp::Divide,
                    args: vec![
                        ScalarAst::InputRef { index: 0 },
                        ScalarAst::InputRef { index: 1 },
                    ],
                }),
                ty: "DECIMAL(19, 6)".to_owned(),
            })],
            correlations: Vec::new(),
            output: vec![decimal_column("ratio", 19, 6)],
        },
        output: vec![decimal_column("ratio", 19, 6)],
        features: vec![Feature::TableScan, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "decimal_divisor_not_statically_nonzero")
    );
}

#[test]
fn rejects_decimal_division_when_divisor_cast_rounds_to_zero() {
    let input = vec![decimal_column("left_amount", 10, 2)];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: input,
            }),
            exprs: vec![scalar(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Call {
                    operator: "/".to_owned(),
                    op: ScalarOp::Divide,
                    args: vec![
                        ScalarAst::InputRef { index: 0 },
                        ScalarAst::TypeAnnotation {
                            expr: Box::new(ScalarAst::Literal {
                                raw: "0.004".to_owned(),
                            }),
                            ty: "DECIMAL(10, 2)".to_owned(),
                        },
                    ],
                }),
                ty: "DECIMAL(19, 6)".to_owned(),
            })],
            correlations: Vec::new(),
            output: vec![decimal_column("ratio", 19, 6)],
        },
        output: vec![decimal_column("ratio", 19, 6)],
        features: vec![Feature::TableScan, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "decimal_divisor_not_statically_nonzero")
    );
}

#[test]
fn rejects_mixed_decimal_arithmetic() {
    let input = vec![decimal_column("amount", 10, 2)];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: input,
            }),
            exprs: vec![scalar(ScalarAst::Call {
                operator: "+".to_owned(),
                op: ScalarOp::Plus,
                args: vec![
                    ScalarAst::InputRef { index: 0 },
                    ScalarAst::Literal {
                        raw: "1".to_owned(),
                    },
                ],
            })],
            correlations: Vec::new(),
            output: vec![decimal_column("amount_plus", 10, 2)],
        },
        output: vec![decimal_column("amount_plus", 10, 2)],
        features: vec![Feature::TableScan, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "decimal_mixed_arithmetic_not_supported")
    );
}

#[test]
fn rejects_decimal_avg_aggregate() {
    let input_output = vec![decimal_column("amount", 10, 2)];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Aggregate {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: input_output,
            }),
            group_keys: Vec::new(),
            grouping_sets: Some(vec![Vec::new()]),
            agg_calls: vec![AggregateCall {
                raw: "AVG($0)".to_owned(),
                function: "AVG".to_owned(),
                distinct: false,
                modifiers: AggregateModifiers::default(),
                args: vec![scalar(ScalarAst::InputRef { index: 0 })],
                filter: None,
            }],
            output: vec![decimal_column("avg_amount", 10, 2)],
        },
        output: vec![decimal_column("avg_amount", 10, 2)],
        features: vec![Feature::Aggregation],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(lowered.diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "decimal_aggregate_unconstrained_numeric_not_supported"
    }));
}

#[test]
fn rejects_decimal_avg_with_fixed_output_scale() {
    let input_output = vec![decimal_column("amount", 10, 2)];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Aggregate {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: input_output,
            }),
            group_keys: Vec::new(),
            grouping_sets: Some(vec![Vec::new()]),
            agg_calls: vec![AggregateCall {
                raw: "AVG($0)".to_owned(),
                function: "AVG".to_owned(),
                distinct: false,
                modifiers: AggregateModifiers::default(),
                args: vec![scalar(ScalarAst::InputRef { index: 0 })],
                filter: None,
            }],
            output: vec![decimal_column("avg_amount", 10, 3)],
        },
        output: vec![decimal_column("avg_amount", 10, 3)],
        features: vec![Feature::Aggregation],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(lowered.diagnostics.iter().any(
        |diagnostic| diagnostic.code == "decimal_aggregate_unconstrained_numeric_not_supported"
    ));
}

#[test]
fn rejects_decimal_sum_aggregate() {
    let input_output = vec![decimal_column("amount", 10, 2)];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Aggregate {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: input_output,
            }),
            group_keys: Vec::new(),
            grouping_sets: Some(vec![Vec::new()]),
            agg_calls: vec![AggregateCall {
                raw: "SUM($0)".to_owned(),
                function: "SUM".to_owned(),
                distinct: false,
                modifiers: AggregateModifiers::default(),
                args: vec![scalar(ScalarAst::InputRef { index: 0 })],
                filter: None,
            }],
            output: vec![decimal_column("sum_amount", 10, 2)],
        },
        output: vec![decimal_column("sum_amount", 10, 2)],
        features: vec![Feature::Aggregation],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(lowered.diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "decimal_aggregate_unconstrained_numeric_not_supported"
    }));
}

#[test]
fn rejects_decimal_min_output_typmod_mismatch() {
    let input_output = vec![decimal_column("amount", 10, 2)];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Aggregate {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: input_output,
            }),
            group_keys: Vec::new(),
            grouping_sets: Some(vec![Vec::new()]),
            agg_calls: vec![AggregateCall {
                raw: "MIN($0)".to_owned(),
                function: "MIN".to_owned(),
                distinct: false,
                modifiers: AggregateModifiers::default(),
                args: vec![scalar(ScalarAst::InputRef { index: 0 })],
                filter: None,
            }],
            output: vec![decimal_column("min_amount", 10, 3)],
        },
        output: vec![decimal_column("min_amount", 10, 3)],
        features: vec![Feature::Aggregation],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "decimal_output_typmod_not_supported")
    );
}

#[test]
fn rejects_unconstrained_decimal_input_scope() {
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: vec![decimal_column_unconstrained("amount")],
            }),
            exprs: vec![scalar(ScalarAst::InputRef { index: 0 })],
            correlations: Vec::new(),
            output: vec![decimal_column("amount", 10, 2)],
        },
        output: vec![decimal_column("amount", 10, 2)],
        features: vec![Feature::TableScan, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "unconstrained_numeric_not_supported")
    );
}

#[test]
fn rejects_unconstrained_decimal_table_scan_output() {
    let query = Query {
        source_sql: None,
        rel: RelExpr::TableScan {
            table: vec!["t".to_owned()],
            output: vec![decimal_column_unconstrained("amount")],
        },
        output: vec![decimal_column_unconstrained("amount")],
        features: vec![Feature::TableScan],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "unconstrained_numeric_not_supported")
    );
}

#[test]
fn rejects_invalid_decimal_input_scope_typmod() {
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: vec![decimal_column("amount", 0, 0)],
            }),
            exprs: vec![scalar(ScalarAst::InputRef { index: 0 })],
            correlations: Vec::new(),
            output: vec![decimal_column("amount", 10, 2)],
        },
        output: vec![decimal_column("amount", 10, 2)],
        features: vec![Feature::TableScan, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "decimal_typmod_not_supported")
    );
}

#[test]
fn lowers_timestamp_literals_and_interval_arithmetic() {
    let output = vec![typed_column("ts", SqlType::timestamp(None))];
    let timestamp_literal = ScalarAst::TypeAnnotation {
        expr: Box::new(ScalarAst::Literal {
            raw: "'1970-01-01 00:00:01.000001'".to_owned(),
        }),
        ty: "TIMESTAMP".to_owned(),
    };
    let timestamp_plus_interval = ScalarAst::Call {
        operator: "+".to_owned(),
        op: ScalarOp::Plus,
        args: vec![
            ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "'1970-01-01 00:00:00'".to_owned(),
                }),
                ty: "TIMESTAMP".to_owned(),
            },
            ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "1".to_owned(),
                }),
                ty: "INTERVAL SECOND".to_owned(),
            },
        ],
    };
    let make_query = |rhs| Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::Filter {
                input: Box::new(RelExpr::TableScan {
                    table: vec!["t".to_owned()],
                    output: output.clone(),
                }),
                predicate: scalar(ScalarAst::Call {
                    operator: "<".to_owned(),
                    op: ScalarOp::Lt,
                    args: vec![ScalarAst::InputRef { index: 0 }, rhs],
                }),
                correlations: Vec::new(),
                output: output.clone(),
            }),
            exprs: vec![scalar(ScalarAst::InputRef { index: 0 })],
            correlations: Vec::new(),
            output: output.clone(),
        },
        output: output.clone(),
        features: vec![Feature::TableScan, Feature::Selection, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let source = lower_query(&make_query(timestamp_literal));
    let target = lower_query(&make_query(timestamp_plus_interval));
    assert_eq!(source.status, LoweringStatus::Lowered);
    assert_eq!(target.status, LoweringStatus::Lowered);

    let module = emit_rocq_query_module(
        source.list_query.as_ref().unwrap(),
        target.list_query.as_ref().unwrap(),
    );
    assert!(module.rocq_module.contains("TimestampColumn \"ts\" 6"));
    assert!(module.rocq_module.contains("CstTimestamp (1000001)"));
    assert!(
        module
            .rocq_module
            .contains("AFunction \"timestamp_add_seconds\"")
    );
}

#[test]
fn lowers_date_to_timestamp_cast() {
    let input = vec![typed_column("HIREDATE", SqlType::Date)];
    let output = vec![timestamp_column("ts", Some(0))];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["emp".to_owned()],
                output: input.clone(),
            }),
            exprs: vec![scalar(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Call {
                    operator: "CAST".to_owned(),
                    op: ScalarOp::Cast,
                    args: vec![ScalarAst::InputRef { index: 0 }],
                }),
                ty: "TIMESTAMP(0)".to_owned(),
            })],
            correlations: Vec::new(),
            output: output.clone(),
        },
        output,
        features: vec![Feature::TableScan, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.list_query.as_ref().unwrap(),
        lowered.list_query.as_ref().unwrap(),
    );
    assert!(module.rocq_module.contains("AttrTimestamp \"ts\" 0"));
    assert!(
        module
            .rocq_module
            .contains("Function \"cast_date_to_timestamp\"")
    );
}

#[test]
fn lowers_timestamp_to_date_cast() {
    let input = vec![timestamp_column("ts", Some(6))];
    let output = vec![typed_column("d", SqlType::Date)];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["events".to_owned()],
                output: input.clone(),
            }),
            exprs: vec![scalar(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Call {
                    operator: "CAST".to_owned(),
                    op: ScalarOp::Cast,
                    args: vec![ScalarAst::InputRef { index: 0 }],
                }),
                ty: "DATE".to_owned(),
            })],
            correlations: Vec::new(),
            output: output.clone(),
        },
        output,
        features: vec![Feature::TableScan, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.list_query.as_ref().unwrap(),
        lowered.list_query.as_ref().unwrap(),
    );
    assert!(module.rocq_module.contains("AttrDate \"d\""));
    assert!(
        module
            .rocq_module
            .contains("Function \"cast_timestamp_to_date\"")
    );
}

#[test]
fn normalizes_timestamp_tz_literals_with_configured_time_zone() {
    let output = vec![typed_column("ts", SqlType::timestamptz(None))];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: output.clone(),
            }),
            exprs: vec![scalar(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "'1970-01-01 08:00:00+08:00'".to_owned(),
                }),
                ty: "TIMESTAMP_WITH_TIME_ZONE(6)".to_owned(),
            })],
            correlations: Vec::new(),
            output: output.clone(),
        },
        output,
        features: vec![Feature::TableScan, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query_with_config(
        &query,
        &LoweringConfig {
            sql_time_zone: SqlTimeZone::parse("UTC"),
        },
    );

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.list_query.as_ref().unwrap(),
        lowered.list_query.as_ref().unwrap(),
    );
    assert!(module.rocq_module.contains("CstTimestamptz (0)"));
}

#[test]
fn normalizes_timestamp_tz_literals_with_named_time_zone() {
    let output = vec![typed_column("ts", SqlType::timestamptz(None))];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: output.clone(),
            }),
            exprs: vec![scalar(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "'1970-01-01 00:00:00+00:00'".to_owned(),
                }),
                ty: "TIMESTAMP_WITH_TIME_ZONE(6)".to_owned(),
            })],
            correlations: Vec::new(),
            output: output.clone(),
        },
        output,
        features: vec![Feature::TableScan, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query_with_config(
        &query,
        &LoweringConfig {
            sql_time_zone: SqlTimeZone::parse("Asia/Shanghai"),
        },
    );

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.list_query.as_ref().unwrap(),
        lowered.list_query.as_ref().unwrap(),
    );
    assert!(module.rocq_module.contains("CstTimestamptz (0)"));
}

#[test]
fn accepts_timestamp_tz_local_literal_in_named_time_zone() {
    let output = vec![typed_column("ts", SqlType::timestamptz(None))];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: output.clone(),
            }),
            exprs: vec![scalar(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "'1970-01-01 08:00:00'".to_owned(),
                }),
                ty: "TIMESTAMP_WITH_TIME_ZONE(6)".to_owned(),
            })],
            correlations: Vec::new(),
            output: output.clone(),
        },
        output,
        features: vec![Feature::TableScan, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query_with_config(
        &query,
        &LoweringConfig {
            sql_time_zone: SqlTimeZone::parse("Asia/Shanghai"),
        },
    );

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let module = emit_rocq_query_module(
        lowered.list_query.as_ref().unwrap(),
        lowered.list_query.as_ref().unwrap(),
    );
    assert!(module.rocq_module.contains("CstTimestamptz (0)"));
}

#[test]
fn lowers_typed_null_temporal_literals() {
    let output = vec![
        timestamp_column("ts", Some(0)),
        typed_column("tstz", SqlType::timestamptz(None)),
    ];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Project {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: output.clone(),
            }),
            exprs: vec![
                scalar(ScalarAst::TypeAnnotation {
                    expr: Box::new(ScalarAst::Literal {
                        raw: "null".to_owned(),
                    }),
                    ty: "TIMESTAMP(0)".to_owned(),
                }),
                scalar(ScalarAst::TypeAnnotation {
                    expr: Box::new(ScalarAst::Literal {
                        raw: "null".to_owned(),
                    }),
                    ty: "TIMESTAMP_WITH_TIME_ZONE(6)".to_owned(),
                }),
            ],
            correlations: Vec::new(),
            output: output.clone(),
        },
        output,
        features: vec![Feature::TableScan, Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let lowered_query = format!("{:?}", lowered.query.as_ref().unwrap());
    assert_eq!(lowered_query.matches("raw: \"null\"").count(), 2);
    assert!(lowered_query.contains("Timestamp"));
    assert!(lowered_query.contains("Timestamptz"));
}

#[test]
fn rejects_timestamp_literals_that_exceed_declared_precision() {
    let output = vec![timestamp_column("ts", Some(3))];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Filter {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: output.clone(),
            }),
            predicate: scalar(ScalarAst::Call {
                operator: "<".to_owned(),
                op: ScalarOp::Lt,
                args: vec![
                    ScalarAst::InputRef { index: 0 },
                    ScalarAst::TypeAnnotation {
                        expr: Box::new(ScalarAst::Literal {
                            raw: "'1970-01-01 00:00:01.001001'".to_owned(),
                        }),
                        ty: "TIMESTAMP(3)".to_owned(),
                    },
                ],
            }),
            correlations: Vec::new(),
            output,
        },
        output: vec![timestamp_column("ts", Some(3))],
        features: vec![Feature::TableScan, Feature::Selection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "timestamp_precision_not_supported")
    );
}

#[test]
fn emits_source_and_target_query_rocq_module() {
    let source = FormalQuery::Table {
        relation: "EMP".to_owned(),
    };
    let target = FormalQuery::Projection {
        select: vec![FormalSelectItem {
            expr: FormalAggregateTerm::Expr {
                term: FormalFunctionTerm::Attribute {
                    name: "EMPNO".to_owned(),
                    ty: FormalAttributeType::Z,
                },
            },
            alias: "EMPNO".to_owned(),
            alias_ty: FormalAttributeType::Z,
        }],
        input: Box::new(source.clone()),
    };

    let source = bag_list_query(source);
    let target = bag_list_query(target);
    let module = emit_rocq_query_module(&source, &target);

    assert!(module.rocq_module.starts_with(
        "From SQLFS Require Import SqlSyntax GenericInstance SqlOrder SqlListAlgebra."
    ));
    assert!(
        module
            .rocq_module
            .contains("Definition source_query : Query :=")
    );
    assert!(
        module
            .rocq_module
            .contains("Definition target_query : Query :=")
    );
    assert!(module.rocq_module.contains("Table \"EMP\""));
    assert!(module.rocq_module.contains("Pi (select_list_0)"));
}

#[test]
fn timestamp_default_precision_identity_select_matches_explicit_six() {
    let query = FormalQuery::Projection {
        select: vec![FormalSelectItem {
            expr: FormalAggregateTerm::Expr {
                term: FormalFunctionTerm::Attribute {
                    name: "ts".to_owned(),
                    ty: FormalAttributeType::Timestamp { precision: None },
                },
            },
            alias: "ts".to_owned(),
            alias_ty: FormalAttributeType::Timestamp { precision: Some(6) },
        }],
        input: Box::new(FormalQuery::Table {
            relation: "events".to_owned(),
        }),
    };

    let module = emit_rocq_query_module(&bag_list_query(query.clone()), &bag_list_query(query));

    assert!(module.rocq_module.contains("TimestampColumn \"ts\" 6"));
    assert!(
        !module
            .rocq_module
            .contains("SelectAs (DotTimestamp \"ts\" 6)")
    );
}

#[test]
fn suppresses_nested_shared_queries_covered_by_larger_shared_query() {
    let select = vec![z_select_item("EMPNO")];
    let nested = FormalQuery::Projection {
        select: select.clone(),
        input: Box::new(FormalQuery::Table {
            relation: "EMP".to_owned(),
        }),
    };
    let shared = FormalQuery::Selection {
        predicate: FormalFormula::True,
        input: Box::new(FormalQuery::CrossJoin {
            left: Box::new(FormalQuery::Table {
                relation: "DEPT".to_owned(),
            }),
            right: Box::new(nested),
        }),
    };
    let source = FormalQuery::Projection {
        select: select.clone(),
        input: Box::new(shared.clone()),
    };
    let target = FormalQuery::Projection {
        select,
        input: Box::new(FormalQuery::Selection {
            predicate: FormalFormula::True,
            input: Box::new(shared),
        }),
    };

    let source = bag_list_query(source);
    let target = bag_list_query(target);
    let module = emit_rocq_query_module(&source, &target);

    assert!(module.rocq_module.contains("Definition shared_query_0"));
    assert!(!module.rocq_module.contains("Definition shared_query_1"));
    assert!(
        module
            .rocq_module
            .contains("Pi (select_list_0) (shared_query_0)")
    );
}

#[test]
fn keeps_nested_shared_query_when_it_is_used_independently() {
    let select = vec![z_select_item("EMPNO")];
    let nested = FormalQuery::Projection {
        select: select.clone(),
        input: Box::new(FormalQuery::Table {
            relation: "EMP".to_owned(),
        }),
    };
    let parent = FormalQuery::Selection {
        predicate: FormalFormula::True,
        input: Box::new(nested.clone()),
    };
    let source = FormalQuery::Set {
        op: FormalSetOp::UnionMax,
        left: Box::new(parent.clone()),
        right: Box::new(nested),
    };
    let target = parent;

    let source = bag_list_query(source);
    let target = bag_list_query(target);
    let module = emit_rocq_query_module(&source, &target);

    assert!(module.rocq_module.contains("Definition shared_query_0"));
    assert!(module.rocq_module.contains("Definition shared_query_1"));
    assert!(
        module
            .rocq_module
            .contains("SetQuery SetUnionMax (shared_query_0) (shared_query_1)")
    );
}

#[test]
fn lowers_left_join_with_exists_desugaring() {
    let left_output = vec![column("id"), column("x")];
    let right_output = vec![column("id0"), column("y")];
    let mut join_output = left_output.clone();
    join_output.extend(right_output.clone());
    let rel = RelExpr::Join {
        left: Box::new(RelExpr::TableScan {
            table: vec!["a".to_owned()],
            output: left_output,
        }),
        right: Box::new(RelExpr::TableScan {
            table: vec!["b".to_owned()],
            output: right_output,
        }),
        join_type: JoinType::Left,
        condition: scalar(ScalarAst::Call {
            operator: "=".to_owned(),
            op: ScalarOp::Eq,
            args: vec![
                ScalarAst::InputRef { index: 0 },
                ScalarAst::InputRef { index: 2 },
            ],
        }),
        correlations: Vec::new(),
        output: join_output.clone(),
    };
    let query = Query {
        source_sql: None,
        rel,
        output: join_output,
        features: vec![Feature::OuterJoin],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);
    let module = emit_rocq_query_module(
        lowered.list_query.as_ref().expect("left join should lower"),
        lowered.list_query.as_ref().expect("left join should lower"),
    );

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert!(module.rocq_module.contains("SetQuery SetUnion"));
    assert!(module.rocq_module.contains("ExistsQuery"));
    assert!(module.rocq_module.contains("NullZ"));
    assert!(!module.rocq_module.contains("LeftJoin"));
}

#[test]
fn lowers_semi_and_anti_join_with_correlated_exists() {
    let semi = existence_join_query(JoinType::Semi);
    let anti = existence_join_query(JoinType::Anti);

    let semi_lowered = lower_query(&semi);
    let anti_lowered = lower_query(&anti);
    let semi_module = emit_rocq_query_module(
        semi_lowered
            .list_query
            .as_ref()
            .expect("semi join should lower"),
        semi_lowered
            .list_query
            .as_ref()
            .expect("semi join should lower"),
    );
    let anti_module = emit_rocq_query_module(
        anti_lowered
            .list_query
            .as_ref()
            .expect("anti join should lower"),
        anti_lowered
            .list_query
            .as_ref()
            .expect("anti join should lower"),
    );

    assert_eq!(semi_lowered.status, LoweringStatus::Lowered);
    assert_eq!(anti_lowered.status, LoweringStatus::Lowered);
    assert!(semi_module.rocq_module.contains("ExistsQuery"));
    assert!(!semi_module.rocq_module.contains("Not (ExistsQuery"));
    assert!(anti_module.rocq_module.contains("Not (ExistsQuery"));
    assert!(!semi_module.rocq_module.contains("SemiJoin"));
    assert!(!anti_module.rocq_module.contains("AntiJoin"));
}

#[test]
fn emits_proof_rocq_module_with_schema_and_query_pair() {
    let module = emit_rocq_bag_bridge_proof_module();

    assert!(
        module
            .rocq_module
            .contains("From LogosGenerated Require Import Schema Queries.\n")
    );
    assert!(
        module
            .rocq_module
            .contains("Definition generated_equivalence_input :=")
    );
    assert!(
        module
            .rocq_module
            .contains("Definition generated_list_query_equiv")
    );
    assert!(
        module
            .rocq_module
            .contains("apply list_equiv_l_bag_of_bag_query_equiv.")
    );
    assert!(
        module
            .rocq_module
            .contains("Theorem generated_queries_equivalent :")
    );
    assert!(
        !module
            .rocq_module
            .contains("Definition generated_schema :=")
    );
    assert!(!module.rocq_module.contains("Definition source_query :="));
    assert!(!module.rocq_module.contains("Definition target_query :="));
}

#[test]
fn bag_bridge_proof_is_only_for_bag_queries() {
    let source = FormalQuery::Projection {
        select: vec![],
        input: Box::new(FormalQuery::Table {
            relation: "t".to_owned(),
        }),
    };
    let target = FormalQuery::Selection {
        predicate: FormalFormula::True,
        input: Box::new(FormalQuery::Table {
            relation: "t".to_owned(),
        }),
    };

    assert!(can_emit_bag_bridge_proof(
        &bag_list_query(source),
        &bag_list_query(target)
    ));
}

#[test]
fn lowers_identity_sort_to_list_bag_observation() {
    let rel = RelExpr::Sort {
        input: Box::new(RelExpr::TableScan {
            table: vec!["t".to_owned()],
            output: vec![column("a")],
        }),
        collation: vec![],
        fetch: None,
        offset: None,
        output: vec![column("a")],
    };
    let query = Query {
        source_sql: None,
        rel,
        output: vec![column("a")],
        features: vec![Feature::Sort],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert_eq!(lowered.query, None);
    assert!(matches!(
        lowered.list_query,
        Some(FormalListQuery::Bag { .. })
    ));
}

#[test]
fn lowers_sort_offset_fetch_to_list_observation() {
    let output = vec![column("a"), column("b")];
    let rel = RelExpr::Sort {
        input: Box::new(RelExpr::TableScan {
            table: vec!["t".to_owned()],
            output: output.clone(),
        }),
        collation: vec![logos_ir::ir::SortKey {
            field_index: 1,
            direction: SortDirection::Descending,
            null_direction: Some(SortNullDirection::First),
        }],
        fetch: Some(scalar(ScalarAst::Literal {
            raw: "10".to_owned(),
        })),
        offset: Some(scalar(ScalarAst::Literal {
            raw: "2".to_owned(),
        })),
        output: output.clone(),
    };
    let query = Query {
        source_sql: None,
        rel,
        output,
        features: vec![Feature::Sort, Feature::Limit, Feature::Offset],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert_eq!(lowered.query, None);
    let list_query = lowered.list_query.expect("sort should lower as list query");
    let FormalListQuery::Fetch { count, input } = list_query else {
        panic!("expected top-level Fetch");
    };
    assert_eq!(count, 10);
    let FormalListQuery::Offset { count, input } = *input else {
        panic!("expected Offset under Fetch");
    };
    assert_eq!(count, 2);
    let FormalListQuery::OrderBy { keys, input } = *input else {
        panic!("expected OrderBy under Offset");
    };
    assert_eq!(keys.len(), 1);
    assert_eq!(keys[0].attribute_name, "b");
    assert_eq!(keys[0].attribute_ty, FormalAttributeType::Z);
    assert_eq!(keys[0].direction, FormalSortDirection::Desc);
    assert_eq!(keys[0].null_direction, FormalNullDirection::First);
    assert!(matches!(*input, FormalListQuery::Bag { .. }));
}

#[test]
fn lowers_nested_fetch_zero_to_empty_bag_query() {
    let rel = RelExpr::Sort {
        input: Box::new(RelExpr::TableScan {
            table: vec!["t".to_owned()],
            output: vec![column("a")],
        }),
        collation: vec![logos_ir::ir::SortKey {
            field_index: 0,
            direction: SortDirection::Ascending,
            null_direction: Some(SortNullDirection::Last),
        }],
        fetch: Some(scalar(ScalarAst::Literal {
            raw: "0".to_owned(),
        })),
        offset: None,
        output: vec![column("a")],
    };
    let nested_rel = rel.clone();
    let query = Query {
        source_sql: None,
        rel,
        output: vec![column("a")],
        features: vec![Feature::Sort, Feature::Limit],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let Some(FormalListQuery::Fetch { count, input }) = lowered.list_query else {
        panic!("expected top-level list Fetch");
    };
    assert_eq!(count, 0);
    assert!(matches!(*input, FormalListQuery::OrderBy { .. }));

    let nested =
        LoweringContext::new(LoweringConfig::default(), None).lower_rel("rel", &nested_rel);
    assert!(matches!(
        nested,
        Some(FormalQuery::Selection {
            predicate: FormalFormula::False,
            ..
        })
    ));
}

#[test]
fn emits_native_empty_bag_relation() {
    let empty = FormalQuery::Empty {
        columns: vec![FormalAttribute {
            name: "a".to_owned(),
            ty: FormalAttributeType::Z,
        }],
    };
    let module = emit_rocq_query_module(
        &FormalListQuery::Bag {
            input: Box::new(empty.clone()),
        },
        &FormalListQuery::Bag {
            input: Box::new(empty),
        },
    );

    assert!(module.rocq_module.contains("EmptyBagRelation"));
    assert!(!module.rocq_module.contains("SetQuery SetDiff"));
}

#[test]
fn lowers_count_star_as_explicit_aggregate() {
    let input_output = vec![column("a")];
    let query = Query {
        source_sql: None,
        rel: RelExpr::Aggregate {
            input: Box::new(RelExpr::TableScan {
                table: vec!["t".to_owned()],
                output: input_output,
            }),
            group_keys: Vec::new(),
            grouping_sets: Some(vec![Vec::new()]),
            agg_calls: vec![AggregateCall {
                raw: "COUNT()".to_owned(),
                function: "COUNT".to_owned(),
                distinct: false,
                modifiers: AggregateModifiers::default(),
                args: Vec::new(),
                filter: None,
            }],
            output: vec![column("c")],
        },
        output: vec![column("c")],
        features: vec![Feature::Aggregation],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert!(
        !lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "count_star_argument_encoded")
    );
    let Some(FormalListQuery::Bag { input }) = lowered.list_query.as_ref() else {
        panic!("aggregate should lower as a bag list query");
    };
    let FormalQuery::Group { select, .. } = input.as_ref() else {
        panic!("expected Group query");
    };
    assert!(matches!(select[0].expr, FormalAggregateTerm::CountStar));

    let module = emit_rocq_query_module(
        lowered
            .list_query
            .as_ref()
            .expect("COUNT(*) should have lowered"),
        lowered
            .list_query
            .as_ref()
            .expect("COUNT(*) should have lowered"),
    );
    assert!(module.rocq_module.contains("ACountStar"));
}

#[test]
fn lowers_predicate_in_subquery_to_exists() {
    let schema = Schema {
        tables: vec![
            Table {
                name: "EMP".to_owned(),
                columns: vec![column("DEPTNO")],
            },
            Table {
                name: "DEPT".to_owned(),
                columns: vec![column("DEPTNO"), column("LOC")],
            },
        ],
    };
    let subquery_rel = RelExpr::Project {
        input: Box::new(RelExpr::Filter {
            input: Box::new(RelExpr::TableScan {
                table: vec!["DEPT".to_owned()],
                output: vec![column("DEPTNO"), column("LOC")],
            }),
            predicate: scalar(ScalarAst::Call {
                operator: "=".to_owned(),
                op: ScalarOp::Eq,
                args: vec![
                    ScalarAst::InputRef { index: 1 },
                    ScalarAst::Literal {
                        raw: "3".to_owned(),
                    },
                ],
            }),
            correlations: Vec::new(),
            output: vec![column("DEPTNO"), column("LOC")],
        }),
        exprs: vec![scalar(ScalarAst::InputRef { index: 0 })],
        correlations: Vec::new(),
        output: vec![column("DEPTNO")],
    };
    let rel = RelExpr::Filter {
        input: Box::new(RelExpr::TableScan {
            table: vec!["EMP".to_owned()],
            output: vec![column("DEPTNO")],
        }),
        predicate: scalar(ScalarAst::Call {
            operator: "IN".to_owned(),
            op: ScalarOp::In,
            args: vec![
                ScalarAst::InputRef { index: 0 },
                ScalarAst::RelSubquery {
                    rel: Box::new(subquery_rel),
                },
            ],
        }),
        correlations: Vec::new(),
        output: vec![column("DEPTNO")],
    };

    let lowered = LoweringContext::new(LoweringConfig::default(), Some(&schema))
        .lower_rel("rel", &rel)
        .expect("IN subquery should lower");
    let module = emit_rocq_query_module(&bag_list_query(lowered.clone()), &bag_list_query(lowered));

    assert!(module.rocq_module.contains("ExistsQuery"));
    assert!(module.rocq_module.contains("__logos_in_0"));
}

#[test]
fn lowers_exists_subquery_to_exists_formula() {
    let schema = Schema {
        tables: vec![
            Table {
                name: "EMP".to_owned(),
                columns: vec![column("DEPTNO")],
            },
            Table {
                name: "DEPT".to_owned(),
                columns: vec![column("DEPTNO")],
            },
        ],
    };
    let subquery_rel = RelExpr::Filter {
        input: Box::new(RelExpr::TableScan {
            table: vec!["DEPT".to_owned()],
            output: vec![column("DEPTNO")],
        }),
        predicate: scalar(ScalarAst::Call {
            operator: "=".to_owned(),
            op: ScalarOp::Eq,
            args: vec![
                ScalarAst::InputRef { index: 0 },
                ScalarAst::Literal {
                    raw: "3".to_owned(),
                },
            ],
        }),
        correlations: Vec::new(),
        output: vec![column("DEPTNO")],
    };
    let rel = RelExpr::Filter {
        input: Box::new(RelExpr::TableScan {
            table: vec!["EMP".to_owned()],
            output: vec![column("DEPTNO")],
        }),
        predicate: scalar(ScalarAst::Call {
            operator: "EXISTS".to_owned(),
            op: ScalarOp::Exists,
            args: vec![ScalarAst::RelSubquery {
                rel: Box::new(subquery_rel),
            }],
        }),
        correlations: Vec::new(),
        output: vec![column("DEPTNO")],
    };

    let lowered = LoweringContext::new(LoweringConfig::default(), Some(&schema))
        .lower_rel("rel", &rel)
        .expect("EXISTS subquery should lower");
    let module = emit_rocq_query_module(&bag_list_query(lowered.clone()), &bag_list_query(lowered));

    assert!(module.rocq_module.contains("ExistsQuery"));
    assert!(
        !module
            .rocq_module
            .contains("formula_operator_not_supported")
    );
}

#[test]
fn lowers_correlated_exists_by_binding_index_not_field_name() {
    let schema = Schema {
        tables: vec![
            Table {
                name: "DEPT".to_owned(),
                columns: vec![column("DEPTNO")],
            },
            Table {
                name: "EMP".to_owned(),
                columns: vec![column("DEPTNO")],
            },
        ],
    };
    let subquery_rel = RelExpr::Filter {
        input: Box::new(RelExpr::TableScan {
            table: vec!["EMP".to_owned()],
            output: vec![column("DEPTNO")],
        }),
        predicate: scalar(ScalarAst::Call {
            operator: "=".to_owned(),
            op: ScalarOp::Eq,
            args: vec![
                ScalarAst::CorrelatedRef {
                    correlation: "$cor0".to_owned(),
                    field: "DEPTNO".to_owned(),
                    index: Some(0),
                    ty: SqlType::Integer,
                },
                ScalarAst::InputRef { index: 0 },
            ],
        }),
        correlations: Vec::new(),
        output: vec![column("DEPTNO")],
    };
    let rel = RelExpr::Filter {
        input: Box::new(RelExpr::TableScan {
            table: vec!["DEPT".to_owned()],
            output: vec![column("DEPTNO")],
        }),
        predicate: scalar(ScalarAst::Call {
            operator: "EXISTS".to_owned(),
            op: ScalarOp::Exists,
            args: vec![ScalarAst::RelSubquery {
                rel: Box::new(subquery_rel),
            }],
        }),
        correlations: vec![CorrelationBinding {
            correlation: "$cor0".to_owned(),
            output: vec![column("DEPTNO")],
        }],
        output: vec![column("DEPTNO")],
    };

    let lowered = LoweringContext::new(LoweringConfig::default(), Some(&schema))
        .lower_rel("rel", &rel)
        .expect("correlated EXISTS should lower");
    let module = emit_rocq_query_module(&bag_list_query(lowered.clone()), &bag_list_query(lowered));

    assert!(module.rocq_module.contains("__logos_cor_cor0_0"));
    assert!(
        module
            .rocq_module
            .contains("Pred \"=\" ([DotZ \"__logos_cor_cor0_0\"; DotZ \"DEPTNO\"])")
    );
    assert!(
        !module
            .rocq_module
            .contains("Pred \"=\" ([DotZ \"DEPTNO\"; DotZ \"DEPTNO\"])")
    );
}

#[test]
fn lowers_correlated_join_output_after_calcite_renaming() {
    let schema = Schema {
        tables: vec![
            Table {
                name: "a".to_owned(),
                columns: vec![column("id"), column("x")],
            },
            Table {
                name: "b".to_owned(),
                columns: vec![column("id"), column("y")],
            },
            Table {
                name: "c".to_owned(),
                columns: vec![column("id")],
            },
        ],
    };
    let join_output = vec![column("id"), column("x"), column("id0"), column("y")];
    let join_rel = RelExpr::Join {
        left: Box::new(RelExpr::TableScan {
            table: vec!["a".to_owned()],
            output: vec![column("id"), column("x")],
        }),
        right: Box::new(RelExpr::TableScan {
            table: vec!["b".to_owned()],
            output: vec![column("id"), column("y")],
        }),
        join_type: JoinType::Inner,
        condition: scalar(ScalarAst::Call {
            operator: "=".to_owned(),
            op: ScalarOp::Eq,
            args: vec![
                ScalarAst::InputRef { index: 0 },
                ScalarAst::InputRef { index: 2 },
            ],
        }),
        correlations: Vec::new(),
        output: join_output.clone(),
    };
    let subquery_rel = RelExpr::Filter {
        input: Box::new(RelExpr::TableScan {
            table: vec!["c".to_owned()],
            output: vec![column("id")],
        }),
        predicate: scalar(ScalarAst::Call {
            operator: "=".to_owned(),
            op: ScalarOp::Eq,
            args: vec![
                ScalarAst::InputRef { index: 0 },
                ScalarAst::CorrelatedRef {
                    correlation: "$cor0".to_owned(),
                    field: "id0".to_owned(),
                    index: Some(2),
                    ty: SqlType::Integer,
                },
            ],
        }),
        correlations: Vec::new(),
        output: vec![column("id")],
    };
    let rel = RelExpr::Filter {
        input: Box::new(join_rel),
        predicate: scalar(ScalarAst::Call {
            operator: "EXISTS".to_owned(),
            op: ScalarOp::Exists,
            args: vec![ScalarAst::RelSubquery {
                rel: Box::new(subquery_rel),
            }],
        }),
        correlations: vec![CorrelationBinding {
            correlation: "$cor0".to_owned(),
            output: join_output,
        }],
        output: vec![column("id"), column("x"), column("id0"), column("y")],
    };

    let lowered = LoweringContext::new(LoweringConfig::default(), Some(&schema))
        .lower_rel("rel", &rel)
        .expect("correlated join output should lower");
    let module = emit_rocq_query_module(&bag_list_query(lowered.clone()), &bag_list_query(lowered));

    assert!(module.rocq_module.contains("__logos_cor_cor0_2"));
    assert!(
        module
            .rocq_module
            .contains("Pred \"=\" ([DotZ \"id\"; DotZ \"__logos_cor_cor0_2\"])")
    );
    assert!(
        !module
            .rocq_module
            .contains("ExistsQuery (Sigma (Pred \"=\" ([DotZ \"id\"; DotZ \"id0\"])")
    );
}

#[test]
fn lowers_empty_values_rows_to_typed_empty_bag() {
    let rel = RelExpr::Values {
        tuples: ValuesTuples::Rows { rows: vec![] },
        output: vec![column("a")],
    };
    let query = Query {
        source_sql: None,
        rel,
        output: vec![column("a")],
        features: vec![Feature::Values],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);
    let module = emit_rocq_query_module(
        lowered
            .list_query
            .as_ref()
            .expect("empty VALUES should lower"),
        lowered
            .list_query
            .as_ref()
            .expect("empty VALUES should lower"),
    );

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert!(matches!(lowered.query, Some(FormalQuery::Empty { .. })));
    assert!(module.rocq_module.contains("EmptyRelation"));
    assert!(!module.rocq_module.contains("SetQuery SetDiff"));
}

#[test]
fn lowers_values_rows_with_additive_bag_union() {
    let rel = RelExpr::Values {
        tuples: ValuesTuples::Rows {
            rows: vec![
                vec![scalar(ScalarAst::Literal {
                    raw: "1".to_owned(),
                })],
                vec![scalar(ScalarAst::Literal {
                    raw: "1".to_owned(),
                })],
            ],
        },
        output: vec![column("A")],
    };
    let query = Query {
        source_sql: None,
        rel,
        output: vec![column("A")],
        features: vec![Feature::Values],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);
    let module = emit_rocq_query_module(
        lowered
            .list_query
            .as_ref()
            .expect("VALUES rows should lower"),
        lowered
            .list_query
            .as_ref()
            .expect("VALUES rows should lower"),
    );

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert!(module.rocq_module.contains("SetQuery SetUnion"));
    assert!(!module.rocq_module.contains("SetQuery SetUnionMax"));
}

#[test]
fn lowers_values_null_using_inferred_column_type() {
    let rel = RelExpr::Values {
        tuples: ValuesTuples::Rows {
            rows: vec![
                vec![scalar(ScalarAst::Literal {
                    raw: "NULL".to_owned(),
                })],
                vec![scalar(ScalarAst::TypeAnnotation {
                    expr: Box::new(ScalarAst::Literal {
                        raw: "1".to_owned(),
                    }),
                    ty: "INTEGER".to_owned(),
                })],
            ],
        },
        output: vec![typed_column("A", SqlType::Null)],
    };
    let query = Query {
        source_sql: None,
        rel,
        output: vec![typed_column("A", SqlType::Null)],
        features: vec![Feature::Values],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let Some(FormalQuery::Set { op, left, right }) = lowered.query else {
        panic!("two VALUES rows should lower to a bag union");
    };
    assert_eq!(op, FormalSetOp::Union);
    let (Some(null_ty), Some(one_ty)) = (
        singleton_constant_type(&left, "NULL"),
        singleton_constant_type(&right, "1"),
    ) else {
        panic!("VALUES rows should lower to typed singleton constants");
    };
    assert_eq!(null_ty, FormalAttributeType::Z);
    assert_eq!(one_ty, FormalAttributeType::Z);
}

#[test]
fn lowers_values_null_using_concrete_output_type() {
    let rel = RelExpr::Values {
        tuples: ValuesTuples::Rows {
            rows: vec![vec![scalar(ScalarAst::Literal {
                raw: "NULL".to_owned(),
            })]],
        },
        output: vec![column("A")],
    };
    let query = Query {
        source_sql: None,
        rel,
        output: vec![column("A")],
        features: vec![Feature::Values],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let Some(ty) = lowered
        .query
        .as_ref()
        .and_then(|query| singleton_constant_type(query, "NULL"))
    else {
        panic!("concrete VALUES output type should type bare NULL");
    };
    assert_eq!(ty, FormalAttributeType::Z);
}

#[test]
fn defaults_untyped_all_null_values_column_to_integer() {
    let rel = RelExpr::Values {
        tuples: ValuesTuples::Rows {
            rows: vec![vec![scalar(ScalarAst::Literal {
                raw: "NULL".to_owned(),
            })]],
        },
        output: vec![typed_column("A", SqlType::Null)],
    };
    let query = Query {
        source_sql: None,
        rel,
        output: vec![typed_column("A", SqlType::Null)],
        features: vec![Feature::Values],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let Some(ty) = lowered
        .query
        .as_ref()
        .and_then(|query| singleton_constant_type(query, "NULL"))
    else {
        panic!("fallback VALUES output type should type bare NULL");
    };
    assert_eq!(ty, FormalAttributeType::Z);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "values_null_type_defaulted_to_integer")
    );
}

#[test]
fn lowers_untyped_null_values_filter_without_static_empty_rewrite() {
    let output = vec![
        typed_column("A", SqlType::Null),
        typed_column("B", SqlType::Null),
    ];
    let values = RelExpr::Values {
        tuples: ValuesTuples::Rows {
            rows: vec![vec![
                scalar(ScalarAst::Literal {
                    raw: "NULL".to_owned(),
                }),
                scalar(ScalarAst::Literal {
                    raw: "NULL".to_owned(),
                }),
            ]],
        },
        output: output.clone(),
    };
    let rel = RelExpr::Filter {
        input: Box::new(values),
        predicate: scalar(ScalarAst::Call {
            operator: "=".to_owned(),
            op: ScalarOp::Eq,
            args: vec![
                ScalarAst::Literal {
                    raw: "1".to_owned(),
                },
                ScalarAst::Literal {
                    raw: "0".to_owned(),
                },
            ],
        }),
        correlations: Vec::new(),
        output: output.clone(),
    };
    let query = Query {
        source_sql: None,
        rel,
        output,
        features: vec![Feature::Values, Feature::Selection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);
    let module = emit_rocq_query_module(
        lowered
            .list_query
            .as_ref()
            .expect("filtered VALUES should lower"),
        lowered
            .list_query
            .as_ref()
            .expect("filtered VALUES should lower"),
    );

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert!(matches!(lowered.query, Some(FormalQuery::Selection { .. })));
    assert!(module.rocq_module.contains("Sigma"));
    assert!(module.rocq_module.contains("NullZ"));
    assert!(module.rocq_module.contains("AttrZ \"A\""));
    assert!(!module.rocq_module.contains("EmptyRelation"));
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "values_null_type_defaulted_to_integer")
    );
}

#[test]
fn rejects_conflicting_inferred_values_column_types() {
    let rel = RelExpr::Values {
        tuples: ValuesTuples::Rows {
            rows: vec![
                vec![scalar(ScalarAst::TypeAnnotation {
                    expr: Box::new(ScalarAst::Literal {
                        raw: "1".to_owned(),
                    }),
                    ty: "INTEGER".to_owned(),
                })],
                vec![scalar(ScalarAst::TypeAnnotation {
                    expr: Box::new(ScalarAst::Literal {
                        raw: "'x'".to_owned(),
                    }),
                    ty: "VARCHAR".to_owned(),
                })],
            ],
        },
        output: vec![typed_column("A", SqlType::Any)],
    };
    let query = Query {
        source_sql: None,
        rel,
        output: vec![typed_column("A", SqlType::Any)],
        features: vec![Feature::Values],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "values_column_type_conflict")
    );
}

#[test]
fn rejects_values_cell_type_mismatch_against_concrete_output() {
    let rel = RelExpr::Values {
        tuples: ValuesTuples::Rows {
            rows: vec![vec![scalar(ScalarAst::TypeAnnotation {
                expr: Box::new(ScalarAst::Literal {
                    raw: "'x'".to_owned(),
                }),
                ty: "VARCHAR".to_owned(),
            })]],
        },
        output: vec![column("A")],
    };
    let query = Query {
        source_sql: None,
        rel,
        output: vec![column("A")],
        features: vec![Feature::Values],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "values_literal_type_mismatch")
    );
}

#[test]
fn rejects_values_duplicate_output_aliases() {
    let rel = RelExpr::Values {
        tuples: ValuesTuples::Rows {
            rows: vec![vec![
                scalar(ScalarAst::Literal {
                    raw: "1".to_owned(),
                }),
                scalar(ScalarAst::Literal {
                    raw: "2".to_owned(),
                }),
            ]],
        },
        output: vec![column("A"), column("A")],
    };
    let query = Query {
        source_sql: None,
        rel,
        output: vec![column("A"), column("A")],
        features: vec![Feature::Values],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "duplicate_values_alias")
    );
}

#[test]
fn lowers_values_fetch_through_bag_observation() {
    let values = RelExpr::Values {
        tuples: ValuesTuples::Rows {
            rows: vec![
                vec![scalar(ScalarAst::Literal {
                    raw: "1".to_owned(),
                })],
                vec![scalar(ScalarAst::Literal {
                    raw: "2".to_owned(),
                })],
            ],
        },
        output: vec![column("a")],
    };
    let rel = RelExpr::Sort {
        input: Box::new(values),
        collation: Vec::new(),
        fetch: Some(scalar(ScalarAst::Literal {
            raw: "1".to_owned(),
        })),
        offset: None,
        output: vec![column("a")],
    };
    let query = Query {
        source_sql: None,
        rel,
        output: vec![column("a")],
        features: vec![Feature::Values],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let Some(FormalListQuery::Fetch { input, .. }) = lowered.list_query else {
        panic!("VALUES with FETCH should lower to a list fetch observation");
    };
    let FormalListQuery::Bag { input } = *input else {
        panic!("FETCH input should observe VALUES through bag semantics");
    };
    assert!(matches!(*input, FormalQuery::Set { .. }));
}

#[test]
fn rejects_duplicate_projection_aliases() {
    let table_output = vec![column("a"), column("b")];
    let rel = RelExpr::Project {
        input: Box::new(RelExpr::TableScan {
            table: vec!["t".to_owned()],
            output: table_output,
        }),
        exprs: vec![
            scalar(ScalarAst::InputRef { index: 0 }),
            scalar(ScalarAst::InputRef { index: 1 }),
        ],
        correlations: Vec::new(),
        output: vec![column("x"), column("x")],
    };
    let query = Query {
        source_sql: None,
        rel,
        output: vec![column("x"), column("x")],
        features: vec![Feature::Projection],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "duplicate_projection_alias")
    );
}

#[test]
fn lowers_union_distinct_as_duplicate_elimination() {
    let input = || RelExpr::TableScan {
        table: vec!["t".to_owned()],
        output: vec![column("a")],
    };
    let rel = RelExpr::Set {
        op: SetOp::Union,
        all: false,
        inputs: vec![input(), input()],
        output: vec![column("a")],
    };
    let query = Query {
        source_sql: None,
        rel,
        output: vec![column("a")],
        features: vec![Feature::Union, Feature::SetDistinct],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let Some(FormalQuery::Group {
        group_by, input, ..
    }) = lowered.query
    else {
        panic!("UNION DISTINCT should lower to duplicate elimination over bag union");
    };
    assert_eq!(group_by.len(), 1);
    assert!(matches!(
        *input,
        FormalQuery::Set {
            op: FormalSetOp::Union,
            ..
        }
    ));
}

#[test]
fn lowers_except_distinct_by_deduplicating_each_input() {
    let input = || RelExpr::TableScan {
        table: vec!["t".to_owned()],
        output: vec![column("a")],
    };
    let rel = RelExpr::Set {
        op: SetOp::Except,
        all: false,
        inputs: vec![input(), input()],
        output: vec![column("a")],
    };
    let query = Query {
        source_sql: None,
        rel,
        output: vec![column("a")],
        features: vec![Feature::Except, Feature::SetDistinct],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    };

    let lowered = lower_query(&query);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    let Some(FormalQuery::Set {
        op: FormalSetOp::Diff,
        left,
        right,
    }) = lowered.query
    else {
        panic!("EXCEPT DISTINCT should lower to bag difference over deduplicated inputs");
    };
    assert!(matches!(*left, FormalQuery::Group { .. }));
    assert!(matches!(*right, FormalQuery::Group { .. }));
}

fn column(name: &str) -> Column {
    typed_column(name, SqlType::Integer)
}

fn typed_column(name: &str, ty: SqlType) -> Column {
    Column {
        name: name.to_owned(),
        ty,
        nullable: true,
    }
}

fn singleton_constant_type(query: &FormalQuery, raw: &str) -> Option<FormalAttributeType> {
    let FormalQuery::Projection { select, input } = query else {
        return None;
    };
    if !matches!(**input, FormalQuery::EmptyTuple) {
        return None;
    }
    let [item] = select.as_slice() else {
        return None;
    };
    let FormalAggregateTerm::Expr {
        term:
            FormalFunctionTerm::Constant {
                raw: constant_raw,
                ty: Some(ty),
            },
    } = &item.expr
    else {
        return None;
    };
    constant_raw.eq_ignore_ascii_case(raw).then_some(*ty)
}

fn decimal_column(name: &str, precision: u32, scale: u32) -> Column {
    Column {
        name: name.to_owned(),
        ty: SqlType::decimal(Some(precision), Some(scale)),
        nullable: true,
    }
}

fn decimal_column_unconstrained(name: &str) -> Column {
    Column {
        name: name.to_owned(),
        ty: SqlType::decimal(None, None),
        nullable: true,
    }
}

fn timestamp_column(name: &str, precision: Option<u32>) -> Column {
    Column {
        name: name.to_owned(),
        ty: SqlType::timestamp(precision),
        nullable: true,
    }
}

fn bag_list_query(query: FormalQuery) -> FormalListQuery {
    FormalListQuery::Bag {
        input: Box::new(query),
    }
}

fn scalar(parsed: ScalarAst) -> ScalarExpr {
    ScalarExpr {
        raw: String::new(),
        class: ScalarClass::Call,
        parsed,
    }
}

fn z_select_item(name: &str) -> FormalSelectItem {
    FormalSelectItem {
        expr: FormalAggregateTerm::Expr {
            term: FormalFunctionTerm::Attribute {
                name: name.to_owned(),
                ty: FormalAttributeType::Z,
            },
        },
        alias: name.to_owned(),
        alias_ty: FormalAttributeType::Z,
    }
}

fn existence_join_query(join_type: JoinType) -> Query {
    let left_output = vec![column("id"), column("x")];
    let right_output = vec![column("id0"), column("y")];
    let rel = RelExpr::Join {
        left: Box::new(RelExpr::TableScan {
            table: vec!["a".to_owned()],
            output: left_output.clone(),
        }),
        right: Box::new(RelExpr::TableScan {
            table: vec!["b".to_owned()],
            output: right_output,
        }),
        join_type,
        condition: scalar(ScalarAst::Call {
            operator: "=".to_owned(),
            op: ScalarOp::Eq,
            args: vec![
                ScalarAst::InputRef { index: 0 },
                ScalarAst::InputRef { index: 2 },
            ],
        }),
        correlations: Vec::new(),
        output: left_output.clone(),
    };
    Query {
        source_sql: None,
        rel,
        output: left_output,
        features: vec![match join_type {
            JoinType::Semi => Feature::SemiJoin,
            JoinType::Anti => Feature::AntiJoin,
            _ => unreachable!("test helper only builds semi/anti joins"),
        }],
        calcite_rel_text: None,
        calcite_rel_plan: None,
    }
}
