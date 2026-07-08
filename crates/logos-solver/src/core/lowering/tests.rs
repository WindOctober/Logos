use super::*;
use logos_ir::ir::ScalarOp;

use logos_ir::ir::{
    Column, Feature, JoinType, Query, RelExpr, ScalarAst, ScalarClass, ScalarExpr, Schema, SetOp,
    SortDirection, SortNullDirection, SqlType, Table, ValuesTuples,
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
            output: table_output.clone(),
        }),
        exprs: vec![scalar(ScalarAst::InputRef { index: 1 })],
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
fn lowers_schema_to_formal_sql_create_table_shape() {
    let schema = Schema {
        tables: vec![Table {
            name: "EMP".to_owned(),
            columns: vec![
                typed_column("EMPNO", SqlType::Integer),
                typed_column("ENAME", SqlType::Varchar),
                typed_column("SLACKER", SqlType::Boolean),
                typed_column("HIREDATE", SqlType::Date),
                timestamp_column("EVENT_TS", Some(6)),
            ],
        }],
    };

    let lowered = lower_schema(&schema);

    assert_eq!(lowered.status, LoweringStatus::Lowered);
    assert_eq!(
        lowered.schema.as_ref().unwrap().tables[0].attributes.len(),
        5
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
                .contains("Attr_Z \"EMPNO\" :: Attr_string \"ENAME\" :: Attr_bool \"SLACKER\" :: Attr_date \"HIREDATE\" :: Attr_timestamp \"EVENT_TS\" 6 :: nil")
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
        "schema-only lowering should not warn for supported DATE/TIMESTAMP columns"
    );
}

#[test]
fn lowers_timestamp_literals_and_interval_arithmetic() {
    let output = vec![typed_column("ts", SqlType::Timestamp)];
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
                output: output.clone(),
            }),
            exprs: vec![scalar(ScalarAst::InputRef { index: 0 })],
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
    let output = vec![typed_column("ts", SqlType::TimestampTz)];
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
    let output = vec![typed_column("ts", SqlType::TimestampTz)];
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
    let output = vec![typed_column("ts", SqlType::TimestampTz)];
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
        typed_column("tstz", SqlType::TimestampTz),
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
                    constructor: "Attr_Z".to_owned(),
                },
            },
            alias: "EMPNO".to_owned(),
            alias_constructor: "Attr_Z".to_owned(),
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
    assert!(module.rocq_module.contains("SetQuery SetUnionMax"));
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
    assert_eq!(keys[0].attribute_constructor, "Attr_Z");
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

    let nested = LoweringContext::new(LoweringConfig::default()).lower_rel("rel", &nested_rel);
    assert!(matches!(
        nested,
        Some(FormalQuery::Selection {
            predicate: FormalFormula::False,
            ..
        })
    ));
}

#[test]
fn does_not_lower_values_rows() {
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

    assert_eq!(lowered.status, LoweringStatus::Blocked);
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
fn rejects_distinct_set_semantics() {
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

    assert_eq!(lowered.status, LoweringStatus::Blocked);
    assert!(
        lowered
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "set_distinct_semantics_not_supported")
    );
}

fn column(name: &str) -> Column {
    typed_column(name, SqlType::Integer)
}

fn typed_column(name: &str, ty: SqlType) -> Column {
    Column {
        name: name.to_owned(),
        ty,
        nullable: true,
        precision: None,
    }
}

fn timestamp_column(name: &str, precision: Option<u32>) -> Column {
    Column {
        name: name.to_owned(),
        ty: SqlType::Timestamp,
        nullable: true,
        precision,
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
                constructor: "Attr_Z".to_owned(),
            },
        },
        alias: name.to_owned(),
        alias_constructor: "Attr_Z".to_owned(),
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
